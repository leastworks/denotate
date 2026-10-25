//! File-based slice-6 re-scoring. See ../SCORECARD.md for timing boundaries.
use denotate_check::{BackendIdentity, Limits, ScopedResult};
use denotate_check_session::{Retention, Session};
use denotate_editor::Document;
use denotate_test_dsl::{analysis, lowering, syntax};
use serde_json::{Value, json};
use std::{
    path::PathBuf,
    sync::Arc,
    time::{Duration, Instant},
};

const USAGE: &str = "scorecard PROGRAM [--edit FILE] [--samples N] [--json FILE] [--unconstrained] [--timeout-ms N]";
const MODES: [&str; 9] = [
    "global-bdd",
    "fresh-local-bdd",
    "fresh-sat",
    "cached-bdd",
    "cached-sat",
    "grounding-bdd",
    "grounding-sat",
    "bdd-no-plans",
    "fresh-grounding-bdd",
];
const PHASES: [&str; 3] = ["cold", "warm", "edit"];

struct Config {
    file: PathBuf,
    edit: Option<PathBuf>,
    json: Option<PathBuf>,
    samples: usize,
    unconstrained: bool,
    timeout_ms: u64,
}
impl Config {
    fn parse(args: impl IntoIterator<Item = String>) -> Result<Self, String> {
        let mut args = args.into_iter();
        let mut c = Self {
            file: args.next().ok_or(USAGE)?.into(),
            edit: None,
            json: None,
            samples: 5,
            unconstrained: false,
            timeout_ms: 60_000,
        };
        while let Some(arg) = args.next() {
            if arg == "--unconstrained" {
                c.unconstrained = true;
                continue;
            }
            let value = args
                .next()
                .ok_or_else(|| format!("Missing value for {arg}"))?;
            match arg.as_str() {
                "--edit" => c.edit = Some(value.into()),
                "--json" => c.json = Some(value.into()),
                "--samples" => c.samples = value.parse().map_err(|_| "Invalid sample count")?,
                "--timeout-ms" => c.timeout_ms = value.parse().map_err(|_| "Invalid timeout")?,
                _ => return Err(format!("Unknown option {arg}\n{USAGE}")),
            }
        }
        if c.samples == 0 || c.timeout_ms == 0 {
            return Err("Samples and timeout must be positive".into());
        }
        if let Some(output) = &c.json {
            if let Ok(output) = output.canonicalize() {
                for input in std::iter::once(&c.file).chain(c.edit.iter()) {
                    if input.canonicalize().ok().as_ref() == Some(&output) {
                        return Err("JSON output must not overwrite either input program".into());
                    }
                }
            }
        }
        Ok(c)
    }
}

fn default_edit(source: &str) -> String {
    for n in 0.. {
        let input = format!("closeout_probe_{n}");
        let slot = format!("closeout_slot_{n}");
        if !source.contains(&input) && !source.contains(&slot) {
            return format!("{source}\ninput {input}; slot {slot}; {slot} <- {input};\n");
        }
    }
    unreachable!()
}

fn session(mode: &str, unconstrained: bool) -> Option<Session> {
    let s = match mode {
        "global-bdd" | "fresh-sat" => return None,
        "fresh-local-bdd" => {
            return Some(Session::new(Retention {
                max_entries: 0,
                max_bytes: 0,
                max_condition_nodes: 0,
            }));
        }
        "grounding-bdd" | "grounding-sat" => Session::with_grounding(),
        "fresh-grounding-bdd" => Session::with_fresh_grounding(),
        "bdd-no-plans" => Session::with_fresh_planning(),
        _ => Session::default(),
    };
    Some(if unconstrained {
        s.without_retention_limits()
    } else {
        s
    })
}

fn prepare(
    text: &str,
    revision: usize,
    lower: &mut lowering::incremental::Session,
) -> Result<(analysis::Program, Value), String> {
    let mut parser = syntax::parser().map_err(|e| e.to_string())?;
    let start = Instant::now();
    let doc = Arc::new(Document::new(
        &mut parser,
        text.into(),
        revision as i32 + 1,
        true,
    ));
    let parse_ns = start.elapsed().as_nanos();
    let start = Instant::now();
    let prepared = analysis::prepare(
        &"file:///closeout.inputmapping".parse().unwrap(),
        revision as u64 + 1,
        doc,
        lower,
    )?;
    let frontend_ns = start.elapsed().as_nanos();
    let program = prepared.program.ok_or_else(|| {
        prepared
            .fast
            .iter()
            .map(|d| d.message.as_str())
            .collect::<Vec<_>>()
            .join("; ")
    })?;
    let stats = lower.stats();
    let t = stats.last;
    let measured = t.projection_ns as u128
        + t.queries_ns as u128
        + t.assembly_attribution_ns as u128
        + t.key_computation_ns as u128;
    Ok((
        program,
        json!({"parse_ns": parse_ns, "frontend_ns": frontend_ns, "frontend": stats,
        "frontend_other_ns": frontend_ns.saturating_sub(measured)}),
    ))
}

fn counts(output: &analysis::Output) -> Value {
    let r = &output.results.value;
    let mut counts = [0usize; 4];
    // Explicit group results only; implicit trivial groups are described separately.
    for result in r.groups.values() {
        counts[match result {
            ScopedResult::Proved => 0,
            ScopedResult::Counterexample(..) => 1,
            ScopedResult::Unsupported(..) => 2,
            ScopedResult::Inconclusive(..) => 3,
        }] += 1;
    }
    json!({"proved": counts[0], "counterexample": counts[1], "unsupported": counts[2], "inconclusive": counts[3],
        "unfinished": format!("{:?}", r.unfinished), "incomplete_regions": r.incomplete.len(),
        "groups": format!("{:?}", r.groups), "group_domains": format!("{:?}", r.group_domains),
        "regions": format!("{:?}", r.regions), "diagnostics": output.diagnostics, "creator_warnings": output.creator_warnings})
}

fn contradiction(a: &analysis::Output, b: &analysis::Output) -> bool {
    let a = &a.results.value;
    let b = &b.results.value;
    a.groups.keys().chain(b.groups.keys()).any(|key| {
        matches!(
            (a.group(key), b.group(key)),
            (
                Some(ScopedResult::Proved),
                Some(ScopedResult::Counterexample(..))
            ) | (
                Some(ScopedResult::Counterexample(..)),
                Some(ScopedResult::Proved)
            )
        )
    })
}

fn collect(c: &Config, source: &str, edited: &str) -> Result<Value, String> {
    // Reject syntax/name errors once, before starting the paired measurement.
    for (label, text) in [("program", source), ("edit", edited)] {
        prepare(text, 0, &mut lowering::incremental::Session::default())
            .map_err(|e| format!("Invalid {label}: {e}"))?;
    }
    let warm = format!("// scorecard warm\n{source}");
    let texts = [source, warm.as_str(), edited];
    let limits = Limits {
        timeout: Duration::from_millis(c.timeout_ms),
        ..Limits::default()
    };
    let mut samples = Vec::new();
    let mut failures = Vec::new();
    for iteration in 0..=c.samples {
        eprintln!(
            "scorecard: {} {}/{}",
            if iteration == 0 { "warm-up" } else { "sample" },
            iteration,
            c.samples
        );
        let mut modes = MODES.to_vec();
        // Keep the global control first; alternate the other paths to reduce order bias.
        if iteration % 2 != 0 {
            modes[1..].reverse();
        }
        let mut global: Vec<Result<analysis::Output, analysis::Failure>> = Vec::new();
        let mut rows = serde_json::Map::new();
        for mode in modes {
            let mut cache = session(mode, c.unconstrained);
            let mut lower = lowering::incremental::Session::new(true);
            let mut previous = None;
            let mut phases = serde_json::Map::new();
            for (phase_index, phase) in PHASES.into_iter().enumerate() {
                let (program, mut row) = prepare(texts[phase_index], phase_index, &mut lower)?;
                let backend = if mode.ends_with("sat") {
                    BackendIdentity::sat()
                } else {
                    BackendIdentity::bdd()
                };
                let start = Instant::now();
                let mut preparation_ns = None;
                let output = program.check_with_backend(
                    &limits,
                    || preparation_ns = Some(start.elapsed().as_nanos()),
                    backend,
                    cache.as_mut(),
                );
                let checking_ns = start.elapsed().as_nanos();
                row["checking_ns"] = json!(checking_ns);
                row["preparation_ns"] = json!(preparation_ns);
                row["after_preparation_ns"] =
                    json!(preparation_ns.map(|n| checking_ns.saturating_sub(n)));
                row["total_ns"] = json!(
                    row["parse_ns"].as_u64().unwrap() as u128
                        + row["frontend_ns"].as_u64().unwrap() as u128
                        + checking_ns
                );
                match &output {
                    Err(error) => {
                        let error = format!("{error:?}");
                        failures.push(format!("sample {iteration}, {mode}/{phase}: {error}"));
                        row["error"] = json!(error);
                    }
                    Ok(output) => {
                        row["results"] = counts(output);
                        row["logical_work"] = json!(
                            output
                                .results
                                .receipts
                                .total()
                                .map_err(|e| format!("{e:?}"))?
                                .work
                        );
                        if phase == "warm" {
                            let equal = previous.as_ref().map(|p| p == &output.results);
                            row["warm_equals_cold"] = json!(equal);
                            if equal == Some(false) {
                                failures.push(format!("sample {iteration}, {mode}: warm results/receipts differ from cold"));
                            }
                        }
                        previous = Some(output.results.clone());
                        if mode != "global-bdd" {
                            if let Some(Ok(reference)) = global.get(phase_index) {
                                let mut neutral = output.results.value.clone();
                                neutral.context.backend = BackendIdentity::bdd();
                                row["matches_global_results"] =
                                    json!(neutral == reference.results.value);
                                row["matches_global_diagnostics"] =
                                    json!(output.diagnostics == reference.diagnostics);
                                let conflict = contradiction(output, reference);
                                row["contradicts_global"] = json!(conflict);
                                if conflict {
                                    failures.push(format!("sample {iteration}, {mode}/{phase}: conclusive contradiction with global BDD"));
                                }
                            }
                        }
                        // Output stats exist only for phases actually reached. A
                        // preparation exhaustion must not report the previous check.
                        if let Some(stats) = output.cache {
                            row["cache"] = json!({"evaluation_hits": stats.evaluation_hits, "evaluation_misses": stats.evaluation_misses,
                                "answer_hits": stats.verdict_hits, "answer_misses": stats.verdict_misses, "retained_bytes": stats.retained_bytes,
                                "bypassed": stats.bypassed, "evicted": stats.evicted});
                        }
                        if let Some(plans) = output.plans {
                            row["plans"] = json!({"executed": plans.executed, "reused": plans.reused, "retained_bytes": plans.retained_bytes});
                        }
                        if let Some(s) = cache.as_ref().filter(|_| preparation_ns.is_some()) {
                            let grounding = s.grounding_stats();
                            row["grounding"] = json!({"executed": grounding.executed, "reused": grounding.reused, "retained_bytes": grounding.retained_bytes});
                        }
                        if let Some(metrics) = &output.local_metrics {
                            row["scc_work"] = json!(metrics.scc_work.iter().map(|(key, work)| json!({
                                "key": format!("{key:?}"), "cone_evaluations": work.cone_evaluations,
                                "elapsed_ns": work.elapsed.as_nanos()
                            })).collect::<Vec<_>>());
                        }
                    }
                }
                if mode == "global-bdd" {
                    global.push(output);
                }
                phases.insert(phase.into(), row);
            }
            rows.insert(mode.into(), Value::Object(phases));
        }
        if iteration > 0 {
            samples.push(Value::Object(rows));
        }
    }
    Ok(
        json!({"schema": 1, "provisional": true, "program": c.file, "edit_file": c.edit,
        "edit_kind": if c.edit.is_some() { "supplied program" } else { "appended unrelated mapping" },
        "source": source, "edited_source": edited, "warmups": 1, "samples_per_point": c.samples,
        "unconstrained_retention": c.unconstrained, "timeout_ms": c.timeout_ms,
        "failures": failures, "samples": samples}),
    )
}

fn median(rows: &[&Value], field: &str) -> String {
    let mut ns = rows
        .iter()
        .filter_map(|r| r.pointer(field).and_then(Value::as_u64))
        .collect::<Vec<_>>();
    ns.sort_unstable();
    if ns.len() != rows.len() {
        return "-".into();
    }
    format!("{:.3}", ns[ns.len() / 2] as f64 / 1e6)
}

fn print_scorecard(data: &Value) {
    println!(
        "Slice 6: provisional, re-score on real programs\nEdit: {}. Retention: {}. {} samples after one warm-up.",
        data["edit_kind"].as_str().unwrap(),
        if data["unconstrained_retention"] == true {
            "unconstrained"
        } else {
            "default"
        },
        data["samples_per_point"]
    );
    println!(
        "Medians in ms; total = parse + frontend + checking. P/C/U/I count explicit groups only.\n"
    );
    println!(
        "{:<22} {:<5} {:>10} {:>10} {:>10} {:>10}  outcomes; comparisons",
        "path", "phase", "total", "checking", "prepare", "remaining"
    );
    let samples = data["samples"].as_array().unwrap();
    for mode in MODES {
        for phase in PHASES {
            let rows = samples.iter().map(|s| &s[mode][phase]).collect::<Vec<_>>();
            let mut outcomes = rows
                .iter()
                .map(|r| {
                    if let Some(error) = r["error"].as_str() {
                        return format!("ERROR {error}");
                    }
                    let o = &r["results"];
                    format!(
                        "{}/{}/{}/{} unfinished={} incomplete={}",
                        o["proved"],
                        o["counterexample"],
                        o["unsupported"],
                        o["inconclusive"],
                        o["unfinished"].as_str().unwrap(),
                        o["incomplete_regions"]
                    )
                })
                .collect::<Vec<_>>();
            outcomes.sort();
            outcomes.dedup();
            let differences = rows
                .iter()
                .filter(|r| r["matches_global_results"] == false)
                .count();
            let diagnostic_differences = rows
                .iter()
                .filter(|r| r["matches_global_diagnostics"] == false)
                .count();
            let compared = rows
                .iter()
                .filter(|r| r["matches_global_results"].is_boolean())
                .count();
            println!(
                "{mode:<22} {phase:<5} {:>10} {:>10} {:>10} {:>10}  {}; global compared={compared}, result deltas={differences}, diagnostic deltas={diagnostic_differences}",
                median(&rows, "/total_ns"),
                median(&rows, "/checking_ns"),
                median(&rows, "/preparation_ns"),
                median(&rows, "/after_preparation_ns"),
                outcomes.join(" | ")
            );
        }
    }
    println!("\nFrontend split for cached-bdd (ms; assembly includes attribution, excludes keys):");
    println!("phase       parse projection    queries   assembly       keys      other");
    for phase in PHASES {
        let rows = samples
            .iter()
            .map(|s| &s["cached-bdd"][phase])
            .collect::<Vec<_>>();
        println!(
            "{phase:<7} {}",
            [
                "/parse_ns",
                "/frontend/last/projection_ns",
                "/frontend/last/queries_ns",
                "/frontend/last/assembly_attribution_ns",
                "/frontend/last/key_computation_ns",
                "/frontend_other_ns"
            ]
            .map(|f| format!("{:>10}", median(&rows, f)))
            .join(" ")
        );
    }
    println!(
        "\nFull reparsing in every phase; warm reuses lowering/checker sessions. Differences are observations, not an equivalence proof. Unsupported/incomplete results are not speed wins."
    );
    for failure in data["failures"].as_array().unwrap() {
        eprintln!("scorecard failure: {}", failure.as_str().unwrap());
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let c = Config::parse(args)?;
    if cfg!(debug_assertions) {
        return Err("Use --release for scorecard timings".into());
    }
    let source =
        std::fs::read_to_string(&c.file).map_err(|e| format!("{}: {e}", c.file.display()))?;
    let edited = match &c.edit {
        Some(file) => {
            std::fs::read_to_string(file).map_err(|e| format!("{}: {e}", file.display()))?
        }
        None => default_edit(&source),
    };
    let data = collect(&c, &source, &edited)?;
    print_scorecard(&data);
    if let Some(file) = c.json {
        std::fs::write(file, serde_json::to_vec_pretty(&data).unwrap())
            .map_err(|e| e.to_string())?;
    }
    if !data["failures"].as_array().unwrap().is_empty() {
        return Err("Scorecard contains failures (partial results printed above)".into());
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn config() -> Config {
        Config::parse(["example.inputmapping", "--samples", "1"].map(String::from)).unwrap()
    }

    #[test]
    fn all_paths_and_phases_handle_semantic_edits() {
        let source = "input i,j; slot a; a <- i; a <- j;";
        let data = collect(&config(), source, "input i,j; slot a; a <- i;").unwrap();
        assert_eq!(data["failures"], json!([]));
        let sample = &data["samples"][0];
        for mode in MODES {
            assert_eq!(sample[mode]["warm"]["warm_equals_cold"], true, "{mode}");
            for phase in PHASES {
                assert!(
                    sample[mode][phase]["frontend"]["last"]["assembly_attribution_ns"].is_number()
                );
                assert!(sample[mode][phase]["checking_ns"].is_number());
            }
        }
        assert_eq!(sample["cached-bdd"]["cold"]["results"]["counterexample"], 1);
        assert_eq!(sample["cached-bdd"]["edit"]["results"]["counterexample"], 0);
        assert_eq!(
            sample["fresh-local-bdd"]["warm"]["cache"]["evaluation_hits"],
            0
        );
        assert!(
            sample["cached-bdd"]["warm"]["cache"]["evaluation_hits"]
                .as_u64()
                .unwrap()
                > 0
        );
    }

    #[test]
    fn unsupported_sat_is_reported_without_claiming_equivalence() {
        let source = "input i,j,k; slot a,b; a <- i when available(b); a <- j when available(b); b <- i when available(a); b <- k;";
        let mut c = config();
        c.unconstrained = true;
        let data = collect(&c, source, &default_edit(source)).unwrap();
        assert_eq!(data["failures"], json!([]));
        assert!(
            data["samples"][0]["cached-sat"]["cold"]["results"]["unsupported"]
                .as_u64()
                .unwrap()
                > 0
        );
        assert_eq!(
            data["samples"][0]["cached-sat"]["cold"]["matches_global_results"],
            false
        );
        assert_eq!(
            data["samples"][0]["fresh-local-bdd"]["warm"]["cache"]["evaluation_hits"],
            0
        );
    }

    #[test]
    fn input_errors_and_collision_free_default_edit() {
        assert!(Config::parse(["p", "--samples", "0"].map(String::from)).is_err());
        assert!(Config::parse(["p", "--edit"].map(String::from)).is_err());
        assert!(
            collect(&config(), "not a program", "not a program")
                .unwrap_err()
                .starts_with("Invalid program:")
        );
        let source = "input closeout_probe_0; slot closeout_slot_1; // final comment";
        assert!(default_edit(source).contains("closeout_probe_2"));
        prepare(
            &default_edit(source),
            0,
            &mut lowering::incremental::Session::default(),
        )
        .unwrap();
        let file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("Cargo.toml")
            .to_string_lossy()
            .into_owned();
        assert!(Config::parse([file.clone(), "--json".into(), file]).is_err());
    }
}
