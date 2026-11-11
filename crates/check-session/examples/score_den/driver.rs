use super::{
    outcomes::{self, Outcomes},
    report,
    scorecard_support::{MODES, session},
};
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::VerificationKey;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, filesystem, load};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

const USAGE: &str = "score_den ROOT_FOLDER_OR_DEN.ROOT [--edit ROOT] [--samples N] [--timeout-ms N] [--unconstrained] [--json FILE]";
pub struct Config {
    pub root: PathBuf,
    pub edit: Option<PathBuf>,
    pub json: Option<PathBuf>,
    pub samples: usize,
    pub unconstrained: bool,
    pub limits: Limits,
}
impl Config {
    pub fn parse(args: impl IntoIterator<Item = String>) -> Result<Self, String> {
        let mut args = args.into_iter();
        let root = args.next().ok_or(USAGE)?;
        if root.starts_with("--") {
            return Err(USAGE.into());
        }
        let mut c = Self {
            root: root.into(),
            edit: None,
            json: None,
            samples: 5,
            unconstrained: false,
            limits: Limits {
                timeout: Duration::from_secs(60),
                ..Limits::default()
            },
        };
        let mut seen = BTreeSet::new();
        while let Some(arg) = args.next() {
            if !seen.insert(arg.clone()) {
                return Err(format!("Repeated option {arg}"));
            }
            if arg == "--unconstrained" {
                c.unconstrained = true;
                continue;
            }
            if !matches!(
                arg.as_str(),
                "--edit" | "--json" | "--samples" | "--timeout-ms"
            ) {
                return Err(format!("Unknown option {arg}; {USAGE}"));
            }
            let value = args
                .next()
                .ok_or_else(|| format!("Missing value for {arg}"))?;
            match arg.as_str() {
                "--edit" => c.edit = Some(value.into()),
                "--json" => c.json = Some(value.into()),
                "--samples" => c.samples = value.parse().map_err(|_| "Invalid sample count")?,
                "--timeout-ms" => {
                    c.limits.timeout =
                        Duration::from_millis(value.parse().map_err(|_| "Invalid timeout")?)
                }
                _ => unreachable!(),
            }
        }
        if c.samples == 0 || c.limits.timeout.is_zero() {
            return Err("Samples and timeout must be positive".into());
        }
        Ok(c)
    }
    pub fn validate_output(&self, base: &Snapshot, edit: Option<&Snapshot>) -> Result<(), String> {
        if let Some(path) = &self.json {
            let path = path.canonicalize().unwrap_or_else(|_| path.clone());
            if path.extension().is_some_and(|e| e == "den")
                || path.file_name().is_some_and(|n| n == "den.root")
            {
                return Err("JSON output must not be a .den source or den.root manifest".into());
            }
            let uri = filesystem::uri(&path);
            if std::iter::once(base)
                .chain(edit)
                .any(|s| s.sources.iter().any(|s| s.uri == uri))
            {
                return Err("JSON output must not overwrite an input source".into());
            }
        }
        Ok(())
    }
}
#[derive(Clone)]
pub struct Snapshot {
    pub membership: ProgramMembership,
    pub sources: Vec<SourceFile>,
}
fn errors(ds: Vec<denotate_ir_text::Diagnostic>) -> String {
    ds.into_iter()
        .map(|d| {
            format!(
                "{}:{}..{}: {}",
                d.uri, d.range.start, d.range.end, d.message
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}
impl Snapshot {
    pub fn discover(root: &Path) -> Result<Self, String> {
        let (membership, sources) = filesystem::discover(root).map_err(errors)?;
        Ok(Self {
            membership,
            sources,
        })
    }
    pub fn load(&self, warm: bool) -> Result<LoadedProgram, String> {
        let sources = self
            .sources
            .iter()
            .map(|s| {
                if warm {
                    SourceFile::new(
                        &s.uri,
                        s.revision + 1,
                        format!("{}\n// scorecard warm snapshot\n", s.text),
                    )
                } else {
                    s.clone()
                }
            })
            .collect::<Vec<_>>();
        load(&self.membership, &sources).map_err(errors)
    }
}
pub struct Run {
    pub row: Value,
    pub outcomes: Option<Outcomes>,
}
impl Run {
    fn finish(
        mut self,
        results: ScopedResults,
        p: &LoadedProgram,
        consistency: Option<bool>,
        receipts: WorkReceipts,
    ) -> Self {
        let mut outcomes = Outcomes::from_results(p, &results);
        outcomes.consistency = match consistency {
            Some(true) => "consistent",
            Some(false) => "inconsistent",
            None => "unknown",
        };
        if results.notices.values().any(|n| {
            matches!(
                n.state,
                NoticeState::Unknown(NoticeUnknown::Deadline { .. })
            )
        }) {
            self.row["error"] = json!({"stage":"notices","detail":"notice deadline"});
        }
        self.row["outcomes"] = outcomes.json();
        self.row["bdd"] = report::work(&receipts);
        self.outcomes = Some(outcomes);
        self
    }
    fn error(mut self, error: CheckError, stage: &str) -> Self {
        self.row["error"] = json!({"stage":stage,"detail":error.to_string()});
        self
    }
}
/// Exactly one invocation of each reached checker stage. All JSON construction,
/// loading, sizes, cache statistics and controls are outside these timers.
pub fn measure(
    p: &LoadedProgram,
    request: &CheckRequest,
    mode: &str,
    cache: &mut Option<Session>,
    limits: &Limits,
) -> Run {
    let operations = OperationalLimits::from(limits);
    let general = request
        .constraints
        .iter()
        .any(|c| matches!(c, InputConstraint::Cardinality { .. }));
    let mut run = Run {
        row: json!({"timings_ns":{"preparation":null,"admission":null,"checking":null,"notices":null},
        "size":null,"cache":null,"preparation_cache":null,"bdd":null,"outcomes":null,
        "effective_path":if mode=="global-bdd" {"global-bdd"}else if general {"global-bdd-general-assumptions"}else{"local-bdd"},
        "selection_kind":if request.obligations.is_empty() {if request.notices.is_empty(){"consistency-only"}else{"notices-only"}}else{"obligations"},
            "selected":{"assumptions":request.constraints.len(),"obligations":request.obligations.len(),"notices":request.notices.len()}}),
        outcomes: None,
    };
    let start = Instant::now();
    let prepared = match cache {
        Some(s) => s.prepare(request, &p.corpus, &p.keys, &operations),
        None => request.prepare(&p.corpus, &p.keys, &operations),
    };
    run.row["timings_ns"]["preparation"] = json!(start.elapsed().as_nanos());
    // An operational failure may precede the session's counter reset. Do not
    // publish counters from the previous snapshot in that case.
    if prepared.is_ok() {
        if let Some(s) = cache.as_ref() {
            run.row["preparation_cache"] = report::preparation_stats(s, mode);
        }
    }
    let prepared = match prepared {
        Err(e) => return run.error(e, "preparation"),
        Ok(RequestPreparation::Inconclusive { reason, receipts }) => {
            return run.finish(request.exhausted(reason), p, None, receipts);
        }
        Ok(RequestPreparation::Complete(prepared)) => prepared,
    };
    run.row["size"] = report::size(&prepared);
    let consistent = prepared.program().assumptions_consistent();
    let before_admission = prepared.receipts().clone();
    let start = Instant::now();
    let admitted = prepared.admit(&operations);
    run.row["timings_ns"]["admission"] = json!(start.elapsed().as_nanos());
    let prepared = match admitted {
        Ok(p) => p,
        Err(CheckError::LimitExceeded {
            phase,
            resource,
            details,
        }) => {
            return run.finish(
                request.exhausted(Inconclusive {
                    phase,
                    resource,
                    details,
                }),
                p,
                Some(consistent),
                before_admission,
            );
        }
        Err(e) => return run.error(e, "admission"),
    };
    drop(before_admission);
    let mut metrics = VerificationMetrics::default();
    let start = Instant::now();
    let result = match cache {
        Some(s) => s
            .verify_with_metrics(&prepared, &operations, &mut metrics)
            .map(|r| match r {
                LocalCheckOutcome::Complete(r) => Ok(r.checked.results),
                LocalCheckOutcome::Inconclusive { reason, receipts } => Err((reason, receipts)),
            }),
        None => prepared
            .verify_with_metrics(&operations, &mut metrics)
            .map(|r| match r {
                CheckOutcome::Complete(r) => Ok(r.results),
                CheckOutcome::Inconclusive {
                    reason, receipts, ..
                } => Err((reason, receipts)),
            }),
    };
    let total = start.elapsed();
    run.row["verification_call_ns"] = json!(total.as_nanos());
    run.row["timings_ns"]["checking"] = json!(
        total
            .checked_sub(metrics.notices.unwrap_or_default())
            .expect("notice pass within verify")
            .as_nanos()
    );
    run.row["timings_ns"]["notices"] = json!(metrics.notices.map(|d| d.as_nanos()));
    if let Some(s) = cache.as_ref() {
        run.row["cache"] = report::cache(s);
    }
    match result {
        Err(e) => run.error(e, "checking"),
        Ok(Err((reason, receipts))) => {
            run.finish(request.exhausted(reason), p, Some(consistent), receipts)
        }
        Ok(Ok(results)) => run.finish(results.value, p, Some(consistent), results.receipts),
    }
}
fn request(
    p: &LoadedProgram,
    key: &VerificationKey,
    limits: &Limits,
) -> Result<CheckRequest, String> {
    p.verification_requests(limits)
        .map_err(|e| e.to_string())?
        .into_iter()
        .find(|(k, _)| k == key)
        .map(|(_, r)| r)
        .ok_or_else(|| format!("Missing verification {}", outcomes::name(&key.0)))
}
fn configuration(p: &LoadedProgram, requests: &[(VerificationKey, CheckRequest)]) -> Value {
    let selected = requests
        .iter()
        .flat_map(|(_, r)| r.obligations.iter())
        .collect::<BTreeSet<_>>();
    let unchecked = p
        .corpus
        .obligations()
        .filter_map(|o| {
            let key = p.keys.obligation(o.id).unwrap();
            (!selected.contains(key)).then(|| outcomes::name(&key.0))
        })
        .collect::<Vec<_>>();
    json!({"state":if requests.is_empty(){"unconfigured"}else if !unchecked.is_empty(){"unchecked-obligations"}else{"configured"},"unchecked_obligations":unchecked})
}
pub fn collect(c: &Config, base: &Snapshot, edit: Option<&Snapshot>) -> Result<Value, String> {
    let p = base.load(false)?;
    let e = edit.map(|s| s.load(false)).transpose()?;
    for program in std::iter::once(&p).chain(e.as_ref()) {
        let validation =
            validate_assumption_cones(&program.corpus, &program.domains, &program.keys, &c.limits)
                .map_err(|e| e.to_string())?;
        if !validation.is_valid() {
            return Err(format!(
                "Assumption validation: {}",
                denotate_ir_text::presentation::present_assumption_validation(program, &validation)
                    .map_err(|e| e.to_string())?
                    .status
            ));
        }
    }
    let requests = p
        .verification_requests(&c.limits)
        .map_err(|e| e.to_string())?;
    let edited = e
        .as_ref()
        .map(|p| p.verification_requests(&c.limits))
        .transpose()
        .map_err(|e| e.to_string())?;
    let base_keys = requests
        .iter()
        .map(|(k, _)| k.clone())
        .collect::<BTreeSet<_>>();
    let edit_keys = edited
        .iter()
        .flatten()
        .map(|(k, _)| k.clone())
        .collect::<BTreeSet<_>>();
    let mut configurations = json!({"base":configuration(&p,&requests)});
    if let (Some(p), Some(rs)) = (&e, &edited) {
        configurations["edit"] = configuration(p, rs);
    }
    let mut verifications = Vec::new();
    let mut failures = BTreeSet::new();
    for key in base_keys.union(&edit_keys) {
        let before = base_keys.contains(key);
        let after = edit_keys.contains(key);
        let change = if edit.is_none() {
            "unchanged"
        } else if !before {
            "added"
        } else if !after {
            "removed"
        } else {
            "retained"
        };
        let mut samples = Vec::new();
        for iteration in 0..=c.samples {
            eprintln!(
                "score-den: {}, {} {iteration}/{}",
                outcomes::name(&key.0),
                if iteration == 0 { "warm-up" } else { "sample" },
                c.samples
            );
            let mut modes = MODES.to_vec();
            if iteration % 2 == 1 {
                modes[1..].reverse();
            }
            let mut global = BTreeMap::<&str, Run>::new();
            let mut rows = serde_json::Map::new();
            for mode in modes {
                let mut cache = session(mode, c.unconstrained);
                let mut cold = None;
                let mut phases = serde_json::Map::new();
                let snapshots = [
                    ("cold", before.then_some(base)),
                    ("warm", before.then_some(base)),
                    ("edit", after.then_some(edit).flatten()),
                ];
                for (phase, snapshot) in snapshots {
                    let Some(snapshot) = snapshot else {
                        continue;
                    };
                    let program = snapshot.load(phase == "warm")?;
                    let req = request(&program, key, &c.limits)?;
                    let mut run = measure(&program, &req, mode, &mut cache, &c.limits);
                    let label = format!(
                        "sample {iteration}, {}, {mode}/{phase}",
                        outcomes::name(&key.0)
                    );
                    if let Some(error) = run.row.get("error") {
                        failures.insert(format!("{label}: {error}"));
                    }
                    if phase == "warm" {
                        let equal = run
                            .outcomes
                            .as_ref()
                            .zip(cold.as_ref())
                            .map(|(a, b)| a == b);
                        run.row["warm_equals_cold"] = json!(equal);
                        if equal == Some(false) {
                            failures
                                .insert(format!("{label}: keyed warm outcomes differ from cold"));
                        }
                    }
                    // Cold is already fresh. The equivalent warm snapshot uses
                    // cold as its control. Edits get a separate fresh SAME-path
                    // control, in addition to the whole-program control below.
                    if phase == "edit" {
                        let control_p = snapshot.load(false)?;
                        let control_req = request(&control_p, key, &c.limits)?;
                        let control = measure(
                            &control_p,
                            &control_req,
                            mode,
                            &mut session(mode, c.unconstrained),
                            &c.limits,
                        );
                        let equal = run
                            .outcomes
                            .as_ref()
                            .zip(control.outcomes.as_ref())
                            .map(|(a, b)| a == b);
                        run.row["matches_fresh_control"] = json!(equal);
                        if equal == Some(false) {
                            failures.insert(format!(
                                "{label}: keyed edited outcomes differ from fresh control"
                            ));
                        }
                        if let Some(error) = control.row.get("error") {
                            failures.insert(format!("{label}, fresh control: {error}"));
                        }
                    } else {
                        run.row["matches_fresh_control"] = if phase == "cold" {
                            json!(run.outcomes.is_some())
                        } else {
                            run.row["warm_equals_cold"].clone()
                        };
                    }
                    if let Some(control) = global.get(phase) {
                        run.row["matches_global_control"] = json!(
                            run.outcomes
                                .as_ref()
                                .zip(control.outcomes.as_ref())
                                .map(|(a, b)| a == b)
                        );
                        let conflict = run
                            .outcomes
                            .as_ref()
                            .zip(control.outcomes.as_ref())
                            .map(|(a, b)| a.contradicts(b));
                        run.row["contradicts_global_control"] = json!(conflict);
                        if conflict == Some(true) {
                            failures.insert(format!(
                                "{label}: conclusive contradiction with global control"
                            ));
                        }
                    }
                    if phase == "cold" {
                        cold = run.outcomes.clone();
                    }
                    phases.insert(phase.into(), run.row.clone());
                    if mode == "global-bdd" {
                        global.insert(phase, run);
                    }
                }
                rows.insert(mode.into(), json!(phases));
            }
            if iteration > 0 {
                samples.push(json!(rows));
            }
        }
        verifications
            .push(json!({"name":outcomes::name(&key.0),"change":change,"samples":samples}));
    }
    Ok(
        json!({"schema_version":1,"root":c.root,"edit_root":c.edit,"samples":c.samples,
        "configuration":configurations,"limits":report::limits(&c.limits),
        "variants":MODES.iter().map(|m|report::variant(m,c.unconstrained)).collect::<Vec<_>>(),
        "verifications":verifications,"failures":failures,
        "measurement_notes":{
            "timing":"Non-overlapping checker phases. Loading, size inspection, reporting and fresh controls excluded. Null means not reached/not selected. Preparation includes assumption evaluation; notice pass is timed inside checking once.",
            "size":"After preparation, before admission rewrites. Largest five components sorted by atoms then rules. Null group totals mean arithmetic overflow; no Cartesian product is enumerated for statistics.",
            "bdd":"Maxima of logical per-query receipt observations, including reused work and rejected attempts. Not simultaneous memory peaks or fresh allocations. Cache retained_condition_nodes sampled after verify; conservative retained payload, not RSS. Null means unavailable.",
            "regions":"Unsupported and no-meaning counts can overlap: a blocked region can also have a replayed no-meaning observation.",
            "comparisons":"Semantic-keyed obligation/component/group, region and notice outcomes; witnesses excluded. Edit uses fresh same-path control. Global agreement reported separately; only conclusive contradictions across paths fail. Incomplete/unsupported results are not speed wins.",
            "retention":"Session envelope shared with planning (up to 1/8 bytes, 1/2 entries) and optional grounding (up to 1/4 bytes). --unconstrained affects retention only; fresh-local retains no entries.",
            "sharing":"Ordinary names and paths. Results stay with the program; this is not an anonymised export."}}),
    )
}
