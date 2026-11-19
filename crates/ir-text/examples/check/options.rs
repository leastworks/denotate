use super::Failure;
use denotate_check::{EmptinessExamples, InputOrder, Limits};
use std::{collections::BTreeSet, fmt::Write, time::Duration};

pub const USAGE: &str = "Usage: check ROOT_FOLDER_OR_DEN.ROOT [OPTIONS]\nRun just check-den --help for options and limit defaults.";
pub struct Options {
    pub root: String,
    pub sat: bool,
    pub sat_query_limits: denotate_check::stable_query::QueryLimits,
    pub sat_check_options: denotate_check::stable_query::CheckOptions,
    pub selection: Option<String>,
    pub validate_all_assumptions: bool,
    pub json: bool,
    pub verbose: bool,
    pub empty_examples: Option<EmptinessExamples>,
    pub hide_library_rewrites: bool,
    pub progress: bool,
    pub profile_memory: Option<String>,
    pub profile_conditions: bool,
    pub dump_component: Option<String>,
    pub dump_component_limit: usize,
    pub export_committed: Option<String>,
    pub export_limits: denotate_ir_text::committed::ExportLimits,
    pub stop_after_round: Option<usize>,
    pub limits: Limits,
    pub input_order: InputOrder,
    pub checking_within_w: bool,
    pub sat_probe: bool,
    pub candidate_probe: Option<denotate_check::CandidateProbeLimits>,
    pub sat_probe_limits: denotate_check::SatProbeLimits,
}
pub fn limit_values(l: &Limits) -> [(&'static str, u128); 15] {
    [
        ("--timeout-ms", l.timeout.as_millis()),
        ("--max-atoms", l.max_atoms as u128),
        ("--max-rules", l.max_rules as u128),
        ("--max-dependencies", l.max_dependencies as u128),
        ("--max-work", l.max_work as u128),
        (
            "--max-input-order-entries",
            l.max_input_order_entries as u128,
        ),
        ("--max-input-order-work", l.max_input_order_work as u128),
        ("--max-bdd-variables", l.max_bdd_variables as u128),
        ("--max-bdd-nodes", l.max_bdd_nodes as u128),
        ("--max-bdd-tasks", l.max_bdd_tasks as u128),
        ("--max-condition-nodes", l.max_condition_nodes as u128),
        (
            "--max-structural-split-depth",
            l.max_structural_split_depth as u128,
        ),
        (
            "--max-structural-split-leaves",
            l.max_structural_split_leaves as u128,
        ),
        (
            "--max-structural-split-scoring-work",
            l.max_structural_split_scoring_work as u128,
        ),
        (
            "--max-structural-split-work",
            l.max_structural_split_work as u128,
        ),
    ]
}
pub fn help() -> String {
    let mut text = String::from(
        "Usage: check ROOT_FOLDER_OR_DEN.ROOT [OPTIONS]\n\n\
        --verification NAME       Run one verification (a partial run)\n\
        --validate-all-assumptions Validate unselected declarations too (authoring aid)\n\
        --input-order ORDER       Diagnostic BDD order: key (default), reverse-key, structural\n\
        --sat-probe-candidates    Diagnostic guarded-candidate search during admission\n\
        --sat-probe-candidate-limit N  Aggregate candidate cap (default 64)\n\
        --sat-probe-candidate-timeout-ms N  Aggregate diagnostic time (default 10000)\n\
        --sat-probe-candidate-work N  Aggregate encoding/validation work (default 10000000)\n\
        --sat-probe               Diagnostic uniqueness and existence search during admission (progress only)\n\
        --sat-probe-timeout-ms N   Time per probe question, independent of checker timeout (default 10000)\n\
        --sat-probe-refinements N  Maximum unfounded-set refinement rounds (default 64)\n\
        --checking-within-w       Opt in to W-masked checking (may increase storage)\n\
        --json                    Print existing status summaries on stdout\n\
        --verbose                 Expand all related locations and structural proof chains\n\
        --empty-examples N|all    Retain N present tuples per empty obligation (default 3)\n\
        --hide-library-rewrites   Hide library rewrite diagnostics\n\
        --no-progress             Silence progress on stderr\n\
        --profile-conditions      Include condition sizes, assumption steps and failed BDD operations\n\
        --profile-memory FILE     Stream detailed memory/BDD JSON lines to a new file\n\
        --dump-component FILE     Stream bounded admission component diagnostics (local JSONL)\n\
        --dump-component-limit N  Aggregate data record cap (default 100000)\n\
        --export-committed FILE   Atomically write one verification's committed graph to a new .den file\n\
        --stop-after-round N      Stop after a whole admission round; requires --export-committed (exit 2)\n\
        --export-max-work N       Independent export work cap (default 100000000)\n\
        --export-max-bytes N      Independent export byte cap (default 1073741824)\n\
        --export-timeout-ms N     Independent export deadline (default 120000)\n\
        --help, -h                Show this help\n\n\
        Checker limits (nonnegative integers; zero allows no use of that resource):\n",
    );
    for (flag, value) in limit_values(&Limits::default()) {
        writeln!(text, "  {flag} N (default {value})").unwrap();
    }
    text.push_str("\nExperimental SAT checking (default engine: bdd):\n  --engine bdd|sat\n  --sat-meaning full|uniqueness|none (default full; skipped meaning keeps exit 2)\n  --sat-max-worlds N (default 1024)\n  --sat-max-tuples N (default 10000)\n  --sat-max-solves N (default 128)\n  --sat-max-refinements N (default 64)\n  --sat-max-polls N (default 100000)\n  --sat-max-conflicts N (default 100000)\n  --sat-max-propagations N (default 1000000)\nSAT checks empty and at_most_one, all fixed obligations, and whole-program meaning.\nOther symbolic obligations and notices are explicitly not analysed.\n");
    text.push_str(
        "\nLimits apply per operation/query, not to the whole command.\n\
        Deadlines are cooperative, not hard timeouts; loading and presentation are outside them.\n\
        Condition nodes count retained BDD condition sizes conservatively, not heap bytes.\n\
        Structural split limits apply per component attempt; exhausting them falls back to ordinary admission.\n\
        Progress is on stderr even with --json; redirect stderr to retain a trace.\n\
        Exit codes: 0 proved, 1 findings, 2 incomplete/invalid/partial, 3 operational failure.\n",
    );
    text
}
impl Options {
    pub fn parse(args: impl IntoIterator<Item = String>, limits: Limits) -> Result<Self, Failure> {
        let mut args = args.into_iter();
        let root = args.next().ok_or((2, USAGE.into()))?;
        let mut options = Self {
            root,
            sat: false,
            sat_query_limits: Default::default(),
            sat_check_options: Default::default(),
            selection: None,
            validate_all_assumptions: false,
            json: false,
            verbose: false,
            empty_examples: None,
            hide_library_rewrites: false,
            progress: true,
            profile_memory: None,
            profile_conditions: false,
            dump_component: None,
            dump_component_limit: 100_000,
            export_committed: None,
            export_limits: Default::default(),
            stop_after_round: None,
            limits,
            input_order: InputOrder::Key,
            checking_within_w: false,
            sat_probe: false,
            candidate_probe: None,
            sat_probe_limits: Default::default(),
        };
        let mut seen = BTreeSet::new();
        while let Some(option) = args.next() {
            if !seen.insert(option.clone()) {
                return Err((
                    2,
                    format!("Unknown or repeated argument {option:?}; {USAGE}"),
                ));
            }
            let mut value = || args.next().ok_or((2, format!("{option} requires a value")));
            match option.as_str() {
                "--engine" => {
                    options.sat = match value()?.as_str() {
                        "bdd" => false,
                        "sat" => true,
                        _ => return Err((2, "--engine requires bdd or sat".into())),
                    }
                }
                "--sat-meaning" => {
                    use denotate_check::stable_query::MeaningMode;
                    options.sat_check_options.meaning = match value()?.as_str() {
                        "full" => MeaningMode::Full,
                        "uniqueness" => MeaningMode::Uniqueness,
                        "none" => MeaningMode::None,
                        _ => {
                            return Err((
                                2,
                                "--sat-meaning requires full, uniqueness or none".into(),
                            ));
                        }
                    };
                }
                "--sat-max-worlds"
                | "--sat-max-tuples"
                | "--sat-max-solves"
                | "--sat-max-refinements"
                | "--sat-max-polls" => {
                    let n = value()?
                        .parse::<usize>()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    match option.as_str() {
                        "--sat-max-worlds" => options.sat_check_options.max_worlds = n,
                        "--sat-max-tuples" => options.sat_check_options.max_tuples = n,
                        "--sat-max-solves" => options.sat_query_limits.max_solves = n,
                        "--sat-max-refinements" => options.sat_query_limits.max_refinements = n,
                        _ => options.sat_query_limits.max_solver_polls = n,
                    }
                }
                "--sat-max-conflicts" | "--sat-max-propagations" => {
                    let n = value()?
                        .parse::<u64>()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    if option == "--sat-max-conflicts" {
                        options.sat_query_limits.max_conflicts = n
                    } else {
                        options.sat_query_limits.max_propagations = n
                    }
                }
                "--validate-all-assumptions" => options.validate_all_assumptions = true,
                "--json" => options.json = true,
                "--checking-within-w" => options.checking_within_w = true,
                "--verbose" => options.verbose = true,
                "--no-progress" => options.progress = false,
                "--profile-memory" => options.profile_memory = Some(value()?),
                "--profile-conditions" => options.profile_conditions = true,
                "--dump-component" => options.dump_component = Some(value()?),
                "--export-committed" => options.export_committed = Some(value()?),
                "--stop-after-round" => {
                    let n = value()?
                        .parse::<usize>()
                        .ok()
                        .filter(|n| *n > 0)
                        .ok_or((2, "--stop-after-round requires a positive integer".into()))?;
                    options.stop_after_round = Some(n);
                }
                "--export-max-work" | "--export-max-bytes" => {
                    let n = value()?
                        .parse::<usize>()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    if option == "--export-max-work" {
                        options.export_limits.max_work = n;
                    } else {
                        options.export_limits.max_bytes = n;
                    }
                }
                "--export-timeout-ms" => {
                    options.export_limits.timeout =
                        Duration::from_millis(value()?.parse::<u64>().map_err(|_| {
                            (2, format!("{option} requires a nonnegative integer"))
                        })?);
                }
                "--dump-component-limit" => {
                    options.dump_component_limit = value()?
                        .parse()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?
                }
                "--hide-library-rewrites" => options.hide_library_rewrites = true,
                "--verification" => options.selection = Some(value()?),
                "--input-order" => {
                    options.input_order = value()?.parse().map_err(|e: &str| (2, e.into()))?
                }
                "--empty-examples" => {
                    let text = value()?;
                    options.empty_examples = Some(if text == "all" {
                        EmptinessExamples::All
                    } else {
                        EmptinessExamples::Limited(text.parse().map_err(|_| {
                            (
                                2,
                                "--empty-examples requires a positive integer or all".into(),
                            )
                        })?)
                    });
                }
                "--sat-probe-candidates" => {
                    options.candidate_probe.get_or_insert_with(Default::default);
                }
                "--sat-probe-candidate-limit" | "--sat-probe-candidate-work" => {
                    let n = value()?
                        .parse()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    let probe = options.candidate_probe.get_or_insert_with(Default::default);
                    if option == "--sat-probe-candidate-limit" {
                        probe.max_candidates = n;
                    } else {
                        probe.max_work = n;
                    }
                }
                "--sat-probe-candidate-timeout-ms" => {
                    let n = value()?
                        .parse()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    options
                        .candidate_probe
                        .get_or_insert_with(Default::default)
                        .timeout = Duration::from_millis(n);
                }
                "--sat-probe" => options.sat_probe = true,
                "--sat-probe-timeout-ms" => {
                    let n = value()?
                        .parse::<u64>()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                    options.sat_probe_limits.timeout = Duration::from_millis(n);
                }
                "--sat-probe-refinements" => {
                    options.sat_probe_limits.max_refinements = value()?
                        .parse()
                        .map_err(|_| (2, format!("{option} requires a nonnegative integer")))?;
                }
                "--timeout-ms" => {
                    let n: u64 = value()?.parse().map_err(|_| {
                        (
                            2,
                            format!("{option} requires a nonnegative integer fitting in u64"),
                        )
                    })?;
                    options.limits.timeout = Duration::from_millis(n);
                }
                "--max-atoms"
                | "--max-rules"
                | "--max-dependencies"
                | "--max-work"
                | "--max-bdd-variables"
                | "--max-bdd-nodes"
                | "--max-bdd-tasks"
                | "--max-condition-nodes"
                | "--max-input-order-entries"
                | "--max-input-order-work"
                | "--max-structural-split-depth"
                | "--max-structural-split-leaves"
                | "--max-structural-split-work"
                | "--max-structural-split-scoring-work" => {
                    let n: usize = value()?.parse().map_err(|_| {
                        (
                            2,
                            format!("{option} requires a nonnegative integer fitting in usize"),
                        )
                    })?;
                    match option.as_str() {
                        "--max-atoms" => options.limits.max_atoms = n,
                        "--max-rules" => options.limits.max_rules = n,
                        "--max-dependencies" => options.limits.max_dependencies = n,
                        "--max-work" => options.limits.max_work = n,
                        "--max-bdd-variables" => options.limits.max_bdd_variables = n,
                        "--max-bdd-nodes" => options.limits.max_bdd_nodes = n,
                        "--max-bdd-tasks" => options.limits.max_bdd_tasks = n,
                        "--max-condition-nodes" => options.limits.max_condition_nodes = n,
                        "--max-input-order-entries" => options.limits.max_input_order_entries = n,
                        "--max-input-order-work" => options.limits.max_input_order_work = n,
                        "--max-structural-split-depth" => {
                            options.limits.max_structural_split_depth = n
                        }
                        "--max-structural-split-leaves" => {
                            options.limits.max_structural_split_leaves = n
                        }
                        "--max-structural-split-scoring-work" => {
                            options.limits.max_structural_split_scoring_work = n
                        }
                        "--max-structural-split-work" => {
                            options.limits.max_structural_split_work = n
                        }
                        _ => unreachable!(),
                    }
                }
                _ => {
                    return Err((
                        2,
                        format!("Unknown or repeated argument {option:?}; {USAGE}"),
                    ));
                }
            }
        }
        if options.stop_after_round.is_some() && options.export_committed.is_none() {
            return Err((2, "--stop-after-round requires --export-committed".into()));
        }
        if options.profile_conditions && options.profile_memory.is_none() {
            return Err((2, "--profile-conditions requires --profile-memory".into()));
        }
        if options.sat {
            for flag in &seen {
                if flag.starts_with("--sat-probe")
                    || matches!(
                        flag.as_str(),
                        "--checking-within-w"
                            | "--input-order"
                            | "--profile-conditions"
                            | "--dump-component"
                            | "--dump-component-limit"
                            | "--export-committed"
                            | "--stop-after-round"
                            | "--hide-library-rewrites"
                    )
                    || flag.starts_with("--export-")
                {
                    return Err((
                        2,
                        format!(
                            "{flag} is a BDD/admission option and cannot be used with --engine sat"
                        ),
                    ));
                }
            }
        } else if seen
            .iter()
            .any(|f| f.starts_with("--sat-max-") || f == "--sat-meaning")
        {
            return Err((
                2,
                "--sat-max-* and --sat-meaning options require --engine sat".into(),
            ));
        }
        Ok(options)
    }
}
