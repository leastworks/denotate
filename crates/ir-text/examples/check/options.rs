use super::Failure;
use denotate_check::{EmptinessExamples, Limits};
use std::{collections::BTreeSet, fmt::Write, time::Duration};

pub const USAGE: &str = "Usage: check ROOT_FOLDER_OR_DEN.ROOT [OPTIONS]\nRun just check-den --help for options and limit defaults.";
pub struct Options {
    pub root: String,
    pub selection: Option<String>,
    pub json: bool,
    pub verbose: bool,
    pub empty_examples: Option<EmptinessExamples>,
    pub hide_library_rewrites: bool,
    pub progress: bool,
    pub profile_memory: Option<String>,
    pub limits: Limits,
}
pub fn limit_values(l: &Limits) -> [(&'static str, u128); 9] {
    [
        ("--timeout-ms", l.timeout.as_millis()),
        ("--max-atoms", l.max_atoms as u128),
        ("--max-rules", l.max_rules as u128),
        ("--max-dependencies", l.max_dependencies as u128),
        ("--max-work", l.max_work as u128),
        ("--max-bdd-variables", l.max_bdd_variables as u128),
        ("--max-bdd-nodes", l.max_bdd_nodes as u128),
        ("--max-bdd-tasks", l.max_bdd_tasks as u128),
        ("--max-condition-nodes", l.max_condition_nodes as u128),
    ]
}
pub fn help() -> String {
    let mut text = String::from(
        "Usage: check ROOT_FOLDER_OR_DEN.ROOT [OPTIONS]\n\n\
        --verification NAME       Run one verification (a partial run)\n\
        --json                    Print existing status summaries on stdout\n\
        --verbose                 Expand all related diagnostic locations\n\
        --empty-examples N|all    Retain N present tuples per empty obligation (default 3)\n\
        --hide-library-rewrites   Hide library rewrite diagnostics\n\
        --no-progress             Silence progress on stderr\n\
        --profile-memory FILE     Stream detailed memory/BDD JSON lines to a new file\n\
        --help, -h                Show this help\n\n\
        Checker limits (nonnegative integers; zero allows no use of that resource):\n",
    );
    for (flag, value) in limit_values(&Limits::default()) {
        writeln!(text, "  {flag} N (default {value})").unwrap();
    }
    text.push_str(
        "\nLimits apply per operation/query, not to the whole command.\n\
        Deadlines are cooperative, not hard timeouts; loading and presentation are outside them.\n\
        Condition nodes count retained BDD condition sizes conservatively, not heap bytes.\n\
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
            selection: None,
            json: false,
            verbose: false,
            empty_examples: None,
            hide_library_rewrites: false,
            progress: true,
            profile_memory: None,
            limits,
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
                "--json" => options.json = true,
                "--verbose" => options.verbose = true,
                "--no-progress" => options.progress = false,
                "--profile-memory" => options.profile_memory = Some(value()?),
                "--hide-library-rewrites" => options.hide_library_rewrites = true,
                "--verification" => options.selection = Some(value()?),
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
                | "--max-condition-nodes" => {
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
        Ok(options)
    }
}
