//! Load a den.root closure and execute its explicit verifications.
use denotate_check::{
    BackendIdentity, Limits, LocalCheckOutcome, OperationalLimits, RegionCompletion,
    RequestPreparation, ScopedResult,
};
use denotate_check_session::Session;
use denotate_ir_text::{filesystem, index, load_with_resolver};
use std::{collections::BTreeSet, fmt::Write};

type Failure = (u8, String);
const USAGE: &str = "Usage: check ROOT_FOLDER_OR_DEN.ROOT [--verification QUALIFIED_NAME]";

fn format_errors(ds: Vec<denotate_ir_text::Diagnostic>) -> String {
    ds.iter()
        .map(|d| {
            format!(
                "{}:{}..{}: {}",
                d.uri, d.range.start, d.range.end, d.message
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}
fn name(namespace: &denotate_ir::Namespace, text: &str) -> String {
    index::Name {
        namespace: Some(namespace.clone()),
        text: text.into(),
        generated: false,
    }
    .spelling()
}

fn run(args: impl IntoIterator<Item = String>, output: &mut String) -> Result<u8, Failure> {
    let mut args = args.into_iter();
    let root = args.next().ok_or((2, USAGE.into()))?;
    let backend = BackendIdentity::bdd();
    let mut selection = None;
    while let Some(option) = args.next() {
        match option.as_str() {
            "--verification" if selection.is_none() => {
                selection = Some(args.next().ok_or((2, USAGE.into()))?)
            }
            _ => {
                return Err((
                    2,
                    format!("Unknown or repeated argument {option:?}; {USAGE}"),
                ));
            }
        }
    }
    let (membership, sources) = filesystem::discover_classified(std::path::Path::new(&root))
        .map_err(|e| {
            let code = if matches!(e, filesystem::DiscoveryError::Operational(_)) {
                3
            } else {
                2
            };
            (code, format_errors(e.diagnostics()))
        })?;
    let p = load_with_resolver(
        &membership,
        &sources,
        Some(&mut filesystem::FileOriginResolver),
    )
    .map_err(|e| (2, format_errors(e)))?;
    writeln!(
        output,
        "Root: {}. Backend: {}. Files: {}.",
        p.root,
        backend.backend,
        p.documents.len()
    )
    .unwrap();
    for notice in &p.embedded.notices {
        writeln!(
            output,
            "Origin unavailable: {} [{} {}]: {:?}",
            notice.source.uri, notice.source.view, notice.source.hash, notice.reason
        )
        .unwrap();
    }
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
    let mut requests = p
        .verification_requests(&limits)
        .map_err(|e| (2, e.to_string()))?;
    let checked = requests
        .iter()
        .flat_map(|(_, r)| r.obligations.iter().cloned())
        .collect::<BTreeSet<_>>();
    // Selection coverage uses every configured verification, so a filtered run does
    // not report obligations that another verification checks as unchecked.
    let mut unchecked = false;
    for obligation in p.corpus.obligations() {
        if !checked.contains(
            p.keys
                .obligation(obligation.id)
                .map_err(|e| (2, e.to_string()))?,
        ) {
            writeln!(
                output,
                "Unchecked obligation {} in program {}",
                name(p.corpus.namespace(obligation.id).unwrap(), &obligation.name),
                p.root
            )
            .unwrap();
            unchecked = true;
        }
    }
    if requests.is_empty() {
        writeln!(output, "No verification configured").unwrap();
        return Ok(2);
    }
    let partial = selection.is_some();
    if let Some(raw) = selection {
        let selected = index::parse_name(&raw).map_err(|e| (2, e))?;
        let matches = p
            .corpus
            .verifications()
            .filter(|v| {
                !selected.generated
                    && v.name == selected.text
                    && selected
                        .namespace
                        .as_ref()
                        .is_none_or(|ns| p.corpus.namespace(v.id) == Some(ns))
            })
            .collect::<Vec<_>>();
        let verification = match matches.as_slice() {
            [v] => p.keys.verification(v.id).map_err(|e| (2, e.to_string()))?,
            [] => return Err((2, format!("Unknown verification {raw:?}"))),
            _ => {
                return Err((
                    2,
                    format!("Ambiguous verification {raw:?}; qualify it with its namespace"),
                ));
            }
        };
        requests.retain(|(key, _)| key == verification);
        writeln!(
            output,
            "Partial run: selected verification {raw}; other verifications were not run."
        )
        .unwrap();
    }
    // Unchecked obligations are incomplete configuration, not findings.
    let mut incomplete = partial || unchecked;
    let mut findings = false;
    let mut session = Session::default();
    for (key, request) in requests {
        let declaration = p
            .corpus
            .verifications()
            .find(|v| p.keys.verification(v.id).is_ok_and(|k| *k == key))
            .unwrap();
        writeln!(
            output,
            "Verification {}",
            name(
                p.corpus.namespace(declaration.id).unwrap(),
                &declaration.name
            )
        )
        .unwrap();
        let assumptions = declaration
            .assumptions
            .iter()
            .map(|id| {
                name(
                    p.corpus.namespace(*id).unwrap(),
                    &p.corpus.assumption(*id).unwrap().name,
                )
            })
            .collect::<Vec<_>>();
        writeln!(output, "Selected assumptions: [{}]", assumptions.join(", ")).unwrap();
        if declaration.obligations.is_empty() {
            writeln!(
                output,
                "No obligations selected; this is a consistency-only verification."
            )
            .unwrap();
        }
        let prepared = session
            .prepare(&request, &p.corpus, &p.keys, &operations)
            .map_err(|e| (2, e.to_string()))?;
        let prepared = match prepared {
            RequestPreparation::Complete(prepared) => prepared,
            RequestPreparation::Inconclusive { reason, .. } => {
                writeln!(output, "Inconclusive: {reason:?}").unwrap();
                incomplete = true;
                continue;
            }
        };
        let admitted = prepared
            .admit(&operations)
            .map_err(|e| (2, e.to_string()))?;
        match session
            .verify(&admitted, &operations)
            .map_err(|e| (2, e.to_string()))?
        {
            LocalCheckOutcome::Complete(report) => {
                let result = &report.checked.results.value;
                incomplete |= result.unfinished.is_some()
                    || !result.incomplete.is_empty()
                    || result.coverage.values().any(|c| !c.complete())
                    || result.groups.values().any(|r| {
                        matches!(
                            r,
                            ScopedResult::Inconclusive(_) | ScopedResult::Unsupported(_)
                        )
                    })
                    || result.regions.values().any(|r| {
                        matches!(r.outcome, ScopedResult::Inconclusive(_))
                            || !matches!(r.completion, RegionCompletion::NoMeaning { .. })
                    });
                let presented = denotate_ir_text::presentation::present(&p, &report.checked)
                    .map_err(|e| (2, e.to_string()))?;
                findings |= presented.status["findings"].as_array().is_some_and(|f| {
                    f.iter()
                        .any(|finding| finding["kind"] != "empty-grouping-domain")
                });
                writeln!(output, "Results: {:#}", presented.status).unwrap();
            }
            LocalCheckOutcome::Inconclusive { reason, .. } => {
                writeln!(output, "Inconclusive: {reason:?}").unwrap();
                incomplete = true;
            }
        }
    }
    Ok(if incomplete {
        2
    } else if findings {
        1
    } else {
        0
    })
}
fn main() {
    let mut output = String::new();
    let result = run(std::env::args().skip(1), &mut output);
    print!("{output}");
    let code = match result {
        Ok(code) => code,
        Err((code, error)) => {
            eprintln!("{error}");
            code
        }
    };
    std::process::exit(code.into());
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };
    struct Fixture(PathBuf);
    impl Fixture {
        fn new(text: &str) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let folder = std::env::temp_dir().join(format!(
                "denotate-check-cli-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&folder).unwrap();
            fs::write(folder.join("den.root"), "{}").unwrap();
            fs::write(folder.join("program.den"), text).unwrap();
            Self(folder)
        }
        fn run(&self, options: &[&str]) -> (u8, String) {
            let mut output = String::new();
            let args = std::iter::once(self.0.to_str().unwrap().to_owned())
                .chain(options.iter().map(|s| s.to_string()));
            let code = match run(args, &mut output) {
                Ok(code) => code,
                Err((code, error)) => {
                    output.push_str(&error);
                    code
                }
            };
            (code, output)
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    const BODY: &str = "sort S; const x, y: S; input p(x:S); relation q(x:S); q(X) :- p(X); assumption a: at_most_one(p, group_by: ()); obligation o: at_most_one(q, group_by: ());";
    const RESTRICTED: &str = "verification v { assumptions: [a]; obligations: [o]; }";
    #[test]
    fn codes_distinguish_proofs_findings_incomplete_and_unconfigured() {
        {
            let backend: Vec<&str> = vec![];
            let proved = Fixture::new(&format!("{BODY} {RESTRICTED}"));
            let (code, output) = proved.run(&backend);
            assert_eq!(code, 0, "{output}");
            assert!(output.contains("Selected assumptions: [::a]"));
            let overlap = Fixture::new(&format!(
                "{BODY} verification v {{ assumptions: []; obligations: [o]; }}"
            ));
            let (code, output) = overlap.run(&backend);
            assert_eq!(code, 1, "{output}");
            assert!(output.contains("counterexample"));
            let incomplete = Fixture::new(&format!(
                "{BODY} verification v {{ assumptions: []; obligations: [o]; }} relation first(); relation second(); first() :- !second(); second() :- !first();"
            ));
            let (code, output) = incomplete.run(&backend);
            assert_eq!(code, 2, "{output}");
            assert!(output.contains("unsupported"));
            let unconfigured = Fixture::new(BODY);
            let (code, output) = unconfigured.run(&backend);
            assert_eq!(code, 2);
            assert!(output.contains("No verification configured"));
            assert!(!output.contains("Results:"));
        }
        let empty = Fixture::new("verification v { assumptions: []; obligations: []; }");
        let (code, output) = empty.run(&[]);
        assert_eq!(code, 0, "{output}");
        assert!(output.contains("consistency-only"));
        let unchecked = Fixture::new(&format!(
            "{BODY} {RESTRICTED} obligation other: at_most_one(q, group_by: ());"
        ));
        let (code, output) = unchecked.run(&[]);
        assert_eq!(code, 2, "{output}");
        assert!(output.contains("Unchecked obligation ::other"));
    }
    #[test]
    fn selectors_use_qualified_name_decoding_and_mark_every_filtered_run_partial() {
        let f = Fixture::new(&format!(
            "namespace 'a::b' {{ {BODY} {RESTRICTED} }} namespace other {{ {BODY} {RESTRICTED} }}"
        ));
        assert_eq!(f.run(&["--verification", "v"]).0, 2);
        assert!(f.run(&["--verification", "v"]).1.contains("Ambiguous"));
        let (code, output) = f.run(&["--verification", "'a::b'::v"]);
        assert_eq!(code, 2, "{output}");
        assert!(output.contains("Partial run:"));
        // The other namespace's obligation is selected by a verification not run here.
        assert!(!output.contains("Unchecked obligation"), "{output}");
        assert_eq!(output.matches("Results:").count(), 1);
        assert!(output.contains("Verification 'a::b'::v"));
        assert!(
            f.run(&["--verification", "absent"])
                .1
                .contains("Unknown verification")
        );
        assert_eq!(f.run(&["--verification"]).0, 2);
        assert_eq!(f.run(&["--verification", "v; sort Injected"]).0, 2);
        let single = Fixture::new(&format!("{BODY} {RESTRICTED}"));
        let (code, output) = single.run(&["--verification", "::v"]);
        assert_eq!(code, 2);
        assert!(output.contains("Partial run:"));
    }
    #[test]
    fn coverage_cli_proofs_failures_and_empty_grouping_notes() {
        {
            let args: &[&str] = &[];
            for (body, code) in [
                ("sort S; const a,b:S; relation p(x:S);", 1),
                ("sort S; const a,b:S; relation p(x:S); p(a); p(b);", 0),
                ("sort S; relation p(x:S);", 0),
            ] {
                let fixture = Fixture::new(&format!(
                    "{body} obligation covered: at_least_one(p, group_by: (x)); verification v {{ assumptions: []; obligations: [covered]; }}"
                ));
                let (actual, output) = fixture.run(args);
                assert_eq!(actual, code, "{output}");
                assert!(output.contains("coverage"));
                if !body.contains("const") {
                    assert!(output.contains("empty-grouping-domain"));
                }
            }
        }
    }
    #[test]
    fn invalid_input_and_operational_failure_have_distinct_codes() {
        let (code, output) = Fixture::new("").run(&["--sat"]);
        assert_eq!(code, 2);
        assert!(output.contains("Unknown or repeated argument"));
        let invalid = Fixture::new("verification v { assumptions: []; }");
        assert_eq!(invalid.run(&[]).0, 2);
        fs::write(invalid.0.join("den.root"), "not json").unwrap();
        assert_eq!(invalid.run(&[]).0, 2);
        fs::remove_file(invalid.0.join("den.root")).unwrap();
        assert_eq!(invalid.run(&[]).0, 3);
    }
}
