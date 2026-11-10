//! Load a den.root closure and execute its explicit verifications.
use denotate_check::{
    BackendIdentity, EmptinessExamples, Limits, LocalCheckOutcome, OperationalLimits,
    RegionCompletion, RequestPreparation, ScopedResult,
};
use denotate_check_session::Session;
use denotate_ir_text::{
    LoadedProgram, filesystem, index, load_with_resolver, origins, presentation,
};
use std::{collections::BTreeSet, fmt::Write};

type Failure = (u8, String);
const USAGE: &str = "Usage: check ROOT_FOLDER_OR_DEN.ROOT [--verification QUALIFIED_NAME] [--json] [--verbose] [--empty-examples N|all] [--hide-library-rewrites]";

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

/// Render the shared presenter's output only; semantic interpretation and
/// source-placement policy stay in presentation.
fn print_diagnostics(
    p: &LoadedProgram,
    presented: &presentation::Presentation,
    output: &mut String,
    verbose: bool,
) -> Result<(), Failure> {
    let location = |span: denotate_ir::SourceSpan| -> Result<_, Failure> {
        let source = p
            .sources
            .snapshot(span.snapshot())
            .map_err(|e| (2, e.to_string()))?;
        let coordinate = origins::coordinate(&source.text, span.byte_range().start)
            .ok_or((2, "Invalid diagnostic source coordinate".into()))?;
        Ok((source.uri.clone(), coordinate))
    };
    let mut diagnostics = Vec::new();
    for d in &presented.diagnostics {
        let mut notes = d.notes.iter().map(String::as_str).collect::<Vec<_>>();
        notes.sort();
        let mut related = d
            .related
            .iter()
            .map(|r| Ok((location(r.span)?, r.label.as_str())))
            .collect::<Result<Vec<_>, Failure>>()?;
        related.sort();
        diagnostics.push((
            location(d.primary)?,
            d.kind.code(),
            d.message.as_str(),
            notes,
            related,
        ));
    }
    diagnostics.sort();
    for ((uri, at), kind, message, notes, related) in diagnostics {
        writeln!(output, "{uri}:{}:{}: {kind}: {message}", at.line, at.column).unwrap();
        for note in notes {
            writeln!(output, "  note: {note}").unwrap();
        }
        let mut hidden = 0;
        for ((uri, at), label) in related {
            if !verbose
                && !matches!(
                    label,
                    "producing rule"
                        | "checked obligation"
                        | "upstream source origin"
                        | "blocking dependency cycle"
                        | "condition being inspected"
                        | "complete enclosing scope"
                )
            {
                hidden += 1;
                continue;
            }
            writeln!(
                output,
                "  related: {uri}:{}:{}: {label}",
                at.line, at.column
            )
            .unwrap();
        }
        if hidden > 0 {
            writeln!(output, "  +{hidden} more related locations (use --verbose)").unwrap();
        }
    }
    Ok(())
}

fn run(args: impl IntoIterator<Item = String>, output: &mut String) -> Result<u8, Failure> {
    run_with_limits(args, output, Limits::default())
}
fn run_with_limits(
    args: impl IntoIterator<Item = String>,
    output: &mut String,
    limits: Limits,
) -> Result<u8, Failure> {
    let mut args = args.into_iter();
    let root = args.next().ok_or((2, USAGE.into()))?;
    let backend = BackendIdentity::bdd();
    let mut selection = None;
    let mut json = false;
    let mut verbose = false;
    let mut empty_examples = None;
    let mut hide_library_rewrites = false;
    while let Some(option) = args.next() {
        match option.as_str() {
            "--json" if !json => json = true,
            "--verbose" if !verbose => verbose = true,
            "--hide-library-rewrites" if !hide_library_rewrites => hide_library_rewrites = true,
            "--empty-examples" if empty_examples.is_none() => {
                let value = args.next().ok_or((2, USAGE.into()))?;
                empty_examples = Some(if value == "all" {
                    EmptinessExamples::All
                } else {
                    EmptinessExamples::Limited(value.parse().map_err(|_| {
                        (
                            2,
                            "--empty-examples requires a positive integer or all".into(),
                        )
                    })?)
                });
            }
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
    let operations = OperationalLimits::from(&limits);
    let validation =
        denotate_check::validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &limits)
            .map_err(|e| (2, e.to_string()))?;
    if !validation.is_valid() {
        let presented = presentation::present_assumption_validation(&p, &validation)
            .map_err(|e| (2, e.to_string()))?;
        if json {
            writeln!(output, "Assumption validation: {:#}", presented.status).unwrap();
        } else {
            writeln!(output, "Assumption validation").unwrap();
            print_diagnostics(&p, &presented, output, verbose)?;
        }
    }
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
    let mut incomplete = partial || unchecked || !validation.is_valid();
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
        if let Some(state) = validation
            .selected_failure(&p.corpus, &p.keys, &request)
            .map_err(|e| (2, e.to_string()))?
        {
            writeln!(
                output,
                "Not checked: selected assumption validation is {}.",
                state.label()
            )
            .unwrap();
            incomplete = true;
            continue;
        }
        if declaration.obligations.is_empty() && declaration.notices.is_empty() {
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
            .map_err(|e| (2, e.to_string()))?
            .with_emptiness_examples(empty_examples.unwrap_or_default());
        match session
            .verify(&admitted, &operations)
            .map_err(|e| (2, e.to_string()))?
        {
            LocalCheckOutcome::Complete(report) => {
                let result = &report.checked.results.value;
                incomplete |= result.unfinished.is_some()
                    || !result.incomplete.is_empty()
                    || result.coverage.values().any(|c| !c.complete())
                    || result.emptiness.values().any(|e| !e.complete())
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
                let mut presented = denotate_ir_text::presentation::present(&p, &report.checked)
                    .map_err(|e| (2, e.to_string()))?;
                findings |= presented.status["findings"].as_array().is_some_and(|f| {
                    f.iter().any(|finding| {
                        !matches!(
                            finding["kind"].as_str(),
                            Some(
                                "empty-grouping-domain"
                                    | "impossible-condition"
                                    | "always-true-condition"
                                    | "unanalysed-condition"
                            )
                        )
                    })
                });
                if hide_library_rewrites {
                    presented.hide_library_rewrites(&p);
                }
                if json {
                    writeln!(output, "Results: {:#}", presented.status).unwrap();
                } else {
                    print_diagnostics(&p, &presented, output, verbose)?;
                    if let Some(count) = presented.status["hiddenLibraryRewrites"]
                        .as_u64()
                        .filter(|n| *n > 0)
                    {
                        writeln!(output, "{count} library rewrite findings hidden; omit --hide-library-rewrites to show them (status and exit code unchanged).").unwrap();
                    }
                    writeln!(
                        output,
                        "Result: {}",
                        presented.status["state"].as_str().unwrap()
                    )
                    .unwrap();
                }
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
    fn invalid_assumptions_are_located_without_verifications_and_block_only_selection() {
        let body = "input i(); relation p(); p():-i(),!p(); assumption invalid:empty(p); assumption exclude:empty(i);";
        for verifications in [
            "",
            "verification bad { assumptions:[invalid]; obligations:[]; } verification good { assumptions:[exclude]; obligations:[]; }",
        ] {
            let fixture = Fixture::new(&format!("{body}{verifications}"));
            let (code, output) = fixture.run(&[]);
            assert_eq!(code, 2, "{output}");
            assert!(
                output.contains("invalid-assumption: Assumption invalid"),
                "{output}"
            );
            assert!(
                output.contains("related:") && output.contains("blocking dependency cycle"),
                "{output}"
            );
            assert!(
                output
                    .lines()
                    .any(|line| line.contains("note: Ground dependency cycle ")
                        && line.contains("p() -not-> p()")),
                "{output}"
            );
            if verifications.is_empty() {
                assert!(output.contains("No verification configured"));
            } else {
                assert!(output.contains("Not checked: selected assumption validation is invalid."));
                assert!(
                    output.contains("Verification ::good") && output.contains("Result: proved"),
                    "{output}"
                );
            }
            let (json_code, json) = fixture.run(&["--json"]);
            assert_eq!(json_code, code);
            assert!(
                json.contains("\"cycles\"") && json.contains("\"state\": \"invalid\""),
                "{json}"
            );
        }
    }
    #[test]
    fn region_diagnostics_print_ground_instances_and_preserve_exit_codes() {
        for (rules, code, kind) in [
            ("p(X):-eligible(X),!p(X);", 1, "no-meaning"),
            (
                "p(X):-eligible(X),!q(X); q(X):-eligible(X),!p(X);",
                2,
                "unsupported-region",
            ),
        ] {
            let fixture = Fixture::new(&format!(
                "sort S; const 'F2','F3':S; relation eligible(x:S); eligible('F2'); eligible('F3'); relation p(x:S); relation q(x:S); {rules} relation clear(); obligation o:empty(clear); verification v{{assumptions:[];obligations:[o];}}"
            ));
            let (exit, output) = fixture.run(&[]);
            assert_eq!(exit, code, "{output}");
            assert!(output.contains(kind));
            let notes = output
                .lines()
                .filter(|line| line.contains("note: Ground dependency cycle "))
                .collect::<Vec<_>>();
            for name in ["F2", "F3"] {
                assert!(
                    notes
                        .iter()
                        .any(|line| line.contains(&format!("p('{name}')"))
                            && line.contains(" -not-> ")),
                    "{output}"
                );
            }
            assert!(
                notes
                    .iter()
                    .all(|n| !(n.contains("F2") && n.contains("F3")))
            );
            assert_eq!(fixture.run(&["--json"]).0, exit);
        }
    }
    #[test]
    fn advisory_notices_print_locations_without_failing_obligations() {
        let f = Fixture::new(
            "input a(); relation no(); notice never:varies(no); notice always:varies(a,within:a); obligation o:empty(no); verification v{assumptions:[];obligations:[o];notices:[never,always];}",
        );
        let (code, text) = f.run(&[]);
        assert_eq!(code, 0, "{text}");
        assert!(
            text.contains("impossible-condition: Condition is impossible in this scope."),
            "{text}"
        );
        assert!(
            text.contains("always-true-condition: Condition is always true in this scope."),
            "{text}"
        );
        let (code, text) = f.run(&["--json"]);
        assert_eq!(code, 0);
        assert!(text.contains("condition-variability"));
        let f = Fixture::new(
            "relation yes(); yes(); notice n:varies(yes); obligation o:empty(yes); verification v{assumptions:[];obligations:[o];notices:[n];}",
        );
        assert_eq!(f.run(&[]).0, 1);
    }
    #[test]
    fn unknown_notice_diagnostics_do_not_change_exit_codes() {
        let unsupported = Fixture::new(
            "relation a(); relation b(); a():-!b(); b():-!a(); notice n:varies(a); verification v{assumptions:[];obligations:[];notices:[n];}",
        );
        let inconsistent = Fixture::new(
            "input a(); assumption yes:at_least_one(a,group_by:()); assumption no:empty(a); notice n:varies(a); verification v{assumptions:[yes,no];obligations:[];notices:[n];}",
        );
        for options in [&[][..], &["--json"][..]] {
            let (code, text) = unsupported.run(options);
            assert_eq!(code, 2);
            assert!(text.contains("unanalysed-condition") && text.contains("unsupported-region"));
            if options.is_empty() {
                assert!(text.contains("blocking dependency cycle"));
            }
            let (code, text) = inconsistent.run(options);
            assert_eq!(code, 1);
            assert!(!text.contains("unanalysed-condition"));
        }
        let f = Fixture::new(
            "input a(); relation no(); obligation o:empty(no); notice n:varies(a); verification v{assumptions:[];obligations:[o];notices:[n];}",
        );
        let mut found = false;
        for max_condition_nodes in 0..128 {
            let limits = Limits {
                max_condition_nodes,
                ..Limits::default()
            };
            let mut output = String::new();
            let args = [f.0.to_str().unwrap().to_owned()];
            let code = run_with_limits(args.clone(), &mut output, limits.clone()).unwrap();
            if !output.contains("unanalysed-condition") || !output.contains("Result: proved") {
                continue;
            }
            assert_eq!(code, 0, "{output}");
            assert!(output.contains("Result: proved"));
            output.clear();
            assert_eq!(
                run_with_limits(
                    args.into_iter().chain(["--json".into()]),
                    &mut output,
                    limits
                )
                .unwrap(),
                0
            );
            assert!(output.contains("unanalysed-condition"));
            found = true;
            break;
        }
        assert!(found);
    }
    #[test]
    fn notice_library_fallback_is_labeled_and_advisory() {
        let f = Fixture::new("");
        fs::create_dir(f.0.join("library")).unwrap();
        fs::write(f.0.join("library/den.root"), "{}").unwrap();
        fs::write(
            f.0.join("den.root"),
            r#"{"libraries":["library/den.root"]}"#,
        )
        .unwrap();
        fs::write(f.0.join("library/lib.den"),"relation no(); notice n:varies(no); verification v{assumptions:[];obligations:[];notices:[n];}").unwrap();
        let (code, text) = f.run(&[]);
        assert_eq!(code, 0, "{text}");
        assert!(text.contains("impossible-condition: in "), "{text}");
        assert!(!text.contains("consistency-only"), "{text}");
        fs::write(f.0.join("library/lib.den"), "relation a(); relation b(); a():-!b(); b():-!a(); notice n:varies(a); verification v{assumptions:[];obligations:[];notices:[n];}").unwrap();
        let (code, text) = f.run(&[]);
        assert_eq!(code, 2, "{text}");
        assert_eq!(text.matches("unanalysed-condition:").count(), 1, "{text}");
        assert!(text.contains("unanalysed-condition: in "), "{text}");
        assert!(text.contains("library/lib.den:1:"), "{text}");
        assert!(text.contains("blocking dependency cycle"), "{text}");
    }
    #[test]
    fn codes_distinguish_proofs_findings_incomplete_and_unconfigured() {
        for backend in [vec![], vec!["--json"]] {
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
        assert_eq!(output.matches("Result:").count(), 1);
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
                if code == 1 {
                    assert!(output.contains("coverage"));
                } else {
                    assert!(output.contains("Result: proved"));
                }
                if !body.contains("const") {
                    assert!(output.contains("empty-grouping-domain"));
                }
            }
        }
    }
    #[test]
    fn exactly_one_cli_reports_both_parts_and_requires_both_for_success() {
        for (facts, code, coverage, uniqueness) in [
            ("", 1, true, false),
            ("p(a);", 0, false, false),
            ("p(a); p(b);", 1, false, true),
            ("p(X) :- i(X);", 1, true, true),
        ] {
            let f = Fixture::new(&format!(
                "sort S; const a,b:S; input i(x:S); relation p(x:S); {facts} obligation one: exactly_one(p, group_by: ()); verification checks {{ assumptions: []; obligations: [one]; }}"
            ));
            let (actual, output) = f.run(&[]);
            assert_eq!(actual, code, "{output}");
            assert_eq!(f.run(&["--json"]).0, code);
            assert_eq!(output.contains("(coverage)"), coverage, "{output}");
            assert_eq!(output.contains("(uniqueness)"), uniqueness, "{output}");
        }
    }
    #[test]
    fn empty_cli_proof_presence_and_unresolved_worlds() {
        for (body, code, failure) in [
            ("relation p();", 0, false),
            ("relation p(); p();", 1, true),
            ("input p();", 1, true),
            ("relation p(); p() :- !p();", 2, false),
            (
                "sort S; const a,b:S; relation p(x:S); p(a); p(b) :- !p(b);",
                2,
                true,
            ),
        ] {
            let f = Fixture::new(&format!(
                "{body} obligation one: empty(p); verification checks {{ assumptions: []; obligations: [one]; }}"
            ));
            let (actual, output) = f.run(&[]);
            assert_eq!(actual, code, "{output}");
            assert_eq!(f.run(&["--json"]).0, code);
            assert_eq!(
                output.contains("relation is not empty"),
                failure,
                "{output}"
            );
        }
        let (code, _) =
            Fixture::new("relation p(); obligation one: empty(p, group_by: ());").run(&[]);
        assert_eq!(code, 2);
    }
    #[test]
    fn restricted_inputs_use_the_evaluated_domain_in_human_and_json_output() {
        for (facts, expected) in [("", 0), ("allowed(a);", 1)] {
            let f = Fixture::new(&format!(
                "sort S; const a,b:S; relation allowed(x:S); input i(x:S) within allowed; {facts} obligation vacant: empty(i); verification checks {{ assumptions:[]; obligations:[vacant]; }}"
            ));
            assert_eq!(f.run(&[]).0, expected);
            assert_eq!(f.run(&["--json"]).0, expected);
        }
        let (code, message) = Fixture::new(
            "input i(); relation allowed(); allowed() :- i(); input j() within allowed;",
        )
        .run(&[]);
        assert_eq!(code, 2);
        assert!(message.contains("domain provider depends on an input"));
    }
    #[test]
    fn general_assumption_consistency_is_a_finding_not_a_vacuous_proof() {
        for (kind, bad, good) in [
            ("empty", "r(x);", ""),
            ("at_most_one", "r(x);r(y);", "r(x);"),
            ("at_least_one", "", "r(x);"),
            ("exactly_one", "r(x);r(y);", "r(x);"),
        ] {
            for (facts, code) in [(bad, 1), (good, 0)] {
                let group = if kind == "empty" { "" } else { ",group_by:()" };
                let f = Fixture::new(&format!(
                    "sort S; const x,y:S; relation r(x:S); {facts} assumption a:{kind}(r{group}); relation q(); obligation o:empty(q); verification v{{assumptions:[a];obligations:[o];}}"
                ));
                let (actual, output) = f.run(&[]);
                assert_eq!(actual, code, "{output}");
                assert_eq!(
                    output.contains("inconsistent-assumptions"),
                    code == 1,
                    "{output}"
                );
                assert_eq!(f.run(&["--json"]).0, code);
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
    #[test]
    fn human_tuple_notes_use_den_name_spelling() {
        let f = Fixture::new(
            "sort S; namespace flags { const 'new-mode', 'F3':S; } relation 'bad-result'(x:S); 'bad-result'(flags::'new-mode'); 'bad-result'(flags::'F3'); obligation one: empty('bad-result'); verification checks { assumptions:[]; obligations:[one]; }",
        );
        let (code, output) = f.run(&[]);
        assert_eq!(code, 1, "{output}");
        for name in ["'new-mode'", "'F3'"] {
            assert!(
                output.contains(&format!(
                    "Replayed present tuple: 'bad-result'(flags::{name})."
                )),
                "{output}"
            );
        }
        assert_eq!(f.run(&["--json"]).0, code);
    }
    #[test]
    fn human_output_prints_presented_location_kind_notes_and_related_labels() {
        let f = Fixture::new(
            "relation p();\r\nrelation '😀'(); p();\r\nobligation one: empty(p);\r\nverification checks { assumptions: []; obligations: [one]; }",
        );
        let uri = filesystem::uri(&fs::canonicalize(f.0.join("program.den")).unwrap());
        let (code, output) = f.run(&[]);
        assert_eq!(code, 1, "{output}");
        assert!(
            output.contains(&format!("{uri}:2:17: counterexample: Obligation one:")),
            "{output}"
        );
        assert!(
            output.contains("  note: Replayed present tuple: p()."),
            "{output}"
        );
        assert!(
            output.contains(&format!("  related: {uri}:3:12: checked obligation")),
            "{output}"
        );
        assert!(output.contains("Verification ::checks"));
        assert!(output.contains("Result: findings"));
        assert!(!output.contains("Results:"));
        let (json_code, json_output) = f.run(&["--json"]);
        assert_eq!(json_code, code);
        let status: serde_json::Value =
            serde_json::from_str(json_output.split_once("Results: ").unwrap().1).unwrap();
        assert_eq!(status["state"], "findings");
        assert_eq!(
            status["emptiness"][0]["examples"][0]["tuple"]["arguments"],
            serde_json::json!([])
        );
        assert!(!json_output.contains("  note:"));
        assert_eq!(f.run(&["--json", "--json"]).0, 2);
    }

    #[test]
    fn library_fallback_keeps_the_presenters_program_label() {
        let f = Fixture::new("");
        fs::create_dir(f.0.join("library")).unwrap();
        fs::write(f.0.join("library/den.root"), "{}").unwrap();
        fs::write(
            f.0.join("den.root"),
            r#"{"libraries":["library/den.root"]}"#,
        )
        .unwrap();
        fs::write(
            f.0.join("library/lib.den"),
            "relation p();
p();
obligation one: empty(p);
verification checks { assumptions: []; obligations: [one]; }",
        )
        .unwrap();
        let library = filesystem::uri(&fs::canonicalize(f.0.join("library/lib.den")).unwrap());
        let root = filesystem::uri(&fs::canonicalize(f.0.join("den.root")).unwrap());
        let (code, output) = f.run(&[]);
        assert_eq!(code, 1, "{output}");
        assert!(
            output.contains(&format!(
                "{library}:2:1: counterexample: in {root}: Obligation one:"
            )),
            "{output}"
        );
        assert!(
            output.contains(&format!("related: {library}:3:12: checked obligation")),
            "{output}"
        );
        assert!(output.contains("note: Replayed present tuple: p()."));
        assert_eq!(f.run(&["--json"]).0, code);
    }

    #[test]
    fn hiding_library_rewrites_keeps_status_and_exit_codes() {
        let f = Fixture::new("relation own_rule(); own_rule():-flag(),!flag(),!own_rule();");
        fs::create_dir(f.0.join("library")).unwrap();
        fs::write(f.0.join("library/den.root"), "{}").unwrap();
        fs::write(
            f.0.join("den.root"),
            r#"{"libraries":["library/den.root"]}"#,
        )
        .unwrap();
        fs::write(f.0.join("library/lib.den"), "input flag(); relation library_rule(); library_rule():-flag(),!flag(),!library_rule(); relation clear(); obligation o:empty(clear); verification v{assumptions:[];obligations:[o];}").unwrap();
        let (code, full) = f.run(&[]);
        let (filtered_code, filtered) = f.run(&["--hide-library-rewrites"]);
        assert_eq!(filtered_code, code);
        assert_eq!(full.matches(": redundant:").count(), 2, "{full}");
        assert_eq!(filtered.matches(": redundant:").count(), 1, "{filtered}");
        assert!(
            filtered.contains("1 library rewrite findings hidden"),
            "{filtered}"
        );
        let status = |options: &[&str]| -> serde_json::Value {
            let (json_code, text) = f.run(options);
            assert_eq!(json_code, code);
            serde_json::from_str(text.split_once("Results: ").unwrap().1).unwrap()
        };
        let mut filtered = status(&["--json", "--hide-library-rewrites"]);
        assert_eq!(
            filtered
                .as_object_mut()
                .unwrap()
                .remove("hiddenLibraryRewrites"),
            Some(serde_json::json!(1))
        );
        assert_eq!(filtered, status(&["--json"]));
    }

    #[test]
    fn several_empty_tuples_are_located_in_numeric_source_order_under_each_verification() {
        let f = Fixture::new(&format!(
            "sort S;
const c,b,a:S;
relation p(x:S);
{}p(c);
p(b);
p(a);
obligation one: empty(p);
verification z {{ assumptions: []; obligations: [one]; }}
verification a {{ assumptions: []; obligations: [one]; }}",
            "\n".repeat(5)
        ));
        let uri = filesystem::uri(&fs::canonicalize(f.0.join("program.den")).unwrap());
        let (code, output) = f.run(&[]);
        assert_eq!(code, 1, "{output}");
        assert_eq!(output, f.run(&[]).1);
        let a = output.find("Verification ::a\n").unwrap();
        let z = output.find("Verification ::z\n").unwrap();
        assert!(a < z); // semantic name order, despite reverse declaration order
        for group in [&output[a..z], &output[z..]] {
            let headers = group
                .lines()
                .filter(|line| line.starts_with(&uri) && line.contains(": counterexample:"))
                .collect::<Vec<_>>();
            assert_eq!(headers.len(), 3, "{group}");
            for (header, line) in headers.iter().zip([9, 10, 11]) {
                assert!(header.starts_with(&format!("{uri}:{line}:1:")), "{header}");
            }
            for tuple in ["p(a)", "p(b)", "p(c)"] {
                assert!(
                    group.contains(&format!("note: Replayed present tuple: {tuple}.")),
                    "{group}"
                );
            }
            assert_eq!(group.matches("Result: findings").count(), 1);
        }
        assert_eq!(f.run(&["--json"]).0, code);
    }

    #[test]
    fn empty_example_option_changes_diagnostics_and_json_but_not_exit_codes() {
        let f = Fixture::new(
            "sort S; const a,b,c,d,e:S; relation p(x:S); p(a);p(b);p(c);p(d);p(e); obligation one:empty(p); verification checks{assumptions:[];obligations:[one];}",
        );
        for (options, n) in [
            (vec![], 3),
            (vec!["--empty-examples", "1"], 1),
            (vec!["--empty-examples", "all"], 5),
            (vec!["--empty-examples", "10"], 5),
        ] {
            let (code, text) = f.run(&options);
            assert_eq!(code, 1, "{text}");
            assert!(
                text.contains(&format!(
                    "5 distinct tuples can be present; showing {n} examples"
                )),
                "{text}"
            );
            let mut json_options = options;
            json_options.push("--json");
            let (code, text) = f.run(&json_options);
            assert_eq!(code, 1);
            let status: serde_json::Value =
                serde_json::from_str(text.split_once("Results: ").unwrap().1).unwrap();
            assert_eq!(
                status["emptiness"][0]["examples"].as_array().unwrap().len(),
                n
            );
            assert_eq!(status["emptiness"][0]["examplesTruncated"], n < 5);
        }
        for options in [
            vec!["--empty-examples"],
            vec!["--empty-examples", "0"],
            vec!["--empty-examples", "-1"],
            vec!["--empty-examples", "lots"],
            vec!["--empty-examples", "2", "--empty-examples", "all"],
        ] {
            assert_eq!(f.run(&options).0, 2);
        }
        let clean = Fixture::new(
            "relation p(); obligation one:empty(p); verification checks{assumptions:[];obligations:[one];}",
        );
        assert_eq!(clean.run(&["--empty-examples", "all"]).0, 0);
    }

    #[test]
    fn rendering_orders_presented_diagnostics_without_changing_their_contents() {
        let f = Fixture::new(
            "sort S; const a,b:S; relation p(x:S); relation q(x:S); p(a); p(b); q(X) :- p(X); obligation one: empty(q); verification checks { assumptions: []; obligations: [one]; }",
        );
        let (membership, sources) = filesystem::discover_classified(&f.0).unwrap();
        let p = load_with_resolver(
            &membership,
            &sources,
            Some(&mut filesystem::FileOriginResolver),
        )
        .unwrap();
        let limits = Limits::default();
        let operations = OperationalLimits::from(&limits);
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &operations).unwrap()
        else {
            panic!()
        };
        let admitted = prepared.admit(&operations).unwrap();
        let denotate_check::CheckOutcome::Complete(report) = admitted.verify(&operations).unwrap()
        else {
            panic!()
        };
        let mut presented = presentation::present(&p, &report).unwrap();
        let mut first = String::new();
        print_diagnostics(&p, &presented, &mut first, true).unwrap();
        for d in &presented.diagnostics {
            assert!(first.contains(&d.message));
            for note in &d.notes {
                assert!(first.contains(note));
            }
            for related in &d.related {
                assert!(first.contains(&related.label));
            }
        }
        presented.diagnostics.reverse();
        for d in &mut presented.diagnostics {
            d.notes.reverse();
            d.related.reverse();
        }
        let mut reordered = String::new();
        print_diagnostics(&p, &presented, &mut reordered, true).unwrap();
        assert_eq!(first, reordered);
    }
    #[test]
    fn concise_related_locations_are_cli_only_and_verbose_restores_the_full_list() {
        let f = Fixture::new(
            "relation p(); p(); obligation one: empty(p); verification checks { assumptions: []; obligations: [one]; }",
        );
        let (membership, sources) = filesystem::discover_classified(&f.0).unwrap();
        let p = load_with_resolver(&membership, &sources, None).unwrap();
        let snapshot = p.sources.snapshots().next().unwrap();
        let span = p.sources.span(snapshot.id, 0..1).unwrap();
        let obligation = p.corpus.obligations().next().unwrap().id;
        // Exercise exactly the presenter's label vocabulary, independently of
        // which proof/source locations any particular witness happens to choose.
        let labels = [
            "producing rule",
            "checked obligation",
            "upstream source origin",
            "contributing occurrence",
            "participating declaration",
            "supporting rewrite proof",
        ];
        let presented = presentation::Presentation {
            diagnostics: vec![denotate_presentation::Diagnostic {
                program: p.root.clone(),
                verification: None,
                identity: denotate_presentation::Identity::Emptiness(obligation),
                kind: denotate_presentation::Kind::Counterexample,
                message: "kept message".into(),
                notes: vec!["kept note".into()],
                primary: span,
                related: labels
                    .iter()
                    .map(|label| denotate_presentation::RelatedLocation::new(span, *label))
                    .collect(),
                fallback: false,
                evidence: serde_json::Value::Null,
            }],
            status: serde_json::Value::Null,
        };
        let mut concise = String::new();
        let mut verbose = String::new();
        print_diagnostics(&p, &presented, &mut concise, false).unwrap();
        print_diagnostics(&p, &presented, &mut verbose, true).unwrap();
        assert!(concise.contains("+3 more related locations (use --verbose)"));
        assert!(!verbose.contains("+3 more"));
        for (i, label) in labels.iter().enumerate() {
            assert_eq!(concise.contains(label), i < 3);
            assert!(verbose.contains(label));
        }
        for text in ["kept message", "kept note"] {
            assert!(concise.contains(text) && verbose.contains(text));
        }
        assert_eq!(presented.diagnostics[0].related.len(), labels.len());

        let (code, normal) = f.run(&[]);
        let (verbose_code, full) = f.run(&["--verbose"]);
        assert_eq!(code, verbose_code);
        assert!(normal.contains("more related locations"));
        assert!(full.contains("contributing occurrence"));
        assert!(!full.contains("more related locations"));
        assert_eq!(f.run(&["--json"]), f.run(&["--verbose", "--json"]));
        assert_eq!(f.run(&["--verbose", "--verbose"]).0, 2);
    }
}

#[cfg(test)]
#[path = "check/shipping_news.rs"]
mod shipping_news;
