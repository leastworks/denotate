use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::*;
use denotate_ir_text::*;
use denotate_presentation::Identity;
use std::collections::BTreeMap;
mod support;

fn single(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn run(
    p: &LoadedProgram,
    session: &mut Session,
) -> Vec<(ScopedResults, presentation::Presentation)> {
    let limits = Limits::default();
    let ops = (&limits).into();
    p.verification_requests(&limits)
        .unwrap()
        .into_iter()
        .map(|(_, request)| {
            let RequestPreparation::Complete(prepared) =
                session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap()
            else {
                panic!()
            };
            let CheckOutcome::Complete(global) = prepared.verify(&ops).unwrap() else {
                panic!()
            };
            assert_eq!(
                report.checked.results.value.notices,
                global.results.value.notices
            );
            let out = presentation::present(p, &report.checked).unwrap();
            (report.checked.results.value, out)
        })
        .collect()
}
fn states(results: &ScopedResults) -> BTreeMap<String, NoticeState> {
    results
        .notices
        .iter()
        .map(|(k, v)| (k.0.name.to_string(), v.state.clone()))
        .collect()
}
const VERIFY: &str = "verification v { assumptions: []; obligations: []; notices: [n]; }";

#[test]
fn truth_table_matches_exhaustive_worlds_and_witnesses_replay() {
    // Every Boolean function of two inputs, checked in every Boolean parent.
    // This is a truth-table oracle, independent of symbolic query construction.
    for g in 0..16u8 {
        for p in 0..16u8 {
            let rules = |name: &str, mask: u8| {
                (0..4)
                    .filter(|w| mask & (1 << w) != 0)
                    .map(|w| {
                        format!(
                            "{name}() :- {}a(), {}b();",
                            if w & 1 == 0 { "!" } else { "" },
                            if w & 2 == 0 { "!" } else { "" }
                        )
                    })
                    .collect::<String>()
            };
            let text = format!(
                "input a(); input b(); relation g(); relation p(); {} {} notice n: varies(g, within: p); {VERIFY}",
                rules("g", g),
                rules("p", p)
            );
            let program = single(&text);
            let results = run(&program, &mut Session::default()).remove(0).0;
            let result = results.notices.values().next().unwrap();
            let yes = p & g != 0;
            let no = p & !g != 0;
            assert_eq!(
                result.state,
                match (yes, no) {
                    (false, false) => NoticeState::ParentUnreachable,
                    (true, true) => NoticeState::Varying,
                    (true, false) => NoticeState::AlwaysTrue,
                    (false, true) => NoticeState::Impossible,
                }
            );
            for (example, expected) in [(&result.when_true, true), (&result.when_false, false)] {
                if let Some(example) = example {
                    let bit =
                        |name| {
                            example.observation.present.iter().any(|a| {
                                a.relation == RelationKey::Named(QualifiedKey::new("", name))
                            })
                        };
                    let world = usize::from(bit("a")) | (usize::from(bit("b")) << 1);
                    assert_ne!(p & (1 << world), 0);
                    assert_eq!(g & (1 << world) != 0, expected);
                    assert_eq!(
                        example.observation.present.len() + example.observation.absent.len(),
                        2
                    );
                }
            }
        }
    }
}

#[test]
fn lexical_context_is_explicit_and_findings_are_use_and_verification_specific() {
    let p = single(
        "input a(); input b(); relation parent(); parent() :- a(), b(); notice outer: varies(a); notice inner: varies(a, within: parent); verification first { assumptions: []; obligations: []; notices: [outer, inner]; } verification second { assumptions: []; obligations: []; notices: [inner]; }",
    );
    let results = run(&p, &mut Session::default());
    assert_eq!(
        states(&results[0].0),
        BTreeMap::from([
            ("outer".into(), NoticeState::Varying),
            ("inner".into(), NoticeState::AlwaysTrue)
        ])
    );
    let diagnostics: Vec<_> = results
        .iter()
        .flat_map(|(_, p)| p.diagnostics.iter())
        .filter(|d| matches!(d.identity, Identity::Notice(_)))
        .collect();
    assert_eq!(diagnostics.len(), 2);
    assert_ne!(
        diagnostics[0].data(&p.keys).unwrap()["finding"],
        diagnostics[1].data(&p.keys).unwrap()["finding"]
    );
    for d in diagnostics {
        assert_eq!(p.sources.text(d.primary).unwrap(), "inner");
        assert!(
            d.related
                .iter()
                .any(|r| p.sources.text(r.span).unwrap() == "parent")
        );
        assert_eq!(d.data(&p.keys).unwrap()["evidence"]["state"], "always-true");
    }
}

#[test]
fn assumptions_selection_and_inconsistent_context_never_make_vacuous_notices() {
    let p = single(
        "input a(); assumption yes: at_least_one(a, group_by: ()); assumption no: empty(a); notice n: varies(a); verification free { assumptions: []; obligations: []; notices: [n]; } verification yes { assumptions: [yes]; obligations: []; notices: [n]; } verification no { assumptions: [no]; obligations: []; notices: [n]; } verification inconsistent { assumptions: [yes,no]; obligations: []; notices: [n]; }",
    );
    for (result, out) in run(&p, &mut Session::default()) {
        match result
            .context
            .verification
            .as_ref()
            .unwrap()
            .0
            .name
            .as_ref()
        {
            "free" => assert_eq!(states(&result)["n"], NoticeState::Varying),
            "yes" => assert_eq!(states(&result)["n"], NoticeState::AlwaysTrue),
            "no" => assert_eq!(states(&result)["n"], NoticeState::Impossible),
            "inconsistent" => {
                assert!(result.inconsistent_assumptions);
                assert_eq!(out.status["notices"][0]["result"]["state"], "unknown");
                assert!(
                    !out.diagnostics
                        .iter()
                        .any(|d| matches!(d.identity, Identity::Notice(_)))
                );
            }
            _ => panic!(),
        }
    }
}

#[test]
fn recursive_unsupported_conditions_are_unknown_but_unreachable_parents_suppress_children() {
    let p = single(
        "relation a(); relation b(); a() :- !b(); b() :- !a(); relation never(); notice n: varies(a); notice child: varies(a, within: never); verification v { assumptions: []; obligations: []; notices: [n,child]; }",
    );
    let (result, out) = run(&p, &mut Session::default()).remove(0);
    assert_eq!(
        states(&result)["n"],
        NoticeState::Unknown(NoticeUnknown::Unsupported)
    );
    assert_eq!(states(&result)["child"], NoticeState::ParentUnreachable);
    assert!(
        !out.diagnostics
            .iter()
            .any(|d| matches!(d.identity, Identity::Notice(_)))
    );
}

#[test]
fn positive_recursion_and_observer_boundaries_keep_existing_meaning() {
    let p = single(&format!(
        "relation t(); t() :- t(); relation guard(); guard() :- !t(); notice n: varies(guard); {VERIFY}"
    ));
    let (result, _) = run(&p, &mut Session::default()).remove(0);
    assert_eq!(states(&result)["n"], NoticeState::AlwaysTrue);
}

#[test]
fn notice_queries_are_bounded_cancelable_and_do_not_change_obligation_verdicts() {
    let p = single(
        "input a(); relation no(); obligation o:empty(no); notice n:varies(a); verification with_notice { assumptions:[]; obligations:[o]; notices:[n]; } verification without { assumptions:[]; obligations:[o]; }",
    );
    let results = run(&p, &mut Session::default());
    assert_eq!(results[0].0.emptiness, results[1].0.emptiness);
    assert_eq!(results[0].1.status["state"], results[1].1.status["state"]);
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request
        .prepare(&p.corpus, &p.keys, &(&limits).into())
        .unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&(&limits).into()).unwrap();
    let relation = p.corpus.notices().next().unwrap().condition;
    let low = Limits {
        max_work: 0,
        ..Limits::default()
    };
    assert!(matches!(
        prepared
            .program()
            .analyze_condition(relation, None, &low)
            .unwrap()
            .state,
        NoticeState::Unknown(NoticeUnknown::Inconclusive(_))
    ));
    let low = Limits {
        max_condition_nodes: 0,
        ..Limits::default()
    };
    assert!(matches!(
        prepared
            .program()
            .analyze_condition(relation, None, &low)
            .unwrap()
            .state,
        NoticeState::Unknown(NoticeUnknown::Inconclusive(_))
    ));
    let cancel = Limits::default();
    cancel.cancellation.cancel();
    assert!(matches!(
        prepared
            .program()
            .analyze_condition(relation, None, &cancel),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn warm_edits_selection_parent_facts_and_current_locations_match_cold() {
    let mut session = Session::default();
    for (i, (fact, parent, selection)) in [
        ("", "b", "n"),
        ("b();", "b", "n"),
        ("a(); b();", "b", "n"),
        ("", "a", "n"),
        ("", "a", ""),
        ("", "b", "n"),
    ]
    .into_iter()
    .enumerate()
    {
        let p = single(&format!(
            "{}relation a(); relation b(); {fact} notice n: varies(a, within: {parent}); verification v {{ assumptions: []; obligations: []; notices: [{selection}]; }}",
            "\n".repeat(i)
        ));
        let warm = run(&p, &mut session).remove(0);
        let cold = run(&p, &mut Session::default()).remove(0);
        assert_eq!(warm.0, cold.0);
        assert_eq!(warm.1.status, cold.1.status);
        let locations = |out: &presentation::Presentation| {
            out.diagnostics
                .iter()
                .map(|d| (d.primary, d.message.clone(), d.data(&p.keys).unwrap()))
                .collect::<Vec<_>>()
        };
        assert_eq!(locations(&warm.1), locations(&cold.1));
    }
}

#[test]
fn declaration_and_reference_validation_and_no_implicit_selection() {
    let base = "sort S; relation p(x:S); relation zero(); assumption a:empty(zero); obligation o:empty(zero); notice n:varies(zero);";
    for bad in [
        "notice bad:varies(p);",
        "notice bad:varies(zero,within:p);",
        "notice bad:varies(missing);",
        "notice bad:varies(o);",
        "notice n:varies(zero);",
        "verification v{assumptions:[];obligations:[];notices:[o];}",
        "verification v{assumptions:[];obligations:[];notices:[missing];}",
        "verification v{assumptions:[];obligations:[];notices:[n,::n];}",
        "verification v{assumptions:[n];obligations:[];}",
    ] {
        let s = SourceFile::new("x", 1, format!("{base}{bad}"));
        assert!(
            load(&ProgramMembership::single("r", [s.uri.clone()]), &[s]).is_err(),
            "{bad}"
        );
    }
    assert!(
        single(base)
            .verification_requests(&Limits::default())
            .unwrap()
            .is_empty()
    );
    let p = single(&format!(
        "{base} verification v{{assumptions:[];obligations:[o];}}"
    ));
    let (r, _) = run(&p, &mut Session::default()).remove(0);
    assert!(r.notices.is_empty());
}

#[test]
fn notice_round_trip_preserves_selection_relations_and_origins() {
    let p = single(
        "namespace 'a::b' { input i(); relation p(); p() :- i(); notice 'inner use': varies(i, within: p) message \"When here\"; notice top:varies(p); verification v { assumptions: []; obligations: []; notices: ['inner use', top]; } }",
    );
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
    };
    let export = ExportProgram {
        corpus: &p.corpus,
        domains: &p.domains,
        sources: &p.sources,
        provenance: &p.provenance,
        layout: &layout,
    };
    for embedded_origins in [false, true] {
        let bundle = print(&export, PrintOptions { embedded_origins }).unwrap();
        let (membership, docs) = bundle.documents("file:///export");
        let q = load_with_resolver(&membership, &docs, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &q, "file:///export", embedded_origins);
        assert_eq!(
            states(&run(&p, &mut Session::default())[0].0),
            states(&run(&q, &mut Session::default())[0].0)
        );
    }
}

#[test]
fn assumption_edits_change_admission_and_notice_queries_without_assuming_the_conclusion() {
    let body = "sort S; const a,b:S; input i(x:S); relation p(); relation q(); p():-i(a),!q(); q():-i(b),!p(); assumption unique:at_most_one(i,group_by:()); notice n:varies(p);";
    let mut session = Session::default();
    for (selection, expected) in [
        ("unique", NoticeState::Varying),
        ("", NoticeState::Unknown(NoticeUnknown::Unsupported)),
        ("unique", NoticeState::Varying),
    ] {
        let p = single(&format!(
            "{body} verification v{{assumptions:[{selection}];obligations:[];notices:[n];}}"
        ));
        let warm = run(&p, &mut session).remove(0);
        let cold = run(&p, &mut Session::default()).remove(0);
        assert_eq!(warm.0, cold.0);
        assert_eq!(states(&warm.0)["n"], expected);
    }
}
