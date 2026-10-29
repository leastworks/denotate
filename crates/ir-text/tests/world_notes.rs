use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///world-notes.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn run(p: &LoadedProgram, session: &mut Session) -> (ScopedResults, presentation::Presentation) {
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = session
        .prepare(&request, &p.corpus, &p.keys, &operations)
        .unwrap()
    else {
        panic!()
    };
    let admitted = prepared.admit(&operations).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &operations).unwrap()
    else {
        panic!()
    };
    let output = presentation::present(p, &report.checked).unwrap();
    (report.checked.results.value, output)
}
fn input_names(
    p: &LoadedProgram,
    scope: &Option<Attribution<std::collections::BTreeSet<AtomKey>>>,
) -> Vec<String> {
    let Some(Attribution::Complete(inputs)) = scope else {
        panic!("{scope:?}")
    };
    let mut names = inputs
        .iter()
        .map(|atom| {
            p.corpus
                .relations()
                .find(|r| p.keys.relation(r.id).unwrap() == &atom.relation)
                .unwrap()
                .name
                .clone()
        })
        .collect::<Vec<_>>();
    names.sort();
    names
}
const VERIFY: &str = "verification checks { assumptions: []; obligations: [one]; }";

#[test]
fn uniqueness_notes_use_conflicting_tuple_cones_and_follow_warm_edits() {
    let mut session = Session::default();
    for absent in ["right", "other", "right"] {
        let p = load_text(&format!(
            "sort S; const a,b,c:S; input left(); input right(); input other();
             relation approved(); approved() :- {absent}();
             relation r(x:S); r(a) :- left(), !approved(); r(b) :- left(), !approved();
             r(c) :- right(), other(); obligation one: at_most_one(r, group_by: ()); {VERIFY}"
        ));
        let (warm, out) = run(&p, &mut session);
        let (cold, cold_out) = run(&p, &mut Session::default());
        assert_eq!(warm, cold);
        assert_eq!(
            out.diagnostics.iter().map(|d| &d.notes).collect::<Vec<_>>(),
            cold_out
                .diagnostics
                .iter()
                .map(|d| &d.notes)
                .collect::<Vec<_>>()
        );
        let ScopedResult::Counterexample(example, _) = warm.groups.values().next().unwrap() else {
            panic!()
        };
        assert_eq!(
            input_names(&p, &example.dependency_inputs),
            ["left", absent]
        );
        assert_eq!(
            example.candidate.present.len() + example.candidate.absent.len(),
            3
        );
        let irrelevant = if absent == "right" {
            "other()"
        } else {
            "right()"
        };
        for d in out
            .diagnostics
            .iter()
            .filter(|d| d.kind == denotate_presentation::Kind::Counterexample)
        {
            let note = d
                .notes
                .iter()
                .find(|n| n.contains("Inputs in dependency cone"))
                .unwrap();
            assert!(note.contains("present: left()"));
            assert!(note.contains(&format!("absent: {absent}()")));
            assert!(!note.contains(irrelevant));
            assert_eq!(
                d.evidence["observation"]["present"]
                    .as_array()
                    .unwrap()
                    .len()
                    + d.evidence["observation"]["absent"]
                        .as_array()
                        .unwrap()
                        .len(),
                3
            );
            assert_eq!(d.evidence["dependencyInputs"]["state"], "complete");
        }
    }
}

#[test]
fn coverage_notes_include_all_candidates_and_alternative_producers_in_the_missing_group() {
    let p = load_text(&format!(
        "sort G; const g,h:G; sort S; const a,b:S;
         input left(); input right(); input alternate(); input other(); input unrelated();
         relation approved(); approved() :- right();
         relation r(g:G,x:S); r(g,a) :- left(); r(g,a) :- alternate(); r(g,b) :- !approved();
         r(h,a) :- other(); obligation one: at_least_one(r, group_by: (g)); {VERIFY}"
    ));
    let mut session = Session::default();
    let (cold, out) = run(&p, &mut session);
    assert_eq!(cold, run(&p, &mut session).0);
    let coverage = cold.coverage.values().next().unwrap();
    assert!(coverage.complete());
    assert_eq!(coverage.missing, 2);
    let g = p
        .keys
        .constant(p.corpus.constants().find(|c| c.name == "g").unwrap().id)
        .unwrap();
    for example in &coverage.examples {
        let expected = if &example.group[0] == g {
            vec!["alternate", "left", "right"]
        } else {
            vec!["other"]
        };
        assert_eq!(input_names(&p, &example.dependency_inputs), expected);
        assert_eq!(
            example.observation.present.len() + example.observation.absent.len(),
            5
        );
    }
    let group_diagnostic = |name| {
        let d = out
            .diagnostics
            .iter()
            .find(|d| p.sources.text(d.primary).unwrap() == name)
            .unwrap();
        assert_eq!(d.notes.len(), 1);
        d
    };
    let g_diagnostic = group_diagnostic("g");
    let h_diagnostic = group_diagnostic("h");
    assert_eq!(g_diagnostic.identity, h_diagnostic.identity);
    assert_eq!(g_diagnostic.evidence, h_diagnostic.evidence);
    let g_note = &g_diagnostic.notes[0];
    assert!(g_note.starts_with("Missing group (g)"));
    assert!(
        g_note.contains("present: right(); absent: alternate(), left()"),
        "{g_note}"
    );
    assert!(!g_note.contains("other()") && !g_note.contains("unrelated()"));
    let h_note = &h_diagnostic.notes[0];
    assert!(h_note.starts_with("Missing group (h)"));
    assert!(h_note.contains("absent: other()"));
    assert!(!h_note.contains("left()") && !h_note.contains("right()"));
    for example in g_diagnostic.evidence["examples"].as_array().unwrap() {
        assert_eq!(
            example["observation"]["present"].as_array().unwrap().len()
                + example["observation"]["absent"].as_array().unwrap().len(),
            5
        );
    }
}

#[test]
fn no_input_cones_omit_world_notes_for_uniqueness_and_coverage() {
    for (contract, facts) in [
        ("at_most_one(r, group_by: ())", "r(a); r(b);"),
        ("at_least_one(r, group_by: ())", ""),
        ("exactly_one(r, group_by: ())", "r(a); r(b);"),
    ] {
        let p = load_text(&format!(
            "sort S; const a,b:S; input unrelated(); relation r(x:S); {facts}
             obligation one: {contract}; {VERIFY}"
        ));
        let (_, out) = run(&p, &mut Session::default());
        assert!(!out.diagnostics.is_empty());
        for d in &out.diagnostics {
            assert!(
                d.notes
                    .iter()
                    .all(|n| !n.contains("present:") && !n.contains("absent:"))
            );
        }
    }
}

#[test]
fn unavailable_display_scopes_keep_full_worlds_and_do_not_change_verdict_or_placement() {
    let p = load_text(&format!(
        "sort S; const a,b:S; input left(); input unrelated(); relation r(x:S);
         r(a) :- left(); r(b) :- left(); obligation one: exactly_one(r, group_by: ()); {VERIFY}"
    ));
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        request.prepare(&p.corpus, &p.keys, &operations).unwrap()
    else {
        panic!()
    };
    let admitted = prepared.admit(&operations).unwrap();
    let CheckOutcome::Complete(mut report) = admitted.verify(&operations).unwrap() else {
        panic!()
    };
    let original = presentation::present(&p, &report).unwrap();
    let cause = Inconclusive {
        phase: "dependency cones",
        resource: "work",
    };
    for group in &mut report.verification.groups {
        if let VerifiedOutcome::Counterexample(c) = &mut group.outcome {
            c.dependency_inputs = Some(Attribution::Incomplete(cause));
        }
    }
    for coverage in report.verification.coverage.values_mut() {
        for example in &mut coverage.examples {
            example.dependency_inputs = Some(Attribution::Incomplete(cause));
        }
    }
    let fallback = presentation::present(&p, &report).unwrap();
    assert_eq!(original.status, fallback.status);
    assert_eq!(
        original
            .diagnostics
            .iter()
            .map(|d| (&d.identity, d.primary, &d.related))
            .collect::<Vec<_>>(),
        fallback
            .diagnostics
            .iter()
            .map(|d| (&d.identity, d.primary, &d.related))
            .collect::<Vec<_>>()
    );
    for d in &fallback.diagnostics {
        let note = d
            .notes
            .iter()
            .find(|n| n.contains("Dependency-cone inputs unavailable"))
            .unwrap();
        assert!(note.contains("unrelated()"));
    }
}
