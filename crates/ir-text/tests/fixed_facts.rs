use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;

fn parse(text: &str) -> LoadedProgram {
    let file = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}
fn compare(text: &str) {
    let p = parse(text);
    let limits = Limits::default();
    let operations = (&limits).into();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let mut session = Session::default();
    let cached = session
        .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
        .unwrap();
    for (_, request) in p.verification_requests(&limits).unwrap() {
        let RequestPreparation::Complete(raw) =
            request.prepare(&p.corpus, &p.keys, &operations).unwrap()
        else {
            panic!()
        };
        let raw = raw.admit(&operations).unwrap();
        let CheckOutcome::Complete(raw_report) = raw.verify(&operations).unwrap() else {
            panic!()
        };
        let raw_presentation = presentation::present(&p, &raw_report).unwrap();
        for fixed in [&fixed, &cached, &cached] {
            let RequestPreparation::Complete(folded) = request
                .prepare_with_fixed(&p.corpus, &p.keys, &operations, fixed, None)
                .unwrap()
            else {
                panic!()
            };
            let folded = folded.admit(&operations).unwrap();
            let CheckOutcome::Complete(report) = folded.verify(&operations).unwrap() else {
                panic!()
            };
            let shown = presentation::present(&p, &report).unwrap();
            assert_eq!(shown.status, raw_presentation.status, "{text}");
            let diagnostics = |shown: &presentation::Presentation| {
                shown
                    .diagnostics
                    .iter()
                    .map(|d| {
                        (
                            d.kind,
                            d.identity
                                .data_in(&p.keys, d.verification.as_ref())
                                .unwrap(),
                            d.message.clone(),
                            d.primary.clone(),
                            d.related.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(
                diagnostics(&shown),
                diagnostics(&raw_presentation),
                "{text}"
            );
            let LocalCheckOutcome::Complete(warm) = session.verify(&folded, &operations).unwrap()
            else {
                panic!()
            };
            assert_eq!(
                denotate_presentation::summary(&warm.checked.results.value),
                denotate_presentation::summary(&report.results.value),
                "{text}"
            );
        }
    }
}

#[test]
fn fixed_presence_absence_recursion_and_input_negation_keep_results() {
    for source in [
        "relation t(); t(); relation f(); f() :- !t(); relation r(); r() :- !f();",
        "relation t(); t(); relation r(); relation s(); r() :- t(); s() :- r(); r() :- s();",
        "input i(); relation r(); r() :- !i();",
        "relation t(); t(); relation f(); f() :- !t(); relation r(); r() :- f(), !s(); relation s(); s() :- !r();",
        "relation t(); t(); relation r(); r() :- !r();",
    ] {
        compare(&format!(
            "{source} obligation o:empty(r); notice n:varies(r); verification v{{assumptions:[];obligations:[o];notices:[n];}}"
        ));
    }
}

#[test]
fn fixed_general_assumptions_and_all_obligation_kinds_keep_meaning() {
    compare(
        "sort S; const a,b:S; relation t(s:S); t(a); relation f(s:S); f(X):-t(X), !t(X); input i(s:S) within t; relation r(s:S); r(X):-i(X); r(b):-!i(a); assumption nonempty:at_least_one(t,group_by:()); assumption absent:empty(f); obligation one:exactly_one(r,group_by:()); obligation all:at_least_one(t,group_by:s); obligation none:empty(f); verification v{assumptions:[nonempty,absent];obligations:[one,all,none];}",
    );
    compare(
        "relation r(); r(); assumption a:empty(r); obligation o:empty(r); verification v{assumptions:[a];obligations:[o];}",
    );
}

#[test]
fn selected_assumption_validation_uses_fixed_truth_and_keeps_original_evidence() {
    let p = parse(
        "relation t(); t(); relation f(); f():-!t(); relation a(); a():-f(),!b(); relation b(); b():-!a(); assumption no_a:empty(a); verification v{assumptions:[no_a];obligations:[];}",
    );
    let limits = Limits::default();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &(&limits).into(), &fixed, None),
        Ok(RequestPreparation::Complete(_))
    ));
    assert!(
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &limits)
            .unwrap()
            .is_valid()
    );
    compare(
        "relation t(); t(); relation f(); f():-!t(); relation a(); a():-f(),!b(); relation b(); b():-!a(); assumption no_a:empty(a); obligation o:empty(a); verification v{assumptions:[no_a];obligations:[o];}",
    );
}

#[test]
fn warm_edits_change_fixed_membership_and_keep_current_evidence() {
    let mut session = Session::default();
    let limits = Limits::default();
    for declaration in [
        "relation a(); a();",
        "sort S; const x,y:S; domain S=[x]; relation allowed(s:S); allowed(x); input selected(s:S) within allowed; relation a(); a():-selected(x);",
        "sort S; const x,y:S; domain S=[x,y]; relation allowed(s:S); allowed(x); allowed(y); input selected(s:S) within allowed; relation a(); a():-selected(X);",
        "sort S; const x,y:S; domain S=[x]; relation allowed(s:S); input selected(s:S) within allowed; relation a(); a():-selected(x);",
        "sort S; const x,y:S; domain S=[x]; relation allowed(s:S); allowed(x); input selected(s:S) within allowed; relation a(); a():-selected(x);",
        "input a();",
        "relation a();",
        "relation a(); a();",
    ] {
        let p = parse(&format!(
            "{declaration} relation r(); r():-a(); obligation o:empty(r); verification v{{assumptions:[];obligations:[o];}}"
        ));
        let fixed = session
            .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            .unwrap();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let operations = (&limits).into();
        let RequestPreparation::Complete(warm) = session
            .prepare_with_fixed(&request, &p.corpus, &p.keys, &operations, &fixed)
            .unwrap()
        else {
            panic!()
        };
        let warm = warm.admit(&operations).unwrap();
        let LocalCheckOutcome::Complete(report) = session.verify(&warm, &operations).unwrap()
        else {
            panic!()
        };
        let RequestPreparation::Complete(raw) =
            request.prepare(&p.corpus, &p.keys, &operations).unwrap()
        else {
            panic!()
        };
        let raw = raw.admit(&operations).unwrap();
        let CheckOutcome::Complete(control) = raw.verify(&operations).unwrap() else {
            panic!()
        };
        assert_eq!(
            presentation::present(&p, &report.checked).unwrap().status,
            presentation::present(&p, &control).unwrap().status
        );
        let locations = |report: &CheckedReport| {
            presentation::present(&p, report)
                .unwrap()
                .diagnostics
                .into_iter()
                .map(|d| {
                    (
                        d.identity
                            .data_in(&p.keys, d.verification.as_ref())
                            .unwrap(),
                        d.primary,
                        d.related,
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(locations(&report.checked), locations(&control));
    }
}

#[test]
fn folded_absence_retains_completed_provider_and_replayed_original_rule() {
    let p = parse(
        "relation t(); t(); relation f(); f():-!t(); input i(); relation r(); r():-i(),!f(); obligation o:empty(r); verification v{assumptions:[];obligations:[o];}",
    );
    let limits = Limits::default();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request
        .prepare_with_fixed(&p.corpus, &p.keys, &(&limits).into(), &fixed, None)
        .unwrap()
    else {
        panic!()
    };
    let atom = |name| {
        GroundAtom::new(
            p.corpus.relations().find(|r| r.name == name).unwrap().id,
            [],
        )
    };
    let replay = prepared.program().evaluate([atom("i")], &limits).unwrap();
    let provider = replay.absence_provider(&atom("f")).unwrap().unwrap();
    assert!(matches!(provider, CompletedProvider::Component(_)));
    let Evidence::Derived { rule, premises } = &replay.derivation(&atom("r")).unwrap().evidence
    else {
        panic!()
    };
    assert_eq!(
        prepared.program().original_rule(*rule).unwrap().body.len(),
        2
    );
    assert!(premises.iter().any(|p| matches!(p, PremiseEvidence::Absent { fact, provider: p, .. } if *fact == atom("f") && *p == provider)));
}

#[test]
fn folding_can_finish_when_symbolic_fixed_storage_previously_exhausted() {
    let facts = (0..30)
        .map(|i| format!("relation fact_{i}(); fact_{i}();"))
        .collect::<String>();
    let p = parse(&format!(
        "{facts} input i(); relation r(); r():-i(),!i(); obligation o:empty(r); verification v{{assumptions:[];obligations:[o];}}"
    ));
    let limits = Limits {
        max_condition_nodes: 12,
        ..Limits::default()
    };
    let operations = (&limits).into();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(folded) = request
        .prepare_with_fixed(&p.corpus, &p.keys, &operations, &fixed, None)
        .unwrap()
    else {
        panic!()
    };
    let folded = folded.admit(&operations).unwrap();
    let CheckOutcome::Complete(report) = folded.verify(&operations).unwrap() else {
        panic!()
    };
    assert_eq!(
        denotate_presentation::summary(&report.results.value)["state"],
        "proved"
    );
    let RequestPreparation::Complete(raw) =
        request.prepare(&p.corpus, &p.keys, &operations).unwrap()
    else {
        panic!()
    };
    let raw = raw.admit(&operations).unwrap();
    let CheckOutcome::Complete(report) = raw.verify(&operations).unwrap() else {
        panic!()
    };
    assert_ne!(
        denotate_presentation::summary(&report.results.value)["state"],
        "proved"
    );
}
