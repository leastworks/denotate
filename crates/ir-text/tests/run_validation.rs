use denotate_check::*;
use denotate_ir_text::*;

const BODY: &str = "sort S; const a,b:S; input present(s:S); relation guarded(s:S); guarded(a); relation gives(s:S); gives(b); relation holds(s:S); holds(X):-present(X); holds(X):-guarded(X),!supplied(X); relation supplied(s:S); supplied(X):-gives(X),!holds(X); relation broken(); broken():-!holds(a); assumption valid:empty(broken);";
fn parse(text: &str) -> LoadedProgram {
    let file = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

#[test]
fn shared_and_lazy_validation_agree_across_selections_and_with_original_preparation() {
    for text in [
        format!("{BODY} input i(); relation bad(); bad():-i(),!bad(); assumption invalid:empty(bad); obligation o:empty(broken); verification free{{assumptions:[];obligations:[o];}} verification a{{assumptions:[valid];obligations:[o];}} verification b{{assumptions:[invalid];obligations:[o];}} verification c{{assumptions:[valid];obligations:[o];}}"),
        "relation truth(); truth(); relation disabled(); disabled():-!truth(); relation a(); a():-disabled(),!b(); relation b(); b():-!a(); assumption invalid:empty(a); obligation o:empty(a); verification free{assumptions:[];obligations:[o];} verification selected{assumptions:[invalid];obligations:[o];}".into(),
    ] {
        let p = parse(&text);
        let limits = Limits::default();
        let ops = (&limits).into();
        let validated = validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
        for fixed in [FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap(), FixedPreparation::prepare_with_validation(&validated, &limits).unwrap()] {
            for (_, request) in p.verification_requests(&limits).unwrap() {
                let original = request.prepare(&p.corpus, &p.keys, &ops);
                let folded = request.prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None);
                match (original, folded) {
                    (Err(a), Err(b)) => assert_eq!(a,b),
                    (Ok(RequestPreparation::Complete(a)), Ok(RequestPreparation::Complete(b))) => {
                        let a = a.admit(&ops).unwrap(); let b = b.admit(&ops).unwrap();
                        let (CheckOutcome::Complete(a), CheckOutcome::Complete(b)) = (a.verify(&ops).unwrap(), b.verify(&ops).unwrap()) else { panic!("unexpected exhaustion") };
                        let a = presentation::present(&p, &a).unwrap();
                        let b = presentation::present(&p, &b).unwrap();
                        assert_eq!(a.status,b.status);
                        let locations = |shown: presentation::Presentation| shown.diagnostics.into_iter().map(|d| (d.kind,d.identity.data_in(&p.keys,d.verification.as_ref()).unwrap(), d.primary, d.related)).collect::<Vec<_>>();
                        assert_eq!(locations(a), locations(b));
                    }
                    _ => panic!("validation paths disagree"),
                }
            }
        }
    }
}

#[test]
fn a_declared_validation_does_not_omit_later_unnamed_restrictions() {
    let p = parse(&format!(
        "{BODY} input i(); relation bad(); bad():-i(),!bad(); verification v{{assumptions:[valid];obligations:[];}}"
    ));
    let limits = Limits::default();
    let ops = (&limits).into();
    let validated =
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
    assert!(validated.result().is_valid());
    for fixed in [
        FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap(),
        FixedPreparation::prepare_with_validation(&validated, &limits).unwrap(),
    ] {
        let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
        assert!(matches!(
            request
                .prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None)
                .unwrap(),
            RequestPreparation::Complete(_)
        ));
        request.verification = None;
        request.constraints = vec![InputConstraint::Cardinality {
            kind: denotate_ir::Cardinality::Empty,
            relation: p
                .keys
                .relation(p.corpus.relations().find(|r| r.name == "bad").unwrap().id)
                .unwrap()
                .clone(),
            group_by: vec![],
        }];
        let original = request.prepare(&p.corpus, &p.keys, &ops).err().unwrap();
        assert_eq!(
            request
                .prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None)
                .err()
                .unwrap(),
            original
        );
    }
}

#[test]
fn validation_exhaustion_is_explicit_and_recovery_does_not_reuse_it_across_runs() {
    let p = parse(
        "input i(); input j(); relation bad(); bad():-i(),!bad(); assumption a:empty(bad); assumption okay:at_most_one(j,group_by:()); verification v{assumptions:[a];obligations:[];}",
    );
    let limits = Limits {
        max_atoms: 1,
        ..Limits::default()
    };
    let validated =
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
    assert!(
        validated
            .result()
            .assumptions
            .iter()
            .any(|(k, v)| k.0.name.as_ref() == "okay" && matches!(v, AssumptionValidity::Valid))
    );
    for fixed in [
        FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap(),
        FixedPreparation::prepare_with_validation(&validated, &limits).unwrap(),
    ] {
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        for _ in 0..2 {
            let RequestPreparation::Inconclusive { reason, .. } = request
                .prepare_with_fixed(&p.corpus, &p.keys, &(&limits).into(), &fixed, None)
                .unwrap()
            else {
                panic!("exhausted validation must not be accepted")
            };
            assert_eq!(reason.phase, "assumption validation");
            assert_eq!(reason.resource, "atoms");
        }
    }
    let limits = Limits::default();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let cancelled = OperationalLimits::from(&limits);
    cancelled.cancellation.cancel();
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &cancelled, &fixed, None),
        Err(CheckError::Cancelled)
    ));
    let ops = OperationalLimits::from(&Limits::default());
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None),
        Err(CheckError::InvalidAssumptionCone { .. })
    ));
}

#[test]
fn reused_validation_is_bound_to_corpus_domains_keys_and_limits() {
    let text = format!("{BODY} const c:S; verification v{{assumptions:[valid];obligations:[];}}");
    let p = parse(&text);
    let other = parse(&text);
    let limits = Limits::default();
    let ops = (&limits).into();
    let validated =
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
    let fixed = FixedPreparation::prepare_with_validation(&validated, &limits).unwrap();
    let request = other.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request.prepare_with_fixed(&other.corpus, &other.keys, &ops, &fixed, None),
        Err(CheckError::InvalidRequest(_))
    ));
    let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
    let different_keys = denotate_ir::SemanticKeys::default();
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &different_keys, &ops, &fixed, None),
        Err(CheckError::Keys(_))
    ));
    let extra = p.corpus.constants().find(|c| c.name == "c").unwrap();
    request
        .domains
        .get_mut(p.keys.sort(extra.sort).unwrap())
        .unwrap()
        .retain(|c| c != p.keys.constant(extra.id).unwrap());
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None),
        Err(CheckError::InvalidRequest(_))
    ));
    let limits = Limits {
        max_atoms: limits.max_atoms + 1,
        ..limits
    };
    assert!(matches!(
        FixedPreparation::prepare_with_validation(&validated, &limits),
        Err(CheckError::InvalidRequest(_))
    ));
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None),
        Err(CheckError::InvalidRequest(_))
    ));
}

#[test]
fn run_preparation_is_shared_and_relation_stratified_validation_stays_lazy() {
    use std::sync::{Arc, Mutex};
    let p = parse("input i(); assumption a:empty(i);");
    validate_assumption_cones_using(&p.corpus, &p.domains, &p.keys, &Limits::default(), || {
        panic!("relation-stratified validation must not prepare fixed facts")
    })
    .unwrap();

    let p = parse(&format!(
        "{BODY} verification a{{assumptions:[valid];obligations:[];}} verification b{{assumptions:[];obligations:[];}}"
    ));
    let events = Arc::new(Mutex::new(Vec::new()));
    let seen = events.clone();
    let limits = Limits {
        profile: Profile::new(move |e| {
            if !e.finished {
                seen.lock().unwrap().push(e.stage);
            }
        }),
        ..Limits::default()
    };
    let mut session = denotate_check_session::Session::default();
    for _ in 0..2 {
        let validated =
            validate_assumption_cones_using(&p.corpus, &p.domains, &p.keys, &limits, || {
                session.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            })
            .unwrap();
        assert!(validated.result().is_valid());
        events.lock().unwrap().clear();
        let fixed = session
            .prepare_fixed_with_validation(&validated, &limits)
            .unwrap();
        for (_, request) in p.verification_requests(&limits).unwrap() {
            assert!(matches!(
                session
                    .prepare_with_fixed(&request, &p.corpus, &p.keys, &(&limits).into(), &fixed)
                    .unwrap(),
                RequestPreparation::Complete(_)
            ));
        }
        // A reuse contract, not a timing, work-receipt or witness golden.
        assert!(events.lock().unwrap().iter().all(|stage| !matches!(
            *stage,
            "fixed-evaluation" | "fixed-binding" | "residual-preparation" | "grounding"
        )));
    }
    assert!(session.fixed_stats().reused > 0);
}

#[test]
fn interruption_during_specialization_does_not_install_a_partial_preparation() {
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };
    let p = parse(&format!(
        "{BODY} verification v{{assumptions:[valid];obligations:[];}}"
    ));
    let cancel = Cancellation::default();
    let trigger = cancel.clone();
    let limits = Limits {
        cancellation: cancel,
        profile: Profile::new(move |e| {
            if e.stage == "assumption-specialization" && !e.finished {
                trigger.cancel();
            }
        }),
        ..Limits::default()
    };
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request.prepare_with_fixed(&p.corpus, &p.keys, &(&limits).into(), &fixed, None),
        Err(CheckError::Cancelled)
    ));
    let fresh = Limits::default();
    assert!(matches!(
        request
            .prepare_with_fixed(&p.corpus, &p.keys, &(&fresh).into(), &fixed, None)
            .unwrap(),
        RequestPreparation::Complete(_)
    ));

    let called = Arc::new(AtomicBool::new(false));
    let seen = called.clone();
    let timeout = Limits {
        timeout: std::time::Duration::ZERO,
        ..Limits::default()
    };
    let validated =
        validate_assumption_cones_using(&p.corpus, &p.domains, &p.keys, &timeout, || {
            seen.store(true, Ordering::Relaxed);
            FixedPreparation::prepare(&p.corpus, &p.domains, &timeout)
        })
        .unwrap();
    assert!(!validated.result().is_valid());
    assert!(!called.load(Ordering::Relaxed));
    // Operational limits do not enter the artifact's deterministic identity;
    // a later non-expired preparation must actually run and succeed.
    let fixed = FixedPreparation::prepare_with_validation(&validated, &fresh).unwrap();
    assert!(matches!(
        request
            .prepare_with_fixed(&p.corpus, &p.keys, &(&fresh).into(), &fixed, None)
            .unwrap(),
        RequestPreparation::Complete(_)
    ));
}

#[test]
fn fold_exhaustion_keeps_already_classified_declarations_valid() {
    let p = parse(
        "sort S; const a,b:S; relation fixed(s:S); fixed(a); fixed(b); input i(); assumption fast:empty(i); relation p(); p():-!p(); assumption ground:empty(p);",
    );
    let limits = Limits {
        max_atoms: 1,
        ..Limits::default()
    };
    let validated =
        validate_assumption_cones_for_run(&p.corpus, &p.domains, &p.keys, &limits).unwrap();
    for (key, validity) in &validated.result().assumptions {
        match key.0.name.as_ref() {
            "fast" => assert!(matches!(validity, AssumptionValidity::Valid)),
            "ground" => assert!(
                matches!(validity, AssumptionValidity::Inconclusive(reason) if reason.phase == "assumption validation")
            ),
            _ => unreachable!(),
        }
    }
}
