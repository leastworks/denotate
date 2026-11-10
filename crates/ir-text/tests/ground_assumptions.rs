use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::AssumptionCone;
use denotate_ir_text::*;

const BODY: &str = "sort S; const a,b:S; input present(s:S); relation guarded(s:S); guarded(a); relation gives(s:S); gives(b); relation holds(s:S); holds(X):-present(X); holds(X):-guarded(X),!supplied(X); relation supplied(s:S); supplied(X):-gives(X),!holds(X); relation broken(); broken():-!holds(a); assumption not_broken:empty(broken);";
const VERIFY: &str = "verification checks { assumptions:[not_broken]; obligations:[]; }";

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///ground-assumptions.den", 1, text);
    load(
        &ProgramMembership::single("program", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn validate(p: &LoadedProgram, limits: &Limits) -> AssumptionValidation {
    validate_assumption_cones(&p.corpus, &p.domains, &p.keys, limits).unwrap()
}
fn state(v: &AssumptionValidation) -> &AssumptionValidity {
    v.assumptions.values().next().unwrap()
}

#[test]
fn relation_cycle_with_no_ground_cycle_is_valid_in_every_input_world() {
    let p = load_text(&format!("{BODY}{VERIFY}"));
    assert!(
        p.corpus
            .validate_assumptions()
            .unwrap()
            .values()
            .any(|c| *c == AssumptionCone::NeedsGrounding)
    );
    let limits = Limits::default();
    assert!(validate(&p, &limits).is_valid());
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request
        .prepare(&p.corpus, &p.keys, &OperationalLimits::from(&limits))
        .unwrap()
    else {
        panic!()
    };
    assert!(prepared.program().assumptions_consistent());
    let inputs = prepared
        .program()
        .input_atoms()
        .cloned()
        .collect::<Vec<_>>();
    for bits in 0..(1 << inputs.len()) {
        let replay = prepared
            .program()
            .evaluate(
                inputs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, a)| a.clone()),
                &limits,
            )
            .unwrap();
        assert!(replay.is_complete());
    }
}

#[test]
fn actual_ground_cycles_reject_selected_requests_with_located_cycle_evidence() {
    for body in [
        format!("{BODY} gives(a);"),
        BODY.replace("relation gives(s:S); gives(b);", "input gives(s:S);"),
    ] {
        let p = load_text(&format!("{body}{VERIFY}"));
        let limits = Limits::default();
        let validation = validate(&p, &limits);
        let AssumptionValidity::Invalid { cycles } = state(&validation) else {
            panic!("{validation:?}")
        };
        assert!(!cycles.is_empty());
        for cycle in cycles {
            assert!(cycle.0.iter().any(|e| e.negative));
            for (edge, next) in cycle.0.iter().zip(cycle.0.iter().cycle().skip(1)) {
                assert_eq!(edge.provider, next.consumer);
            }
        }
        let output = presentation::present_assumption_validation(&p, &validation).unwrap();
        assert_eq!(output.diagnostics.len(), 1);
        let diagnostic = &output.diagnostics[0];
        assert_eq!(diagnostic.kind.code(), "invalid-assumption");
        assert_eq!(p.sources.text(diagnostic.primary).unwrap(), "not_broken");
        assert!(
            diagnostic
                .related
                .iter()
                .any(|r| r.label == "blocking dependency cycle")
        );
        assert_eq!(
            diagnostic.data(&p.keys).unwrap()["finding"]["assumption"],
            serde_json::json!(["", "not_broken"])
        );
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        assert!(matches!(
            request.prepare(&p.corpus, &p.keys, &OperationalLimits::from(&limits)),
            Err(CheckError::InvalidAssumptionCone { .. })
        ));
    }
}

#[test]
fn a_cycle_at_an_unreachable_tuple_is_not_an_invalid_assumption() {
    let p = load_text(&format!(
        "{}{VERIFY}",
        BODY.replace("relation guarded(s:S); guarded(a);", "input guarded(s:S);")
    ));
    let limits = Limits::default();
    assert!(validate(&p, &limits).is_valid());
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    assert!(!report.results.value.inconsistent_assumptions);
    assert!(!report.results.value.regions.is_empty());
    assert!(
        report
            .results
            .value
            .regions
            .keys()
            .flat_map(|k| k.0.iter())
            .all(|a| a.arguments.iter().all(|c| c.name.contains('b')))
    );
}

fn edit_sequence(texts: &[String], valid: &[bool]) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let mut session = Session::with_grounding();
    for (text, expected) in texts.iter().zip(valid) {
        let p = load_text(text);
        let validation = validate(&p, &limits);
        assert_eq!(validation.is_valid(), *expected);
        let fresh = load_text(text);
        assert_eq!(validation, validate(&fresh, &limits));
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let warm = session.prepare(&request, &p.corpus, &p.keys, &ops);
        let cold = request.prepare(&p.corpus, &p.keys, &ops);
        if *expected {
            let (Ok(RequestPreparation::Complete(warm)), Ok(RequestPreparation::Complete(cold))) =
                (warm, cold)
            else {
                panic!("valid cone failed preparation")
            };
            let (warm, cold) = (warm.admit(&ops).unwrap(), cold.admit(&ops).unwrap());
            let (LocalCheckOutcome::Complete(warm), CheckOutcome::Complete(cold)) = (
                session.verify(&warm, &ops).unwrap(),
                cold.verify(&ops).unwrap(),
            ) else {
                panic!()
            };
            assert_eq!(warm.checked.results.value, cold.results.value);
        } else {
            let (Err(warm), Err(cold)) = (warm, cold) else {
                panic!("invalid cone accepted")
            };
            assert_eq!(warm, cold);
            assert!(matches!(warm, CheckError::InvalidAssumptionCone { .. }));
        }
    }
}

#[test]
fn fact_edits_revalidate_in_warm_sessions() {
    edit_sequence(
        &[
            format!("{BODY}{VERIFY}"),
            format!("{BODY} gives(a); {VERIFY}"),
            format!("{BODY}{VERIFY}"),
        ],
        &[true, false, true],
    );
}

#[test]
fn domains_and_input_eligibility_revalidate_in_warm_sessions() {
    let template = "sort S; const a:S; DOMAIN input i(s:S) WITHIN; ELIGIBLE relation r(s:S); r(X):-i(X),!r(X); assumption not_broken:empty(r);";
    let domain = |d: &str| {
        format!(
            "{}{VERIFY}",
            template
                .replace("DOMAIN", d)
                .replace("WITHIN", "")
                .replace("ELIGIBLE", "")
        )
    };
    edit_sequence(
        &[
            domain("domain S=[];"),
            domain("domain S=[a];"),
            domain("domain S=[];"),
        ],
        &[true, false, true],
    );
    let eligibility = |fact: &str| {
        format!(
            "{}{VERIFY}",
            template
                .replace("DOMAIN", "")
                .replace("WITHIN", "within eligible")
                .replace("ELIGIBLE", &format!("relation eligible(s:S); {fact}"))
        )
    };
    edit_sequence(
        &[
            eligibility(""),
            eligibility("eligible(a);"),
            eligibility(""),
        ],
        &[true, false, true],
    );
}

#[test]
fn unselected_declarations_are_validated_and_other_assumptions_cannot_hide_cycles() {
    let body = "input i(); relation r(); r():-i(),!r(); assumption invalid:empty(r); assumption exclude:empty(i);";
    for verification in [
        "",
        "verification v { assumptions:[]; obligations:[]; }",
        "verification v { assumptions:[exclude,invalid]; obligations:[]; }",
    ] {
        let p = load_text(&format!("{body}{verification}"));
        let validation = validate(&p, &Limits::default());
        assert!(
            validation
                .assumptions
                .iter()
                .any(|(k, s)| k.0.name.as_ref() == "invalid"
                    && matches!(s, AssumptionValidity::Invalid { .. }))
        );
        if !verification.is_empty() {
            let request = p
                .verification_requests(&Limits::default())
                .unwrap()
                .remove(0)
                .1;
            assert_eq!(
                validation
                    .selected_failure(&p.corpus, &p.keys, &request)
                    .unwrap()
                    .is_some(),
                verification.contains("exclude,invalid")
            );
        }
    }
}

#[test]
fn exhausted_validation_is_inconclusive_and_cancelled_work_is_not_a_result() {
    let p = load_text(&format!("{BODY}{VERIFY}"));
    let limits = Limits {
        max_atoms: 0,
        ..Limits::default()
    };
    let validation = validate(&p, &limits);
    assert!(matches!(
        state(&validation),
        AssumptionValidity::Inconclusive(_)
    ));
    let output = presentation::present_assumption_validation(&p, &validation).unwrap();
    assert_eq!(output.diagnostics[0].kind.code(), "unvalidated-assumption");
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(
        validation
            .selected_failure(&p.corpus, &p.keys, &request)
            .unwrap()
            .is_some()
    );
    assert!(matches!(
        request
            .prepare(&p.corpus, &p.keys, &OperationalLimits::from(&limits))
            .unwrap(),
        RequestPreparation::Inconclusive { .. }
    ));
    limits.cancellation.cancel();
    assert!(matches!(
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &limits),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn validation_does_not_simplify_negated_fixed_premises() {
    let p = load_text(
        "relation fixed(); fixed(); relation gate(); gate():-!fixed(); relation p(); relation q(); p():-gate(),!q(); q():-!p(); assumption a:empty(p);",
    );
    assert!(matches!(
        state(&validate(&p, &Limits::default())),
        AssumptionValidity::Invalid { .. }
    ));
}

#[test]
fn unnamed_api_restrictions_also_require_independent_ground_meaning() {
    let p = load_text(
        "input i(); relation r(); r():-i(),!r(); verification v { assumptions:[]; obligations:[]; }",
    );
    let limits = Limits::default();
    let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
    request.verification = None;
    let relation = p.corpus.relations().find(|r| r.name == "r").unwrap().id;
    request.constraints.push(InputConstraint::Cardinality {
        kind: denotate_ir::Cardinality::Empty,
        relation: p.keys.relation(relation).unwrap().clone(),
        group_by: vec![],
    });
    assert!(matches!(
        request.prepare(&p.corpus, &p.keys, &OperationalLimits::from(&limits)),
        Err(CheckError::InvalidAssumptionCone { .. })
    ));
}

#[test]
fn library_cycle_evidence_uses_labeled_fallback_and_current_source_locations() {
    use std::collections::{BTreeMap, BTreeSet};
    let text = "namespace lib { relation p(); p():-!p(); assumption invalid:empty(p); }";
    let build = |uri: &str, prefix: &str| {
        load(
            &ProgramMembership {
                root: "consumer".into(),
                roots: BTreeMap::from([
                    (
                        "consumer".into(),
                        RootInfo {
                            files: BTreeSet::from(["app.den".into()]),
                            libraries: BTreeSet::from(["lib".into()]),
                        },
                    ),
                    (
                        "lib".into(),
                        RootInfo {
                            files: BTreeSet::from([uri.into()]),
                            libraries: BTreeSet::new(),
                        },
                    ),
                ]),
            },
            &[
                SourceFile::new("app.den", 1, "// consumer"),
                SourceFile::new(uri, 1, format!("{prefix}{text}")),
            ],
        )
        .unwrap()
    };
    let before = build("lib.den", "");
    let validation = validate(&before, &Limits::default());
    let current = build("moved.den", "// moved\n\n");
    assert_eq!(validation, validate(&current, &Limits::default()));
    let output = presentation::present_assumption_validation(&current, &validation).unwrap();
    let d = &output.diagnostics[0];
    assert!(d.notes.iter().any(
        |n| n.starts_with("Ground dependency cycle ") && n.contains("lib::p() -not-> lib::p()")
    ));
    assert!(d.fallback && d.message.starts_with("in consumer:"));
    assert_eq!(
        current.sources.snapshot(d.primary.snapshot()).unwrap().uri,
        "moved.den"
    );
    assert_eq!(current.sources.text(d.primary).unwrap(), "invalid");
    assert!(d.primary.byte_range().start > "// moved\n\n".len());
    assert!(
        d.related
            .iter()
            .all(|r| current.sources.snapshot(r.span.snapshot()).unwrap().uri == "moved.den")
    );
}
