//! Request ownership, semantic outcomes, and preparation equivalence.
use super::*;

pub(super) fn request(p: &LoweredProgram, limits: &Limits) -> CheckRequest {
    p.request(limits).unwrap()
}
pub(super) fn checked<'s>(p: &'s LoweredProgram, limits: &Limits) -> PreparedCheck<'s> {
    let RequestPreparation::Complete(g) = request(p, limits)
        .prepare(&p.corpus, &p.keys, &limits.into())
        .unwrap()
    else {
        panic!("unexpected preparation exhaustion")
    };
    g.admit(&limits.into()).unwrap()
}
pub(super) fn fresh_capture(p: &LoweredProgram, max_work: usize) -> Value {
    let limits = Limits {
        max_work,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let req = request(p, &limits);
    let exhausted =
        |c: Inconclusive| json!({"status":"inconclusive","phase":c.phase,"resource":c.resource});
    let g = match req.prepare(&p.corpus, &p.keys, &(&limits).into()).unwrap() {
        RequestPreparation::Complete(g) => g,
        RequestPreparation::Inconclusive { reason, .. } => return exhausted(reason),
    };
    let g = g.admit(&(&limits).into()).unwrap();
    match g.verify(&(&limits).into()).unwrap() {
        CheckOutcome::Complete(r) => {
            assert_eq!(r.results.value.context, req);
            for group in &r.verification.groups {
                if let VerifiedOutcome::Counterexample(c) = &group.outcome {
                    assert!(c.tuples.len() >= 2);
                    assert!(!c.evidence.is_empty());
                }
            }
            captured_report(&r.verification, &Names { keys: &p.keys })
        }
        CheckOutcome::Inconclusive { reason, .. } => exhausted(reason),
    }
}

#[test]
fn request_and_raw_execution_preserve_semantic_outcomes() {
    for row in regression_cases() {
        let source = row["source"].as_str().unwrap();
        let (_, _, p) = lower(source);
        for report in [
            budget_result_lowered(&p, Limits::default().max_work),
            fresh_capture(&p, Limits::default().max_work),
        ] {
            assert_eq!(semantic_outcomes(report), row["expected"], "{source}");
        }
    }
}

#[test]
fn request_context_and_scoped_results_are_owned_and_distinguish_reasons() {
    let source = "input z, a, m; slot s, empty, cycle, dependent; s <- z; s <- a; cycle <- m when not available(cycle); dependent <- z when available(cycle); dependent <- a;";
    let (_, _, p) = lower(source);
    let limits = Limits::default();
    let g = checked(&p, &limits);
    let CheckOutcome::Complete(r) = g.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    assert!(
        r.results
            .value
            .groups
            .values()
            .any(|r| matches!(r, ScopedResult::Counterexample(..)))
    );
    assert!(r.results.value.groups.values().any(|r|matches!(r,ScopedResult::Unsupported(UnsupportedReason::DependsOnUnsettled(d)) if !d.is_empty())));
    assert!(r.results.value.regions.values().any(|r| matches!(
        r.outcome,
        ScopedResult::Unsupported(UnsupportedReason::UnsettledNegativeCycle)
    ) && matches!(
        r.completion,
        RegionCompletion::NoMeaning { .. }
    )));
    let (obligation, domain) = r.results.value.group_domains.first_key_value().unwrap();
    let empty = domain.domains[0]
        .iter()
        .find(|v| v.name.as_ref() == "empty")
        .unwrap();
    assert_eq!(
        r.results
            .value
            .group(&domain.key(obligation, vec![empty.clone()]).unwrap()),
        Some(ScopedResult::Proved)
    );
    let (_, _, q) = lower(&format!("// moved\n{source}"));
    let next = checked(&q, &limits);
    let CheckOutcome::Complete(s) = next.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    assert_eq!(
        r.results, s.results,
        "no arena IDs or source spans in neutral equality"
    );
    for change in 0..6 {
        let mut altered = r.results.clone();
        match change {
            0 => altered.value.context.constraints.clear(),
            1 => altered.value.context.obligations.clear(),
            2 => altered.value.context.domains.clear(),
            3 => altered.value.context.backend.configuration.push('!'),
            4 => altered.value.context.limits.max_work += 1,
            _ => {
                altered.value.groups.insert(
                    altered.value.groups.first_key_value().unwrap().0.clone(),
                    ScopedResult::Inconclusive(ResourceReason {
                        phase: "test".into(),
                        resource: "work".into(),
                        details: Default::default(),
                    }),
                );
            }
        }
        assert_ne!(r.results, altered);
    }
    let tiny = Limits {
        max_bdd_variables: 0,
        ..limits.clone()
    };
    let tiny = checked(&p, &tiny);
    let CheckOutcome::Inconclusive { reason, .. } = tiny.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    assert_eq!(
        tiny.request()
            .exhausted(reason)
            .unfinished
            .unwrap()
            .resource,
        "BDD variables"
    );
    // Find a scoped exhaustion boundary in the current implementation;
    // no particular historical node allowance is part of the contract.
    let mut scoped_exhaustion = false;
    for nodes in 0..=condition_storage_peak(&r.results.receipts) {
        let bounded = Limits {
            max_condition_nodes: nodes,
            ..limits.clone()
        };
        let bounded = checked(&p, &bounded);
        if let CheckOutcome::Complete(result) = bounded.verify(&(&limits).into()).unwrap() {
            if result.results.value.groups.values().any(|r| matches!(r, ScopedResult::Inconclusive(ResourceReason { resource, .. }) if resource == "condition nodes")) {
                scoped_exhaustion = true;
                break;
            }
        }
    }
    assert!(scoped_exhaustion);
    let (_, _, mut empty_program) = lower(source);
    let id = empty_program
        .corpus
        .verification_in(
            Namespace::default(),
            "consistency_only",
            [empty_program.library.one_value_per_input],
            [],
        )
        .unwrap();
    empty_program
        .keys
        .bind_verification(
            &empty_program.corpus,
            id,
            VerificationKey(QualifiedKey::new("test", "consistency_only")),
        )
        .unwrap();
    let empty = CheckRequest::for_verification(
        &empty_program.corpus,
        &empty_program.keys,
        &empty_program.domains(),
        id,
        &limits,
    )
    .unwrap();
    let RequestPreparation::Complete(empty) = empty
        .prepare(
            &empty_program.corpus,
            &empty_program.keys,
            &(&limits).into(),
        )
        .unwrap()
    else {
        panic!("unexpected preparation exhaustion")
    };
    assert!(empty.keys().groups.is_empty());
    let cancelled = OperationalLimits::from(&limits);
    cancelled.cancellation.cancel();
    assert!(matches!(g.verify(&cancelled), Err(CheckError::Cancelled)));
    let deadline = OperationalLimits {
        profile: Default::default(),
        cancellation: Cancellation::default(),
        timeout: Duration::ZERO,
    };
    assert!(matches!(
        g.verify(&deadline),
        Err(CheckError::Deadline { .. })
    ));
}

#[test]
fn committed_key_index_retains_original_bindings_and_indexes_rewrites() {
    let (_, _, p) = lower(
        "input i, j; slot a; a <- i when present(j) and not present(j) and not available(a); a <- j;",
    );
    let g = checked(&p, &Limits::default());
    assert!(!g.keys().rewrites.is_empty());
    assert_eq!(
        g.keys().instances.len(),
        g.program().original_rules().count()
    );
    assert_eq!(g.keys().committed.len(), g.program().rules().count());
    assert!(
        g.keys()
            .content
            .iter()
            .any(|(k, v)| g.keys().committed.get(k) != Some(v))
    );
    for proof in g.program().rewrite_proofs() {
        let key = &g.keys().rewrites[&proof.id];
        assert_eq!(key.candidate, g.keys().instances[&proof.candidate.rule.id]);
        assert!(g.keys().content.contains_key(&key.candidate));
        for producer in &key.producers {
            assert!(g.keys().content.contains_key(producer));
        }
        if let KeyedRewriteKind::Discharge(o) = &key.kind {
            p.keys.bindings().resolve(o).unwrap();
        }
    }
    assert_eq!(g.keys().components.len(), g.program().components().count());
    for c in g.program().components() {
        let actual: BTreeSet<_> = c
            .atoms
            .iter()
            .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
            .collect();
        assert_eq!(
            actual,
            g.keys().components[&c.id].0.iter().cloned().collect()
        );
    }
    let CheckOutcome::Complete(r) = g.verify(&(&Limits::default()).into()).unwrap() else {
        panic!()
    };
    for result in r.results.value.groups.values() {
        if let ScopedResult::Counterexample(_, e) = result {
            for o in &e.occurrences {
                p.keys.bindings().resolve(o).unwrap();
            }
            for i in &e.instances {
                assert!(g.keys().content.contains_key(i));
            }
        }
    }
}

#[test]
fn request_preparation_preserves_current_inventory_and_errors() {
    for row in edit_regressions() {
        for side in ["before", "after"] {
            let text = row[format!("{side}_source")].as_str().unwrap();
            let (ast, sources) = parse(text);
            match lowering::lower(&ast, &sources).unwrap() {
                LoweringOutcome::UserErrors(errors) => assert_eq!(
                    json!(
                        errors
                            .iter()
                            .map(|e| format!("{:?}", e.kind))
                            .collect::<Vec<_>>()
                    ),
                    row[format!("{side}_errors")]
                ),
                LoweringOutcome::Lowered(p) => {
                    assert!(row[format!("{side}_errors")].is_null());
                    let limits = Limits::default();
                    let RequestPreparation::Complete(g) = request(&p, &limits)
                        .prepare(&p.corpus, &p.keys, &(&limits).into())
                        .unwrap()
                    else {
                        panic!()
                    };
                    let raw = prepare(&p, &limits).unwrap();
                    assert_eq!(
                        inventory(&ast, &sources, &p, &raw),
                        inventory(&ast, &sources, &p, g.program())
                    );
                }
            }
        }
    }
}

#[test]
fn explicit_request_constraints_control_permitted_worlds_and_validate_keys() {
    let (_, _, mut p) = lower(
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
    );
    let unrestricted = p
        .corpus
        .verification_in(
            Namespace::default(),
            "unrestricted",
            [],
            [p.library.unique_input],
        )
        .unwrap();
    p.keys
        .bind_verification(
            &p.corpus,
            unrestricted,
            VerificationKey(QualifiedKey::new("test", "unrestricted")),
        )
        .unwrap();
    let limits = Limits::default();
    let constrained = checked(&p, &limits);
    let CheckOutcome::Complete(constrained) = constrained.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    assert!(
        constrained
            .results
            .value
            .groups
            .values()
            .all(|r| matches!(r, ScopedResult::Proved))
    );
    let mut req =
        CheckRequest::for_verification(&p.corpus, &p.keys, &p.domains(), unrestricted, &limits)
            .unwrap();
    let RequestPreparation::Complete(unrestricted) =
        req.prepare(&p.corpus, &p.keys, &(&limits).into()).unwrap()
    else {
        panic!()
    };
    let unrestricted = unrestricted.admit(&(&limits).into()).unwrap();
    let CheckOutcome::Complete(unrestricted) = unrestricted.verify(&(&limits).into()).unwrap()
    else {
        panic!()
    };
    assert!(
        unrestricted
            .results
            .value
            .groups
            .values()
            .any(|r| matches!(r, ScopedResult::Counterexample(..)))
    );
    assert_ne!(
        constrained.results.value.context,
        unrestricted.results.value.context
    );
    let (_, _, other) = lower("input i, j; slot a;");
    assert!(matches!(
        req.prepare(&other.corpus, &p.keys, &(&limits).into()),
        Err(CheckError::Keys(_))
    ));
    req.backend.configuration.push('!');
    assert!(matches!(
        req.prepare(&p.corpus, &p.keys, &(&limits).into()),
        Err(CheckError::InvalidRequest(_))
    ));
}

#[test]
fn named_witness_and_context_survive_declaration_reordering() {
    let (_, _, p) = lower("input z, a, m; slot s; s <- z; s <- a; s <- m;");
    let (_, _, q) = lower("input m, z, a; slot s; s <- z; s <- a; s <- m;");
    let limits = Limits::default();
    let p = checked(&p, &limits);
    let q = checked(&q, &limits);
    let CheckOutcome::Complete(p) = p.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    let CheckOutcome::Complete(q) = q.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    assert!(
        p.results
            .value
            .groups
            .values()
            .any(|r| matches!(r, ScopedResult::Counterexample(..)))
    );
    assert_eq!(p.results.value, q.results.value);
    assert_eq!(
        p.results, q.results,
        "canonical tuple work survives declaration reordering"
    );
}
