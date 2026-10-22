//! Migration acceptance against immutable 6.0/6a.1 captures.
use super::*;

pub(super) fn request(p: &LoweredProgram, limits: &Limits) -> CheckRequest {
    CheckRequest::all_obligations(&p.corpus, &p.keys, &p.domains(), &constraints(p), limits)
        .unwrap()
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
fn frozen_witness_migration_is_exact() {
    let report: Value =
        serde_json::from_str(include_str!("../../../check/IDENTITIES-6a.1.json")).unwrap();
    let delta: Value =
        serde_json::from_str(include_str!("../../../check/WITNESS-ORDER-6a.2.json")).unwrap();
    let baseline: Value = serde_json::from_str(include_str!(
        "../../../check/fixtures/SLICE-6.0-BASELINE.json"
    ))
    .unwrap();
    let report = super::planner_evidence::adapted("identities", report);
    let baseline = super::planner_evidence::adapted("baseline", baseline);
    let mut used = BTreeSet::new();
    let mut changed = 0;
    for row in report["witnesses"].as_array().unwrap() {
        if row["invalid_source"] == true {
            continue;
        }
        let case = row["fixture"].as_str().unwrap();
        let max_work = row["max_work"].as_u64().unwrap() as usize;
        let source = row["source"].as_str().unwrap();
        if let Some(index) = case.strip_prefix("budget/") {
            let frozen = &baseline["budgets"][index.parse::<usize>().unwrap()];
            assert_eq!(row["source"], frozen["source"]);
            assert_eq!(row["current"], frozen["result"]);
        } else {
            let (name, side) = case.rsplit_once('/').unwrap();
            let frozen = baseline["edits"]
                .as_array()
                .unwrap()
                .iter()
                .find(|r| r["edit"] == name)
                .unwrap();
            assert_eq!(row["source"], frozen[format!("{side}_source")]);
        }
        let (_, _, p) = lower(source);
        // The historical-order path independently replays/certifies the old
        // witness; the request boundary replays/certifies the new one. Both
        // use the current planner, with its explicit preparation-budget overlay.
        let old = budget_result_lowered(&p, max_work);
        let new = fresh_capture(&p, max_work);
        assert_eq!(old, row["current"], "old capture {case}");
        assert_eq!(new, row["proposed"], "6a.1 prediction {case}");
        assert_eq!(old != new, row["witness_differs"] == true);
        changed += usize::from(old != new);
        let mut adapted = old.clone();
        for (i, entry) in delta["entries"]
            .as_array()
            .unwrap()
            .iter()
            .enumerate()
            .filter(|(_, e)| e["case"] == case)
        {
            assert!(used.insert(i));
            let finding = entry["finding"].as_str().unwrap();
            let target = adapted.pointer_mut(finding).unwrap();
            assert_eq!(target["status"], entry["status"]);
            for field in ["present", "absent"] {
                assert_eq!(target[field], entry["old_witness"][field]);
                target[field] = entry["new_witness"][field].clone();
            }
        }
        assert_eq!(new, adapted, "unlisted difference in {case}");
    }
    assert_eq!(changed, 38);
    assert_eq!(used.len(), 41);
    assert_eq!(used.len(), delta["entries"].as_array().unwrap().len());
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
    let limited = Limits {
        max_condition_nodes: 11,
        ..limits.clone()
    };
    let limited = checked(&p, &limited);
    let CheckOutcome::Complete(limited) = limited.verify(&(&limits).into()).unwrap() else {
        panic!("expected scoped exhaustion")
    };
    assert!(limited.results.value.groups.values().any(|r|matches!(r,ScopedResult::Inconclusive(ResourceReason {resource,..}) if resource=="condition nodes")));
    let mut invalid = request(&p, &limits);
    invalid.obligations.clear();
    assert!(matches!(
        invalid.prepare(&p.corpus, &p.keys, &(&limits).into()),
        Err(CheckError::InvalidRequest(_))
    ));
    let cancelled = OperationalLimits::from(&limits);
    cancelled.cancellation.cancel();
    assert!(matches!(g.verify(&cancelled), Err(CheckError::Cancelled)));
    let deadline = OperationalLimits {
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
fn frozen_inventory_matches_request_preparation() {
    let frozen: Value = serde_json::from_str(include_str!(
        "../../../check/fixtures/SLICE-6.0-BASELINE.json"
    ))
    .unwrap();
    let snapshot = |text: &str| {
        let (ast, sources) = parse(text);
        match lowering::lower(&ast, &sources).unwrap() {
            LoweringOutcome::UserErrors(errors) => Err(errors
                .iter()
                .map(|e| format!("{:?}", e.kind))
                .collect::<Vec<_>>()),
            LoweringOutcome::Lowered(p) => {
                let limits = Limits::default();
                let RequestPreparation::Complete(g) = request(&p, &limits)
                    .prepare(&p.corpus, &p.keys, &(&limits).into())
                    .unwrap()
                else {
                    panic!()
                };
                Ok(inventory(&ast, &sources, &p, g.program()))
            }
        }
    };
    for row in frozen["edits"].as_array().unwrap() {
        let a = snapshot(row["before_source"].as_str().unwrap());
        let b = snapshot(row["after_source"].as_str().unwrap());
        let changes = match (&a, &b) {
            (Ok(a), Ok(b)) => delta(a, b),
            _ => Value::Null,
        };
        assert_eq!(json!(a.err()), row["before_errors"]);
        assert_eq!(json!(b.err()), row["after_errors"]);
        assert_eq!(changes, row["changes"], "{}", row["edit"]);
    }
}

#[test]
fn explicit_request_constraints_control_permitted_worlds_and_validate_keys() {
    let (_, _, p) = lower(
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
    );
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
    let mut req = request(&p, &limits);
    req.constraints.clear();
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
