//! 6b.2a invariants: owned execution, Salsa cutoff, retention and scheduling.
use super::*;
use crate::{FreshSession, Session};

fn inputs(source: &str) -> Vec<LocalInput> {
    let (_, _, p) = lower(source);
    let limits = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let prepared = request_evidence::checked(&p, &limits);
    let LocalCheckOutcome::Complete(r) = FreshSession.verify(&prepared, &(&limits).into()).unwrap()
    else {
        panic!()
    };
    r.queries.into_values().map(|q| q.input).collect()
}
fn ops() -> OperationalLimits {
    OperationalLimits::from(&Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    })
}
#[test]
fn coarse_scc_work_counts_executed_cones_not_cache_hits_or_sat_queries() {
    let queries = inputs(
        "input i,j,k; slot shared,a,b; shared <- i; \
         a <- j when available(shared); a <- k when available(shared); \
         b <- j when available(shared); b <- k when available(shared);",
    );
    let mut expected = BTreeMap::<ComponentKey, BTreeSet<GroupKey>>::new();
    for input in &queries {
        let LocalScope::Group(group) = &input.scope else {
            panic!("fixture must have only admitted obligation cones")
        };
        for (key, component) in &input.components {
            assert!(component.blocked_by.is_empty());
            expected
                .entry(key.clone())
                .or_default()
                .insert(group.clone());
        }
    }
    assert!(expected.values().any(|cones| cones.len() > 1));
    let check_metrics = |metrics: &LocalMetrics| {
        assert_eq!(metrics.scc_work.len(), expected.len());
        for (key, cones) in &expected {
            let work = &metrics.scc_work[key];
            assert_eq!(work.cone_evaluations, cones.len());
        }
    };
    let mut fresh_metrics = LocalMetrics::default();
    let fresh = queries
        .iter()
        .map(|q| NoLocalMemo.execute(q, &ops(), &mut fresh_metrics).unwrap())
        .collect::<Vec<_>>();
    check_metrics(&fresh_metrics);
    let mut session = Session::default();
    for warm in [false, true] {
        let mut metrics = LocalMetrics::default();
        for (q, value) in queries.iter().zip(&fresh) {
            assert_eq!(&session.execute(q, &ops(), &mut metrics).unwrap(), value);
        }
        if warm {
            assert!(metrics.scc_work.is_empty());
        } else {
            check_metrics(&metrics);
        }
    }
    session.evict_values();
    let mut metrics = LocalMetrics::default();
    for (q, value) in queries.iter().zip(&fresh) {
        assert_eq!(&session.execute(q, &ops(), &mut metrics).unwrap(), value);
    }
    check_metrics(&metrics);
    let mut bypass = Session::new(crate::Retention {
        max_entries: 0,
        ..Default::default()
    });
    let mut metrics = LocalMetrics::default();
    for (q, value) in queries.iter().zip(&fresh) {
        assert_eq!(&bypass.execute(q, &ops(), &mut metrics).unwrap(), value);
    }
    check_metrics(&metrics);
    let mut metrics = LocalMetrics::default();
    for mut q in queries {
        q.backend = BackendIdentity::sat();
        session.execute(&q, &ops(), &mut metrics).unwrap();
    }
    assert!(metrics.scc_work.is_empty());
}
#[test]
fn owned_queries_survive_snapshot_drop_and_salsa_backdates_semantics_separately_from_receipts() {
    let mut input = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let mut session = Session::default();
    let first = session
        .execute(&input, &ops(), &mut LocalMetrics::default())
        .unwrap();
    let old = session.stats();
    // Duplicate a positive premise: a valid ground equation with identical
    // meaning, but more evaluation work. No current snapshot remains alive.
    let rule = input
        .rules
        .values_mut()
        .find(|r| !r.body.is_empty())
        .unwrap();
    rule.body.push(rule.body[0].clone());
    let next = session
        .execute(&input, &ops(), &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(first.evaluation, next.evaluation);
    assert_eq!(first.answer, next.answer);
    assert_ne!(first.evaluation_receipt, next.evaluation_receipt);
    assert_eq!(session.stats().evaluation_misses, old.evaluation_misses + 1);
    assert_eq!(session.stats().verdict_misses, old.verdict_misses);
    assert_eq!(session.stats().verdict_hits, old.verdict_hits + 1);
    assert_eq!(
        session.retained_receipts(&input.scope).unwrap().0,
        next.evaluation_receipt
    );
    let fresh = NoLocalMemo
        .execute(&input, &ops(), &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(next, fresh);
}
#[test]
fn owned_query_order_eviction_and_limits_do_not_change_results_or_charges() {
    let queries = inputs("input i,j,k; slot a,b; a <- i; a <- j; b <- k when not available(b);");
    assert!(queries.len() >= 2);
    let mut expected = BTreeMap::new();
    for q in &queries {
        expected.insert(
            q.scope.clone(),
            NoLocalMemo
                .execute(q, &ops(), &mut LocalMetrics::default())
                .unwrap(),
        );
    }
    let mut session = Session::default();
    for reverse in [false, true, false] {
        let mut order = queries.clone();
        if reverse {
            order.reverse();
            session.evict_values();
        }
        for q in order {
            assert_eq!(
                session
                    .execute(&q, &ops(), &mut LocalMetrics::default())
                    .unwrap(),
                expected[&q.scope]
            );
        }
    }
    for work in [0, 1, 32, 64, 128, 256, 500, 1000, 2000] {
        for q in &queries {
            let mut q = q.clone();
            q.limits.max_work = work;
            let fresh = NoLocalMemo
                .execute(&q, &ops(), &mut LocalMetrics::default())
                .unwrap();
            for _ in 0..2 {
                assert_eq!(
                    session
                        .execute(&q, &ops(), &mut LocalMetrics::default())
                        .unwrap(),
                    fresh
                );
            }
        }
    }
}
#[test]
fn owned_query_missing_premise_fails_closed() {
    let mut input = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let premise = input
        .rules
        .values()
        .find_map(|r| r.body.first())
        .unwrap()
        .1
        .atom
        .clone();
    input.facts.remove(&premise);
    assert!(matches!(
        NoLocalMemo.execute(&input, &ops(), &mut LocalMetrics::default()),
        Err(CheckError::Internal(
            "local premise outside dependency cone"
        ))
    ));
}
#[test]
fn owned_slots_recycle_beyond_capacity_without_whole_database_resets() {
    let template = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let retention = crate::Retention::default();
    let churn = retention.max_entries + 1;
    let mut session = Session::new(retention);
    for i in 0..churn {
        let mut q = template.clone();
        let LocalScope::Group(ref mut k) = q.scope else {
            panic!()
        };
        k.obligation = ObligationKey(QualifiedKey::new("retention", format!("q{i}")));
        session
            .execute(&q, &ops(), &mut LocalMetrics::default())
            .unwrap();
        assert_eq!(session.stats().resets, 0);
        assert!(session.stats().retained_entries <= retention.max_entries);
        assert!(session.stats().retained_bytes <= retention.max_bytes);
    }
    assert!(session.stats().evicted > 0);
    // Recent scopes remain reusable after churn; old slots were reassigned.
    let before = session.stats();
    let mut q = template;
    let LocalScope::Group(ref mut k) = q.scope else {
        panic!()
    };
    k.obligation = ObligationKey(QualifiedKey::new("retention", format!("q{}", churn - 1)));
    session
        .execute(&q, &ops(), &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(session.stats().evaluation_misses, before.evaluation_misses);
}

#[test]
fn owned_salsa_interruption_clears_failed_memos_and_recovery_recomputes() {
    let input = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let mut session = Session::default();
    session.interrupt_after_evaluation();
    assert!(matches!(
        session.execute(&input, &ops(), &mut LocalMetrics::default()),
        Err(CheckError::Cancelled)
    ));
    assert!(session.retained_receipts(&input.scope).is_none());
    let before = session.stats().evaluation_misses;
    let recovered = session
        .execute(&input, &ops(), &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(session.stats().evaluation_misses, before + 1);
    assert_eq!(
        recovered,
        NoLocalMemo
            .execute(&input, &ops(), &mut LocalMetrics::default())
            .unwrap()
    );
    assert_eq!(
        session
            .execute(&input, &ops(), &mut LocalMetrics::default())
            .unwrap(),
        recovered
    );
    assert_eq!(session.stats().evaluation_misses, before + 1);
}
