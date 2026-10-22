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
        assert!(
            metrics
                .scc_work
                .values()
                .map(|w| w.elapsed)
                .sum::<Duration>()
                <= metrics.evaluation
        );
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
fn owned_slots_recycle_above_512_scopes_without_whole_database_resets() {
    let template = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let mut session = Session::default();
    for i in 0..600 {
        let mut q = template.clone();
        let LocalScope::Group(ref mut k) = q.scope else {
            panic!()
        };
        k.obligation = ObligationKey(QualifiedKey::new("retention", format!("q{i}")));
        session
            .execute(&q, &ops(), &mut LocalMetrics::default())
            .unwrap();
        assert_eq!(session.stats().resets, 0);
        assert!(session.stats().retained_entries <= 1024);
        assert!(session.stats().retained_bytes <= 64 * 1024 * 1024);
    }
    assert!(session.stats().evicted > 0);
    // Recent scopes remain reusable after churn; old slots were reassigned.
    let before = session.stats();
    let mut q = template;
    let LocalScope::Group(ref mut k) = q.scope else {
        panic!()
    };
    k.obligation = ObligationKey(QualifiedKey::new("retention", "q599"));
    session
        .execute(&q, &ops(), &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(session.stats().evaluation_misses, before.evaluation_misses);
}
#[test]
#[ignore = "capture the new owned-query accounting reference; never overwrite frozen captures"]
fn capture_owned_query_reference() {
    println!("OWNED_6B2A_REFERENCE={}", local::local_reference());
}

#[test]
#[ignore = "isolated release owned-cone cold/warm/edit measurements"]
fn measure_owned_query_paths() {
    assert!(!cfg!(debug_assertions));
    fn run(session: &mut Session, source: &str) -> (Value, Accounted<ScopedResults>) {
        let start = Instant::now();
        let (_, _, p) = lower(source);
        let assembly = start.elapsed();
        let limits = Limits {
            timeout: Duration::from_secs(60),
            ..Limits::default()
        };
        let request = request_evidence::request(&p, &limits);
        let start = Instant::now();
        let RequestPreparation::Complete(g) = session
            .prepare(&request, &p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!()
        };
        let preparation = start.elapsed();
        let start = Instant::now();
        let g = g.admit(&(&limits).into()).unwrap();
        let admission = start.elapsed();
        let start = Instant::now();
        let LocalCheckOutcome::Complete(r) = session.verify(&g, &(&limits).into()).unwrap() else {
            panic!()
        };
        let checking = start.elapsed();
        let start = Instant::now();
        let LocalCheckOutcome::Complete(fresh) =
            FreshSession.verify(&g, &(&limits).into()).unwrap()
        else {
            panic!()
        };
        let fresh_time = start.elapsed();
        assert_eq!(r.checked.results, fresh.checked.results);
        let start = Instant::now();
        let CheckOutcome::Complete(global) = g.verify(&(&limits).into()).unwrap() else {
            panic!()
        };
        let global_time = start.elapsed();
        assert_eq!(r.checked.results.value, global.results.value);
        let c = session.stats();
        let m = r.metrics;
        let v = json!({"assembly_ns":assembly.as_nanos(),"preparation_ns":preparation.as_nanos(),"admission_ns":admission.as_nanos(),"checking_ns":checking.as_nanos(),"fresh_checking_ns":fresh_time.as_nanos(),"global_checking_ns":global_time.as_nanos(),"key_projection_ns":m.keys.as_nanos(),"evaluation_ns":m.evaluation.as_nanos(),"scc_evaluation_ns":m.scc_work.values().map(|w|w.elapsed.as_nanos()).sum::<u128>(),"unique_evaluated_sccs":m.scc_work.len(),"scc_cone_evaluations":m.scc_work.values().map(|w|w.cone_evaluations).sum::<usize>(),"duplicate_scc_cone_evaluations":m.scc_work.values().map(|w|w.cone_evaluations.saturating_sub(1)).sum::<usize>(),"predicted_duplicate_scc_ns":m.scc_work.values().map(|w|w.elapsed.as_nanos() * w.cone_evaluations.saturating_sub(1) as u128 / w.cone_evaluations.max(1) as u128).sum::<u128>(),"export_ns":m.export.as_nanos(),"property_ns":m.property.as_nanos(),"completion_ns":m.completion.as_nanos(),"conversion_ns":m.conversion.as_nanos(),"finding_context_ns":m.finding_context.as_nanos(),"evaluation_hits":c.evaluation_hits,"evaluation_misses":c.evaluation_misses,"verdict_hits":c.verdict_hits,"verdict_misses":c.verdict_misses,"completion_hits":c.completion_hits,"completion_misses":c.completion_misses,"evicted":c.evicted,"bypassed":c.bypassed,"resets":c.resets,"retained_entries":c.retained_entries,"retained_bytes":c.retained_bytes,"retained_condition_nodes":c.retained_condition_nodes,"reused_query_work":c.reused_query_work,"logical_work":r.checked.results.receipts.total().unwrap().work});
        (v, r.checked.results)
    }
    let data: Value = serde_json::from_str(include_str!("../../LOCAL-6b.1a.json")).unwrap();
    let mut rows = Vec::new();
    for row in data["measurement"]["rows"].as_array().unwrap() {
        let source = row["source"].as_str().unwrap();
        let mut samples = Vec::new();
        for iteration in 0..6 {
            let mut session = Session::default();
            let (cold, a) = run(&mut session, source);
            let (warm, b) = run(&mut session, &format!("// moved\n{source}"));
            assert_eq!(a, b);
            if cold["bypassed"] == 0 && cold["evicted"] == 0 {
                assert_eq!(warm["evaluation_misses"], 0);
            }
            let edited = format!("{source}\ninput new6b; slot new6b_slot; new6b_slot <- new6b;");
            let (edit, _) = run(&mut session, &edited);
            if iteration > 0 {
                samples.push(json!({"cold":cold,"warm":warm,"edit":edit}));
            }
        }
        rows.push(
            json!({"family":row["family"],"size":row["size"],"source":source,"samples":samples}),
        );
    }
    assert_eq!(rows.len(), 26);
    println!(
        "OWNED_6B2A_MEASUREMENTS={}",
        json!({"warmups":1,"samples_per_point":5,"rows":rows})
    );
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
