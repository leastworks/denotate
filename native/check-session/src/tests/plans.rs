use super::*;
use crate::{Retention, Session};

fn limits(work: usize) -> Limits {
    Limits {
        max_work: work,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}
fn compare(session: &mut Session, source: &str, work: usize) {
    let (_, sources, p) = lower(source);
    let limits = limits(work);
    let request = request_evidence::request(&p, &limits);
    let fresh = request
        .prepare(&p.corpus, &p.keys, &(&limits).into())
        .unwrap();
    let cached = session
        .prepare(&request, &p.corpus, &p.keys, &(&limits).into())
        .unwrap();
    match (fresh, cached) {
        (RequestPreparation::Complete(a), RequestPreparation::Complete(b)) => {
            assert_eq!(a.receipts(), b.receipts());
            assert_eq!(a.keys().content, b.keys().content);
            assert_eq!(
                a.keys().components.values().collect::<BTreeSet<_>>(),
                b.keys().components.values().collect::<BTreeSet<_>>()
            );
            assert_eq!(
                a.keys().atoms.values().collect::<BTreeSet<_>>(),
                b.keys().atoms.values().collect::<BTreeSet<_>>()
            );
            if work == 20_000_000 {
                let a = a.admit(&(&limits).into()).unwrap();
                let b = b.admit(&(&limits).into()).unwrap();
                let LocalCheckOutcome::Complete(fresh) =
                    crate::FreshSession.verify(&a, &(&limits).into()).unwrap()
                else {
                    panic!("fresh exhausted")
                };
                let LocalCheckOutcome::Complete(cached) =
                    session.verify(&b, &(&limits).into()).unwrap()
                else {
                    panic!("cached exhausted")
                };
                assert_eq!(fresh.checked.results, cached.checked.results);
                let render = |r: &Verification<'_>| {
                    format!(
                        "{:?}",
                        denotate_test_dsl::presentation::present(
                            &p,
                            r,
                            &sources,
                            denotate_test_dsl::attribution::SourceView::TestDsl.as_str()
                        )
                        .unwrap()
                    )
                };
                assert_eq!(
                    render(&fresh.checked.verification),
                    render(&cached.checked.verification)
                );
            }
        }
        (
            RequestPreparation::Inconclusive {
                reason: a,
                receipts: ar,
            },
            RequestPreparation::Inconclusive {
                reason: b,
                receipts: br,
            },
        ) => {
            assert_eq!(a, b, "work {work}");
            assert_eq!(ar, br, "work {work}");
        }
        _ => panic!("preparation outcome flip at {work}"),
    }
}

#[test]
fn small_rule_documents_keep_the_full_local_entry_allowance() {
    let data: Value = serde_json::from_str(include_str!("../../LOCAL-6b.1a.json")).unwrap();
    let row = data["measurement"]["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["family"] == "helper_chain" && r["size"] == 64)
        .unwrap();
    let source = row["source"].as_str().unwrap();
    let mut session = Session::default();
    for _ in 0..2 {
        compare(&mut session, source, 20_000_000);
        assert!(session.plan_stats().small_rules > 512);
        assert_eq!(session.plan_stats().queries, 0);
        assert_eq!(session.plan_stats().evicted, 0);
        assert_eq!(session.plan_stats().retained_entries, 0);
        assert_eq!(session.plan_stats().retained_bytes, 0);
        assert_eq!(session.local_retention_for_test().max_entries, 1024);
        assert_eq!(
            session.local_retention_for_test().max_bytes,
            64 * 1024 * 1024
        );
    }
}

#[test]
fn plans_all_edit_transitions_keep_results_receipts_and_current_sources() {
    let cases = edit_cases();
    assert_eq!(cases.len(), 26);
    for (_, before, after) in cases {
        let mut session = Session::default();
        for source in [&before, &after, &before, &after] {
            let (ast, sources) = parse(source);
            if matches!(
                lowering::lower(&ast, &sources).unwrap(),
                LoweringOutcome::UserErrors(_)
            ) {
                // Existing frontend capture tests pin these diagnostics; no
                // semantic preparation is dispatched for an invalid snapshot.
                continue;
            }
            compare(&mut session, source, 20_000_000);
        }
    }
}

#[test]
fn plans_reuse_current_rules_across_edits_and_undo() {
    let source = "input i,j,k,l,m; slot a,b; a <- i when present(j) and present(k) and present(l) and present(m); a <- j; b <- k;";
    let mut session = Session::default();
    compare(&mut session, source, 20_000_000);
    assert!(session.plan_stats().executed > 0);
    compare(
        &mut session,
        &format!("// shifted source\n{source}"),
        20_000_000,
    );
    assert_eq!(session.plan_stats().executed, 0);
    assert!(session.plan_stats().reused_work > 0);
    for edit in [
        source.replace("input i,j,k", "input k,j,i"),
        source.replace("b <- k;", "b <- j;"),
        format!("{source}\na <- j;"),
        source.into(),
    ] {
        compare(&mut session, &edit, 20_000_000);
        assert!(session.plan_stats().reused > 0);
    }
}

#[test]
fn plans_every_tight_preparation_prefix_matches_with_warm_cache() {
    let source = "input i,j,k,l,m; slot a; a <- i when present(j) and present(k) and present(l) and present(m); a <- j;";
    let mut session = Session::default();
    compare(&mut session, source, 20_000_000);
    let mut fallbacks = 0;
    for work in 0..1600 {
        compare(&mut session, source, work);
        fallbacks += session.plan_stats().fallback;
    }
    assert!(fallbacks > 0);
    compare(&mut session, source, 20_000_000);
    assert_eq!(session.plan_stats().executed, 0);
}

#[test]
fn plans_share_retention_and_recover_after_interruption_and_reset() {
    let source = "input i,j,k,l,m; slot a; a <- i when present(j) and present(k) and present(l) and present(m); a <- j;";
    let mut session = Session::new(Retention {
        max_entries: 32,
        max_bytes: 128 * 1024,
        max_condition_nodes: 1_000_000,
    });
    for i in 0..20 {
        compare(
            &mut session,
            &format!("{source}\nslot s{i}; s{i} <- i;"),
            20_000_000,
        );
        assert!(session.plan_stats().retained_entries <= 16);
        assert!(session.plan_stats().retained_bytes + session.stats().retained_bytes <= 128 * 1024);
        // Separate per-type entry caps; only payload bytes are shared.
        assert!(session.stats().retained_entries <= 32);
        assert_eq!(session.local_retention_for_test().max_entries, 32);
    }
    let (_, _, p) = lower(source);
    let request = request_evidence::request(&p, &limits(20_000_000));
    let operations = OperationalLimits::from(&limits(20_000_000));
    operations.cancellation.cancel();
    assert!(matches!(
        session.prepare(&request, &p.corpus, &p.keys, &operations),
        Err(CheckError::Cancelled)
    ));
    let mut operations = OperationalLimits::from(&limits(20_000_000));
    operations.timeout = Duration::ZERO;
    assert!(matches!(
        session.prepare(&request, &p.corpus, &p.keys, &operations),
        Err(CheckError::Deadline { .. })
    ));
    compare(&mut session, source, 20_000_000);
    session.reset();
    assert_eq!(session.plan_stats().retained_entries, 0);
    compare(&mut session, source, 20_000_000);
    assert!(session.plan_stats().executed > 0);
}

#[test]
fn completed_plan_survives_outer_interruption_without_caching_interruption() {
    struct Interrupt {
        plans: crate::plans::PlanCache,
        token: Option<Cancellation>,
    }
    impl JoinPlanStore for Interrupt {
        fn plan(
            &mut self,
            key: RuleKey,
            schema: RuleSchema,
            remaining: usize,
        ) -> Result<Option<std::sync::Arc<OwnedJoinPlan>>, CheckError> {
            let result = self.plans.plan(key, schema, remaining)?;
            if result.is_some() {
                if let Some(token) = self.token.take() {
                    token.cancel();
                }
            }
            Ok(result)
        }
    }
    let (_, _, p) = lower(
        "input i,j,k,l,m; slot a; a <- i when present(j) and present(k) and present(l) and present(m); a <- j;",
    );
    let limits = limits(20_000_000);
    let request = request_evidence::request(&p, &limits);
    let operations = OperationalLimits::from(&limits);
    let mut store = Interrupt {
        plans: Default::default(),
        token: Some(operations.cancellation.clone()),
    };
    store.plans.begin(128, 1024 * 1024);
    assert!(matches!(
        request.prepare_with_plans(&p.corpus, &p.keys, &operations, &mut store),
        Err(CheckError::Cancelled)
    ));
    assert_eq!(store.plans.stats.executed, 1);
    store.plans.begin(128, 1024 * 1024);
    let operations = OperationalLimits {
        cancellation: Cancellation::default(),
        timeout: Duration::from_secs(60),
    };
    let RequestPreparation::Complete(recovered) = request
        .prepare_with_plans(&p.corpus, &p.keys, &operations, &mut store)
        .unwrap()
    else {
        panic!("recovery exhausted")
    };
    let RequestPreparation::Complete(fresh) =
        request.prepare(&p.corpus, &p.keys, &operations).unwrap()
    else {
        panic!("fresh exhausted")
    };
    assert_eq!(recovered.receipts(), fresh.receipts());
    assert!(store.plans.stats.reused > 0);
}

#[test]
#[ignore = "isolated release preparation and full local-path measurements"]
fn measure_owned_plan_queries() {
    assert!(!cfg!(debug_assertions));
    fn run(session: &mut Session, source: &str) -> (Value, Accounted<ScopedResults>) {
        let start = Instant::now();
        let (_, _, p) = lower(source);
        let lowering_ns = start.elapsed().as_nanos();
        let limits = limits(20_000_000);
        let request = request_evidence::request(&p, &limits);
        let start = Instant::now();
        let RequestPreparation::Complete(prepared) = session
            .prepare(&request, &p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!("preparation exhausted")
        };
        let preparation_ns = start.elapsed().as_nanos();
        let m = prepared.program().metrics().clone();
        let preparation_receipts = budget_evidence::receipt_capture(prepared.receipts());
        let start = Instant::now();
        let prepared = prepared.admit(&(&limits).into()).unwrap();
        let admission_ns = start.elapsed().as_nanos();
        let start = Instant::now();
        let LocalCheckOutcome::Complete(result) =
            session.verify(&prepared, &(&limits).into()).unwrap()
        else {
            panic!("verification exhausted")
        };
        let verification_ns = start.elapsed().as_nanos();
        let q = session.plan_stats();
        let c = session.stats();
        (
            json!({"lowering_ns":lowering_ns,"preparation_ns":preparation_ns,"admission_ns":admission_ns,"verification_ns":verification_ns,
            "plans_and_seeds_ns":m.plans_and_seeds.as_nanos(),"plan_keying_ns":m.plan_keying.as_nanos(),"plan_binding_ns":m.plan_binding.as_nanos(),"input_seeding_ns":m.input_seeding.as_nanos(),"closure_and_instances_ns":m.closure_and_instances.as_nanos(),"ordering_ns":m.ordering.as_nanos(),"graph_ns":m.admissibility.as_nanos(),"grounding_ns":m.grounding.as_nanos(),"all_ground_keys_ns":prepared.key_computation().as_nanos(),
            "small_rules":q.small_rules,"evicted":q.evicted,"bypassed":q.bypassed,"queries":q.queries,"executed":q.executed,"reused":q.reused,"fallback":q.fallback,"reused_work":q.reused_work,"query_ns":q.query_ns,"execution_ns":q.execution_ns,"projection_ns":q.projection_ns,"plan_entries":q.retained_entries,"plan_bytes":q.retained_bytes,"local_bytes":c.retained_bytes,"local_misses":c.evaluation_misses,
            "evaluation_ns":result.metrics.evaluation.as_nanos(),"export_ns":result.metrics.export.as_nanos(),"preparation_receipts":preparation_receipts}),
            result.checked.results,
        )
    }
    let data: Value = serde_json::from_str(include_str!("../../LOCAL-6b.1a.json")).unwrap();
    let mut rows = Vec::new();
    for row in data["measurement"]["rows"].as_array().unwrap() {
        let source = row["source"].as_str().unwrap();
        let mut samples = Vec::new();
        for iteration in 0..6 {
            let mut baseline = Session::with_fresh_planning();
            let mut cached = Session::default();
            let (fresh, a) = run(&mut baseline, source);
            let (cold, b) = run(&mut cached, source);
            assert_eq!(a, b);
            let warm_source = format!("// current source\n{source}");
            let (fresh_warm, a) = run(&mut baseline, &warm_source);
            let (warm, b) = run(&mut cached, &warm_source);
            assert_eq!(a, b);
            if warm["evicted"] == 0 && warm["bypassed"] == 0 {
                assert_eq!(warm["executed"], 0, "{}", row["family"]);
            }
            let edited =
                format!("{source}\ninput added6b; slot added6b_slot; added6b_slot <- added6b;");
            let (fresh_edit, a) = run(&mut baseline, &edited);
            let (edit, b) = run(&mut cached, &edited);
            assert_eq!(a, b);
            if warm["queries"].as_u64().unwrap() > 0
                && edit["evicted"] == 0
                && edit["bypassed"] == 0
            {
                assert!(edit["reused"].as_u64().unwrap() > 0);
            }
            if iteration > 0 {
                samples.push(json!({"fresh":fresh,"cold":cold,"fresh_warm":fresh_warm,"warm":warm,"fresh_edit":fresh_edit,"edit":edit}));
            }
        }
        rows.push(
            json!({"family":row["family"],"size":row["size"],"source":source,"samples":samples}),
        );
    }
    assert_eq!(rows.len(), 26);
    println!(
        "PLANS_6B3A_MEASUREMENTS={}",
        json!({"warmups":1,"samples_per_point":5,"rows":rows})
    );
}
