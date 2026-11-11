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
            assert_eq!(
                a.key_view().original_content().unwrap(),
                b.key_view().original_content().unwrap()
            );
            assert_eq!(
                a.program()
                    .components()
                    .map(|c| a.key_view().component(c.id).unwrap())
                    .collect::<BTreeSet<_>>(),
                b.program()
                    .components()
                    .map(|c| b.key_view().component(c.id).unwrap())
                    .collect::<BTreeSet<_>>()
            );
            assert_eq!(
                a.program()
                    .atoms()
                    .chain(
                        a.program()
                            .original_rules()
                            .flat_map(|r| r.body.iter().map(|l| &l.term.atom))
                    )
                    .map(|atom| a.key_view().atom(atom).unwrap())
                    .collect::<BTreeSet<_>>(),
                b.program()
                    .atoms()
                    .chain(
                        b.program()
                            .original_rules()
                            .flat_map(|r| r.body.iter().map(|l| &l.term.atom))
                    )
                    .map(|a| b.key_view().atom(a).unwrap())
                    .collect::<BTreeSet<_>>()
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
    let source = workload("helper_chain", 64);
    let retention = Retention::default();
    let mut session = Session::default();
    for _ in 0..2 {
        compare(&mut session, &source, 20_000_000);
        assert!(session.plan_stats().small_rules > 0);
        assert_eq!(session.plan_stats().queries, 0);
        assert_eq!(session.plan_stats().evicted, 0);
        assert_eq!(session.plan_stats().retained_entries, 0);
        assert_eq!(session.plan_stats().retained_bytes, 0);
        assert_eq!(
            session.local_retention_for_test().max_entries,
            retention.max_entries
        );
        assert_eq!(
            session.local_retention_for_test().max_bytes,
            retention.max_bytes
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
        profile: Default::default(),
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
