//! Cached execution is checked against current fresh execution and semantic corpora.
use super::*;
use crate::{FreshSession, Retention, Session};
use denotate_test_dsl::{attribution::SourceView, presentation};

fn check(
    session: &mut Session,
    source: &str,
    limits: &Limits,
) -> (Accounted<ScopedResults>, crate::CacheStats) {
    let (_, sources, p) = lower(source);
    let prepared = request_evidence::checked(&p, limits);
    let LocalCheckOutcome::Complete(fresh) =
        FreshSession.verify(&prepared, &limits.into()).unwrap()
    else {
        panic!("fresh preparation exhausted")
    };
    let LocalCheckOutcome::Complete(cached) = session.verify(&prepared, &limits.into()).unwrap()
    else {
        panic!("cached preparation exhausted")
    };
    assert_eq!(fresh.checked.results, cached.checked.results, "{source}");
    assert_eq!(fresh.queries, cached.queries);
    let render = |r: &Verification<'_>| {
        format!(
            "{:?}",
            presentation::present(&p, r, &sources, SourceView::TestDsl.as_str()).unwrap()
        )
    };
    assert_eq!(
        render(&fresh.checked.verification),
        render(&cached.checked.verification),
        "current source attribution: {source}"
    );
    (cached.checked.results, session.stats())
}
fn generous() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}

#[test]
fn memo_cold_warm_regression_sources_and_current_attribution() {
    let cases = regression_cases();
    let sources = cases.iter().map(|r| r["source"].as_str().unwrap());
    for source in sources {
        let mut session = Session::default();
        check(&mut session, source, &generous());
        let (_, stats) = check(
            &mut session,
            &format!("// current location\n{source}"),
            &generous(),
        );
        assert_eq!(stats.evaluation_misses, 0, "{source}: {stats:?}");
        assert_eq!(stats.verdict_misses + stats.completion_misses, 0);
    }
}
#[test]
fn memo_eviction_retains_receipts_and_recomputes_exactly() {
    let source = "input i,j; slot a; a <- i; a <- j;";
    let mut session = Session::default();
    let (first, _) = check(&mut session, source, &generous());
    let scope = LocalScope::Group(first.value.groups.keys().next().unwrap().clone());
    let receipt = session.retained_receipts(&scope).unwrap();
    session.evict_values();
    assert_eq!(session.retained_receipts(&scope).unwrap(), receipt);
    let (next, stats) = check(&mut session, source, &generous());
    assert_eq!(first, next);
    assert!(stats.evaluation_misses > 0);
    let (_, stats) = check(&mut session, source, &generous());
    assert_eq!(stats.evaluation_misses, 0);
    session.reset();
    assert!(session.retained_receipts(&scope).is_none());
    assert!(check(&mut session, source, &generous()).1.evaluation_misses > 0);
}
#[test]
fn memo_limits_reordering_completion_and_recovery() {
    let sources = [
        "input z,a,m; slot b,c; b <- z; b <- a; c <- m;",
        "input m,a,z; slot b,c; b <- z; b <- a; c <- m;",
        "input i,j; slot a,b; a <- i; a <- j; b <- i when not available(b);",
        "input i,j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
        "input i,j; slot a; a <- i when input_value(i) is 01; a <- j when input_value(i) is 2;",
    ];
    for nodes in [64, 1_000_000] {
        let limits = Limits {
            max_condition_nodes: nodes,
            ..generous()
        };
        let mut session = Session::default();
        for source in sources.into_iter().chain(sources.into_iter().rev()) {
            check(&mut session, source, &limits);
            check(&mut session, source, &limits);
        }
    }
    let mut session = Session::default();
    let (_, _, p) = lower(sources[2]);
    let g = request_evidence::checked(&p, &generous());
    let limits = generous();
    limits.cancellation.cancel();
    assert!(matches!(
        session.verify(&g, &(&limits).into()),
        Err(CheckError::Cancelled)
    ));
    let limits = Limits {
        timeout: Duration::ZERO,
        ..generous()
    };
    assert!(matches!(
        session.verify(&g, &(&limits).into()),
        Err(CheckError::Deadline { .. })
    ));
    check(&mut session, sources[2], &generous());
}
#[test]
fn memo_retention_caps_and_oversized_bypass() {
    let source = "input i,j; slot a; a <- i; a <- j;";
    for retention in [
        Retention {
            max_entries: 0,
            ..Retention::default()
        },
        Retention {
            max_bytes: 1,
            ..Retention::default()
        },
        Retention {
            max_condition_nodes: 1,
            ..Retention::default()
        },
    ] {
        let mut session = Session::new(retention);
        for _ in 0..2 {
            let (_, stats) = check(&mut session, source, &generous());
            assert!(stats.bypassed > 0);
            assert_eq!(stats.retained_entries, 0);
        }
    }
}

#[test]
fn memo_all_edit_transitions_reuse_and_invalidation() {
    let run = |session: &mut Session, source: &str| {
        let (ast, sources) = parse(source);
        if matches!(
            lowering::lower(&ast, &sources).unwrap(),
            LoweringOutcome::UserErrors(_)
        ) {
            // Invalid edits stop before the cache. Compare fresh frontend diagnostics
            // and retain the session for the subsequent repair/undo.
            let uri = "file:///invalid.testdsl".parse().unwrap();
            let document = std::sync::Arc::new(Document::new(
                &mut syntax::parser().unwrap(),
                source.into(),
                1,
                true,
            ));
            let a = denotate_test_dsl::analysis::prepare(
                &uri,
                1,
                document.clone(),
                &mut lowering::incremental::Session::default(),
            )
            .unwrap();
            let b = denotate_test_dsl::analysis::prepare(
                &uri,
                1,
                document,
                &mut lowering::incremental::Session::default(),
            )
            .unwrap();
            assert!(a.program.is_none() && b.program.is_none());
            assert_eq!(a.fast, b.fast);
            return crate::CacheStats::default();
        }
        check(session, source, &generous()).1
    };
    for (name, before, after) in edit_cases() {
        let mut session = Session::default();
        run(&mut session, &before);
        let stats = run(&mut session, &after);
        match name.as_str() {
            "comment" | "numeric_alias" => {
                assert_eq!(stats.evaluation_misses, 0, "{name}: {stats:?}")
            }
            "wide_local_guard" => {
                let old = local::query_inputs(&before);
                let new = local::query_inputs(&after);
                let reusable = new
                    .iter()
                    .filter(|(key, input)| old.get(key) == Some(input))
                    .count();
                assert!(reusable > 0 && reusable < new.len());
                assert_eq!(stats.evaluation_hits, reusable);
                assert_eq!(stats.evaluation_misses, new.len() - reusable);
            }
            "insert_helper_before" => assert!(stats.evaluation_hits > 0, "{stats:?}"),
            "add_literal" | "remove_literal" => {
                assert_eq!(stats.evaluation_hits, 0, "K changes: {name}")
            }
            _ => {}
        }
        // Undo and a second edit history must produce the same current result,
        // regardless of which old publications remain in memory.
        run(&mut session, &before);
        run(&mut session, &after);
    }
}
#[test]
fn memo_resource_cases_match_fresh_before_and_after_eviction() {
    fn run(
        p: &LoweredProgram,
        limits: &Limits,
        mut session: Option<&mut Session>,
    ) -> Accounted<ScopedResults> {
        let req = request_evidence::request(p, limits);
        let ops = limits.into();
        let prep = match session.as_deref_mut() {
            Some(s) => s.prepare(&req, &p.corpus, &p.keys, &ops),
            None => req.prepare(&p.corpus, &p.keys, &ops),
        }
        .unwrap();
        let exhausted = |reason, receipts| Accounted {
            value: req.exhausted(reason),
            receipts,
        };
        match prep {
            RequestPreparation::Inconclusive { reason, receipts } => exhausted(reason, receipts),
            RequestPreparation::Complete(g) => {
                let g = g.admit(&ops).unwrap();
                let result = match session {
                    Some(s) => s.verify(&g, &ops),
                    None => FreshSession.verify(&g, &ops),
                }
                .unwrap();
                match result {
                    LocalCheckOutcome::Complete(r) => r.checked.results,
                    LocalCheckOutcome::Inconclusive { reason, receipts } => {
                        exhausted(reason, receipts)
                    }
                }
            }
        }
    }
    for (source, work) in resource_cases() {
        let (_, _, p) = lower(&source);
        let limits = Limits {
            max_work: work,
            ..generous()
        };
        let expected = run(&p, &limits, None);
        let mut session = Session::default();
        for _ in 0..2 {
            assert_eq!(
                expected,
                run(&p, &limits, Some(&mut session)),
                "{source} / {work}"
            );
        }
        session.evict_values();
        assert_eq!(
            expected,
            run(&p, &limits, Some(&mut session)),
            "{source} / {work}"
        );
    }
}
#[test]
fn memo_tight_completion_conversion_limits_match_fresh() {
    let source = "input z,a; slot s,t; s <- z when not available(s); t <- a when not available(t);";
    let (_, _, p) = lower(source);
    let mut completed = 0;
    for work in (300..3000).step_by(59) {
        let limits = Limits {
            max_work: work,
            ..generous()
        };
        // Keep preparation ample to reach the query boundaries under test.
        let mut request = request_evidence::request(&p, &generous());
        request.limits = (&limits).into();
        // Use the request's normal preparation; skip only limits that prevent
        // admission, covered separately by the resource cases above.
        let RequestPreparation::Complete(g) = request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            continue;
        };
        let g = g.admit(&(&limits).into()).unwrap();
        completed += 1;
        let mut session = Session::default();
        for _ in 0..2 {
            let fresh = FreshSession.verify(&g, &(&limits).into()).unwrap();
            let cached = session.verify(&g, &(&limits).into()).unwrap();
            match (fresh, cached) {
                (LocalCheckOutcome::Complete(a), LocalCheckOutcome::Complete(b)) => {
                    assert_eq!(a.checked.results, b.checked.results)
                }
                (
                    LocalCheckOutcome::Inconclusive {
                        reason: a,
                        receipts: ar,
                    },
                    LocalCheckOutcome::Inconclusive {
                        reason: b,
                        receipts: br,
                    },
                ) => {
                    assert_eq!(a, b);
                    assert_eq!(ar, br);
                }
                _ => panic!("different exhaustion boundary at {work}"),
            }
        }
    }
    assert!(completed > 0);
}

#[test]
fn memo_lru_node_eviction_and_metadata_reset_stay_bounded() {
    let (_, wide, _) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "wide_local_guard")
        .unwrap();
    for retention in [
        Retention {
            max_condition_nodes: 100,
            ..Retention::default()
        },
        Retention {
            max_entries: 2,
            ..Retention::default()
        },
    ] {
        let mut session = Session::new(retention);
        let (_, stats) = check(&mut session, &wide, &generous());
        assert!(stats.evicted > 0 || stats.resets > 0, "{stats:?}");
        assert!(stats.retained_entries <= retention.max_entries);
        assert!(stats.retained_bytes <= retention.max_bytes);
        assert!(stats.retained_condition_nodes <= retention.max_condition_nodes);
        check(&mut session, &wide, &generous());
    }
}

#[test]
fn memo_interruption_retains_only_completed_queries() {
    struct Interrupt<'a> {
        session: &'a mut Session,
        cancel: Cancellation,
        after_put: bool,
        completed: BTreeSet<LocalScope>,
    }
    impl LocalMemoStore for Interrupt<'_> {
        fn execute(
            &mut self,
            input: &LocalInput,
            operations: &OperationalLimits,
            metrics: &mut LocalMetrics,
        ) -> Result<std::sync::Arc<LocalMemo>, CheckError> {
            if !self.after_put {
                self.cancel.cancel();
            }
            let value = self.session.execute(input, operations, metrics)?;
            self.completed.insert(input.scope.clone());
            if self.after_put {
                self.cancel.cancel();
            }
            Ok(value)
        }
    }
    let (_, wide, _) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "wide_local_guard")
        .unwrap();
    for after_put in [false, true] {
        let (_, _, p) = lower(&wide);
        let g = request_evidence::checked(&p, &generous());
        let mut session = Session::default();
        let limits = generous();
        let mut interrupted = Interrupt {
            session: &mut session,
            cancel: limits.cancellation.clone(),
            after_put,
            completed: BTreeSet::new(),
        };
        assert!(matches!(
            g.verify_local_with(&(&limits).into(), &mut interrupted),
            Err(CheckError::Cancelled)
        ));
        let completed = interrupted.completed;
        let expected = local::query_inputs(&wide);
        assert!(completed.iter().all(|key| expected.contains_key(key)));
        let (_, stats) = check(&mut session, &wide, &generous());
        assert_eq!(stats.evaluation_hits, completed.len());
        assert_eq!(stats.evaluation_misses, expected.len() - completed.len());
    }
}

#[test]
fn memo_receipt_invalidation_survives_interruption_with_equal_outcomes() {
    struct StopAfterLookup<'a>(&'a mut Session, Cancellation);
    impl LocalMemoStore for StopAfterLookup<'_> {
        fn execute(
            &mut self,
            i: &LocalInput,
            operations: &OperationalLimits,
            metrics: &mut LocalMetrics,
        ) -> Result<std::sync::Arc<LocalMemo>, CheckError> {
            self.1.cancel();
            self.0.execute(i, operations, metrics)
        }
    }
    let before = "input i,j,k; slot a; a <- i; a <- j;";
    let after = "input i,j,k; slot a; a <- i when present(k); a <- j;";
    let mut session = Session::default();
    let (old, _) = check(&mut session, before, &generous());
    let scope = LocalScope::Group(old.value.groups.keys().next().unwrap().clone());
    assert!(session.retained_receipts(&scope).is_some());
    let (_, _, p) = lower(after);
    let g = request_evidence::checked(&p, &generous());
    let limits = generous();
    let mut stop = StopAfterLookup(&mut session, limits.cancellation.clone());
    assert!(matches!(
        g.verify_local_with(&(&limits).into(), &mut stop),
        Err(CheckError::Cancelled)
    ));
    assert!(session.retained_receipts(&scope).is_none());
    let (new, stats) = check(&mut session, after, &generous());
    assert!(stats.evaluation_misses > 0);
    assert!(matches!(
        old.value.groups.values().next().unwrap(),
        ScopedResult::Counterexample(..)
    ));
    assert!(matches!(
        new.value.groups.values().next().unwrap(),
        ScopedResult::Counterexample(..)
    ));
    assert_ne!(old.receipts, new.receipts);
}
#[test]
fn memo_component_permutations_preserve_tight_limit_receipts_or_recompute() {
    let (_, before, after) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "insert_helper_before")
        .unwrap();
    for nodes in [32, 64, 128, 256, 512, 1000000] {
        let limits = Limits {
            max_condition_nodes: nodes,
            ..generous()
        };
        let mut session = Session::default();
        check(&mut session, &before, &limits);
        check(&mut session, &after, &limits);
        check(&mut session, &before, &limits);
    }
}
#[test]
fn memo_independent_scopes_match_fresh_across_storage_limits() {
    let (_, source, _) = edit_cases()
        .into_iter()
        .find(|(name, _, _)| name == "wide_local_guard")
        .unwrap();
    for nodes in [16, 32, 64, 128, 256, 1024] {
        let limits = Limits {
            max_condition_nodes: nodes,
            ..generous()
        };
        let mut session = Session::default();
        let (cold, _) = check(&mut session, &source, &limits);
        let (warm, stats) = check(&mut session, &source, &limits);
        assert_eq!(cold, warm);
        assert_eq!(stats.evaluation_misses, 0);
        assert!(stats.evaluation_hits > 0);
    }
}

#[test]
fn memo_completion_global_replay_charges_are_current_after_unrelated_edits() {
    let base = "input i,j; slot a,b,spare; a <- i; a <- j; b <- i when not available(b);";
    let variants = [
        base.to_owned(),
        format!("{base} spare <- j;"),
        base.replace("input i,j;", "input i,j,z;"),
        format!("{base} spare <- j when input_value(j) is 1;"),
    ];
    let mut session = Session::default();
    for source in variants.iter().chain(variants.iter().rev()) {
        check(&mut session, source, &generous());
        check(&mut session, source, &generous());
    }
}

#[test]
fn memo_oversized_replacement_preserves_other_cones() {
    #[derive(Default)]
    struct Capture(Vec<LocalInput>);
    impl LocalMemoStore for Capture {
        fn execute(
            &mut self,
            i: &LocalInput,
            operations: &OperationalLimits,
            metrics: &mut LocalMetrics,
        ) -> Result<std::sync::Arc<LocalMemo>, CheckError> {
            self.0.push(i.clone());
            NoLocalMemo.execute(i, operations, metrics)
        }
    }
    let (_, wide, _) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "wide_local_guard")
        .unwrap();
    let (_, _, p) = lower(&wide);
    let g = request_evidence::checked(&p, &generous());
    let mut capture = Capture::default();
    g.verify_local_with(&(&generous()).into(), &mut capture)
        .unwrap();
    let mut input = capture.0.remove(0);
    let mut session = Session::new(Retention {
        max_bytes: 8 * 1024 * 1024,
        ..Retention::default()
    });
    check(&mut session, &wide, &generous());
    input.backend.configuration = "x".repeat(16 * 1024 * 1024);
    session
        .execute(&input, &(&generous()).into(), &mut LocalMetrics::default())
        .unwrap();
    assert!(session.retained_receipts(&input.scope).is_none());
    let (_, stats) = check(&mut session, &wide, &generous());
    let expected = local::query_inputs(&wide);
    let unaffected = expected.keys().filter(|key| **key != input.scope).count();
    assert_eq!(stats.evaluation_hits, unaffected);
    assert_eq!(stats.evaluation_misses, expected.len() - unaffected);
}

#[test]
fn memo_completion_order_changes_compare_exactly_under_tight_task_limits() {
    let before = "input z,a,m; slot r; r <- z when not available(r); r <- a when present(m);";
    let after = before.replace("input z,a,m;", "input m,a,z;");
    for tasks in [1, 2, 4, 8, 16, 64, 100000] {
        let limits = Limits {
            max_bdd_tasks: tasks,
            ..generous()
        };
        let mut session = Session::default();
        for source in [before, &after, before] {
            let (_, _, p) = lower(source);
            let g = request_evidence::checked(&p, &limits);
            for _ in 0..2 {
                let a = FreshSession.verify(&g, &(&limits).into()).unwrap();
                let b = session.verify(&g, &(&limits).into()).unwrap();
                match (a, b) {
                    (LocalCheckOutcome::Complete(a), LocalCheckOutcome::Complete(b)) => {
                        assert_eq!(a.checked.results, b.checked.results)
                    }
                    (
                        LocalCheckOutcome::Inconclusive {
                            reason: a,
                            receipts: ar,
                        },
                        LocalCheckOutcome::Inconclusive {
                            reason: b,
                            receipts: br,
                        },
                    ) => {
                        assert_eq!(a, b);
                        assert_eq!(ar, br);
                    }
                    _ => panic!("completion order changed exhaustion at {tasks}"),
                }
            }
        }
    }
}
