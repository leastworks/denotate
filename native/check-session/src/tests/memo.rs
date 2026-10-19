//! Cached execution is checked against the immutable local fresh reference.
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
    if session.stats().evaluation_misses == 0 {
        assert_eq!(cached.metrics.evaluation, Duration::ZERO);
        assert_eq!(cached.metrics.export, Duration::ZERO);
        assert_eq!(cached.metrics.property, Duration::ZERO);
        assert_eq!(cached.metrics.completion, Duration::ZERO);
    }
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
fn memo_cold_warm_frozen_sources_and_current_attribution() {
    let data: Value =
        serde_json::from_str(include_str!("../../../check/IDENTITIES-6a.1.json")).unwrap();
    let sources: BTreeSet<_> = data["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["invalid_source"] != true)
        .map(|r| r["source"].as_str().unwrap())
        .collect();
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
            let uri = "file:///invalid.inputmapping".parse().unwrap();
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
                assert_eq!(stats.evaluation_hits, 15);
                assert_eq!(stats.evaluation_misses, 1);
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
fn memo_all_43_frozen_results_and_receipts_are_exact() {
    let reference: Value =
        serde_json::from_str(include_str!("../../fixtures/LOCAL-6b.1a-REFERENCE.json")).unwrap();
    let mut count = 0;
    for row in reference["cases"].as_array().unwrap() {
        let source = row["source"].as_str().unwrap();
        let limits = Limits {
            max_work: row["max_work"].as_u64().unwrap() as usize,
            ..generous()
        };
        let mut session = Session::default();
        for _ in 0..2 {
            let (_, _, p) = lower(source);
            let request = request_evidence::request(&p, &limits);
            let exhausted = |reason: Inconclusive, receipts| {
                (
                    json!({"status":"inconclusive","phase":reason.phase,"resource":reason.resource}),
                    Accounted {
                        value: request.exhausted(reason),
                        receipts,
                    },
                )
            };
            let (capture, result) = match session
                .prepare(&request, &p.corpus, &p.keys, &(&limits).into())
                .unwrap()
            {
                RequestPreparation::Inconclusive { reason, receipts } => {
                    exhausted(reason, receipts)
                }
                RequestPreparation::Complete(g) => {
                    let g = g.admit(&(&limits).into()).unwrap();
                    match session.verify(&g, &(&limits).into()).unwrap() {
                        LocalCheckOutcome::Inconclusive { reason, receipts } => {
                            exhausted(reason, receipts)
                        }
                        LocalCheckOutcome::Complete(r) => (
                            captured_report(&r.checked.verification, &Names { keys: &p.keys }),
                            r.checked.results,
                        ),
                    }
                }
            };
            assert_eq!(capture, row["captured_result"], "{source}");
            assert_eq!(
                format!("{:?}", result.value),
                row["neutral_result"].as_str().unwrap()
            );
            assert_eq!(
                budget_evidence::receipt_capture(&result.receipts),
                row["receipts"],
                "{source}"
            );
        }
        count += 1;
    }
    assert_eq!(count, 43);
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
        // admission, covered separately by the exact 43 frozen pairs above.
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
    }
    impl LocalMemoStore for Interrupt<'_> {
        fn get(
            &mut self,
            input: &LocalInput,
            work: &LocalWorkInput,
        ) -> Option<std::sync::Arc<LocalMemo>> {
            let value = self.session.get(input, work);
            if !self.after_put {
                self.cancel.cancel();
            }
            value
        }
        fn put(
            &mut self,
            input: &LocalInput,
            work: &LocalWorkInput,
            value: std::sync::Arc<LocalMemo>,
        ) {
            self.session.put(input, work, value);
            if self.after_put {
                self.cancel.cancel();
            }
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
        };
        assert!(matches!(
            g.verify_local_with(&(&limits).into(), &mut interrupted),
            Err(CheckError::Cancelled)
        ));
        let (_, stats) = check(&mut session, &wide, &generous());
        assert_eq!(stats.evaluation_hits, usize::from(after_put));
        assert_eq!(stats.evaluation_misses, 16 - usize::from(after_put));
    }
}

#[test]
#[ignore = "manual 6b.1b cold/warm phase measurements; run alone in release"]
fn measure_memoized_workload_families() {
    fn sample(
        session: &mut Session,
        source: &str,
        global: bool,
    ) -> (Accounted<ScopedResults>, Value) {
        let limits = generous();
        let start = Instant::now();
        let (_, _, p) = lower(source);
        let assembly_ns = start.elapsed().as_nanos();
        let request = request_evidence::request(&p, &limits);
        let start = Instant::now();
        let RequestPreparation::Complete(g) = request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!()
        };
        let preparation_ns = start.elapsed().as_nanos();
        let start = Instant::now();
        let g = g.admit(&(&limits).into()).unwrap();
        let admission_ns = start.elapsed().as_nanos();
        let start = Instant::now();
        let LocalCheckOutcome::Complete(r) = session.verify(&g, &(&limits).into()).unwrap() else {
            panic!()
        };
        let checking_ns = start.elapsed().as_nanos();
        let mut global_ns = None;
        if global {
            let start = Instant::now();
            let CheckOutcome::Complete(reference) = g.verify(&(&limits).into()).unwrap() else {
                panic!()
            };
            global_ns = Some(start.elapsed().as_nanos());
            assert_eq!(reference.results.value, r.checked.results.value);
        }
        let c = session.stats();
        let m = r.metrics;
        let record = json!({"assembly_ns":assembly_ns,"preparation_ns":preparation_ns,"admission_ns":admission_ns,"checking_ns":checking_ns,"global_checking_ns":global_ns,
            "key_computation_ns":(p.key_computation+g.key_computation()+m.keys).as_nanos(),"local_keys_ns":m.keys.as_nanos(),
            "local_evaluation_ns":m.evaluation.as_nanos(),"bdd_export_ns":m.export.as_nanos(),"property_ns":m.property.as_nanos(),"completion_ns":m.completion.as_nanos(),"conversion_ns":m.conversion.as_nanos(),"finding_context_ns":m.finding_context.as_nanos(),
            "replay_ns":r.checked.verification.finding_metrics.replay.as_nanos(),"certification_ns":r.checked.verification.finding_metrics.certification.as_nanos(),
            "lookup_ns":c.lookup_ns,"publication_ns":c.publication_ns,"evaluation_hits":c.evaluation_hits,"evaluation_misses":c.evaluation_misses,"verdict_hits":c.verdict_hits,"verdict_misses":c.verdict_misses,"completion_hits":c.completion_hits,"completion_misses":c.completion_misses,
            "evicted":c.evicted,"bypassed":c.bypassed,"resets":c.resets,"reused_query_work":c.reused_query_work,"logical_work":r.checked.results.receipts.total().unwrap().work,"retained_entries":c.retained_entries,"retained_bytes":c.retained_bytes,"retained_condition_nodes":c.retained_condition_nodes,
            "cone_atoms":m.cone_atoms,"unique_atoms":m.unique_atoms,"cone_inputs":m.cone_inputs,"queries":r.queries.len()});
        (r.checked.results, record)
    }
    let mut workloads = Vec::new();
    for family in ["duplicates", "distinct_literals", "helper_chain"] {
        for size in [1, 4, 16, 64] {
            workloads.push((
                format!("query_{family}"),
                size,
                format!(
                    "{}s0 <- i1; s1 <- i2; s2 <- i3; s3 <- i0;",
                    workload(family, size)
                ),
            ));
        }
    }
    let (_, wide, _) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "wide_local_guard")
        .unwrap();
    workloads.push(("wide_overlap".into(), 16, wide));
    workloads.push((
        "mixed_completion".into(),
        1,
        "input i,j; slot a,b; a <- i; a <- j; b <- i when not available(b);".into(),
    ));
    let mut rows = Vec::new();
    for (family, size, source) in workloads {
        let mut samples = Vec::new();
        let mut receipt = Value::Null;
        for run in 0..6 {
            let mut session = Session::default();
            let (cold, cold_times) = sample(&mut session, &source, true);
            let (warm, warm_times) = sample(
                &mut session,
                &format!("// current snapshot\n{source}"),
                false,
            );
            assert_eq!(cold, warm);
            let stats = session.stats();
            assert!(
                stats.evaluation_misses == 0
                    || stats.evicted > 0
                    || stats.bypassed > 0
                    || stats.resets > 0,
                "{family}/{size}: {stats:?}"
            );
            if stats.evaluation_misses == 0 {
                assert_eq!(stats.verdict_misses + stats.completion_misses, 0);
            }
            receipt = budget_evidence::receipt_capture(&cold.receipts);
            if run > 0 {
                samples.push(json!({"cold":cold_times,"warm":warm_times}));
            }
        }
        rows.push(json!({"family":family,"size":size,"source":source,"samples":samples,"receipts":receipt}));
    }
    println!(
        "CACHE_6B1B_MEASUREMENTS={}",
        json!({"warmups":1,"samples_per_point":5,"rows":rows})
    );
}

#[test]
fn memo_receipt_invalidation_survives_interruption_with_equal_outcomes() {
    struct StopAfterLookup<'a>(&'a mut Session, Cancellation);
    impl LocalMemoStore for StopAfterLookup<'_> {
        fn get(&mut self, i: &LocalInput, w: &LocalWorkInput) -> Option<std::sync::Arc<LocalMemo>> {
            let value = self.0.get(i, w);
            self.1.cancel();
            value
        }
        fn put(&mut self, i: &LocalInput, w: &LocalWorkInput, v: std::sync::Arc<LocalMemo>) {
            self.0.put(i, w, v);
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
fn memo_reviewed_64_node_flip_stays_separate_and_exact() {
    let delta: Value = serde_json::from_str(include_str!("../../LOCAL-DELTA-6b.1a.json")).unwrap();
    let source = delta["tight_limit_delta"]["source"].as_str().unwrap();
    let limits = Limits {
        max_condition_nodes: 64,
        ..generous()
    };
    let mut session = Session::default();
    for _ in 0..2 {
        let (result, _) = check(&mut session, source, &limits);
        assert_eq!(result.value.groups.len(), 16);
        assert!(
            result
                .value
                .groups
                .values()
                .all(|r| matches!(r, ScopedResult::Counterexample(..)))
        );
    }
    assert_eq!(session.stats().evaluation_hits, 16);
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
    struct Capture(Vec<(LocalInput, LocalWorkInput, std::sync::Arc<LocalMemo>)>);
    impl LocalMemoStore for Capture {
        fn get(&mut self, _: &LocalInput, _: &LocalWorkInput) -> Option<std::sync::Arc<LocalMemo>> {
            None
        }
        fn put(&mut self, i: &LocalInput, w: &LocalWorkInput, v: std::sync::Arc<LocalMemo>) {
            self.0.push((i.clone(), w.clone(), v));
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
    let (mut input, work, value) = capture.0.remove(0);
    let mut session = Session::new(Retention {
        max_bytes: 1024 * 1024,
        ..Retention::default()
    });
    check(&mut session, &wide, &generous());
    input.backend.configuration = "x".repeat(2 * 1024 * 1024);
    assert!(session.get(&input, &work).is_none());
    session.put(&input, &work, value);
    assert!(session.retained_receipts(&input.scope).is_none());
    let (_, stats) = check(&mut session, &wide, &generous());
    assert_eq!(stats.evaluation_hits, 15);
    assert_eq!(stats.evaluation_misses, 1);
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
