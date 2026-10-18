//! Local execution is compared with the unchanged global oracle and frozen inputs.
use super::*;
use crate::FreshSession;
use denotate_test_dsl::{attribution::SourceView, presentation};

fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}
fn compare(source: &str) {
    let (_, sources, p) = lower(source);
    let l = limits();
    let prepared = request_evidence::checked(&p, &l);
    let CheckOutcome::Complete(global) = prepared.verify(&(&l).into()).unwrap() else {
        panic!("global exhausted")
    };
    let LocalCheckOutcome::Complete(local) = FreshSession.verify(&prepared, &(&l).into()).unwrap()
    else {
        panic!("local exhausted")
    };
    assert_eq!(
        global.results.value, local.checked.results.value,
        "{source}"
    );
    let render = |r: &Verification<'_>| {
        format!(
            "{:?}",
            presentation::present(&p, r, &sources, SourceView::TestDsl.as_str()).unwrap()
        )
    };
    assert_eq!(
        render(&global.verification),
        render(&local.checked.verification),
        "{source}"
    );
    local.checked.results.receipts.total().unwrap();
    assert!(
        local
            .checked
            .results
            .receipts
            .get(&QueryKey::Symbolic)
            .is_none()
    );
}
#[test]
fn local_scopes_preserve_frozen_status_witness_and_current_diagnostics() {
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
        compare(source);
    }
}
#[test]
fn owned_local_queries_survive_snapshot_drop_and_trivia_edits() {
    let capture = |s: &str| {
        let (_, _, p) = lower(s);
        let l = limits();
        let prepared = request_evidence::checked(&p, &l);
        let LocalCheckOutcome::Complete(r) = FreshSession.verify(&prepared, &(&l).into()).unwrap()
        else {
            panic!()
        };
        (r.queries, r.checked.results)
    };
    let source = "input z, a, m; slot b, c; b <- z; b <- a; c <- m;";
    assert_eq!(capture(source), capture(&format!("// shifted\n{source}")));
    assert_eq!(
        capture(source).0,
        capture(&source.replace("input z, a, m", "input m, z, a")).0
    );
}
#[test]
fn local_at_most_one_projection_keeps_cross_boundary_and_singleton_constraints() {
    for source in [
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when not input_value(i) is 2;",
        "input z, a, m, unused; slot s; s <- z when present(a); s <- m when present(a);",
        "input i, j; slot a, b; a <- i; a <- j; b <- i when not available(b);",
    ] {
        compare(source);
    }
}
#[test]
fn local_interruption_never_returns_a_semantic_value_and_recovers() {
    let (_, _, p) = lower("input i, j; slot a; a <- i; a <- j;");
    let l = limits();
    let prepared = request_evidence::checked(&p, &l);
    let mut ops = OperationalLimits::from(&l);
    ops.cancellation.cancel();
    assert!(matches!(
        FreshSession.verify(&prepared, &ops),
        Err(CheckError::Cancelled)
    ));
    ops = OperationalLimits::from(&limits());
    ops.timeout = Duration::ZERO;
    assert!(matches!(
        FreshSession.verify(&prepared, &ops),
        Err(CheckError::Deadline { .. })
    ));
    assert!(matches!(
        FreshSession.verify(&prepared, &(&limits()).into()),
        Ok(LocalCheckOutcome::Complete(_))
    ));
}

#[test]
fn local_execution_preserves_pre_mask_normalization_and_84_fingerprint_cases() {
    for (text, count) in [
        (include_str!("../../../test-dsl/fixtures/pre-mask.json"), 22),
        (
            include_str!("../../../test-dsl/fixtures/pre-normalize.json"),
            38,
        ),
        (
            include_str!("../../../test-dsl/fixtures/pre-integration-fingerprints.json"),
            84,
        ),
    ] {
        let data: Value = serde_json::from_str(text).unwrap();
        let cases = data["cases"].as_array().unwrap();
        // Case counts are explicit so fixture coverage cannot silently shrink.
        assert_eq!(cases.len(), count);
        for row in cases {
            let source = row["text"].as_str().unwrap();
            let doc = std::sync::Arc::new(Document::new(
                &mut syntax::parser().unwrap(),
                source.into(),
                1,
                true,
            ));
            let frontend = denotate_test_dsl::analysis::prepare(
                &"file:///baseline.inputmapping".parse().unwrap(),
                1,
                doc,
                &mut denotate_test_dsl::lowering::incremental::Session::default(),
            )
            .unwrap();
            if frontend.program.is_none() {
                assert!(row.get("groups").is_none() && row.get("diagnostics").is_some());
                assert_eq!(
                    serde_json::to_value(frontend.fast).unwrap(),
                    row["diagnostics"]
                );
            } else {
                compare(source);
            }
        }
    }
}
fn local_reference() -> Value {
    let old: Value =
        serde_json::from_str(include_str!("../../../check/IDENTITIES-6a.1.json")).unwrap();
    let mut cases = BTreeMap::<(String, usize), Vec<String>>::new();
    for row in old["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["invalid_source"] != true)
    {
        cases
            .entry((
                row["source"].as_str().unwrap().into(),
                row["max_work"].as_u64().unwrap() as usize,
            ))
            .or_default()
            .push(row["fixture"].as_str().unwrap().into());
    }
    let rows:Vec<_>=cases.into_iter().map(|((source,max_work),fixtures)| {
        let (_,_,p)=lower(&source);let l=Limits {max_work,..limits()};let req=request_evidence::request(&p,&l);
        let exhausted=|reason:Inconclusive,receipts| (json!({"status":"inconclusive","phase":reason.phase,"resource":reason.resource}),Accounted {value:req.exhausted(reason),receipts});
        let (capture,r)=match req.prepare(&p.corpus,&p.keys,&(&l).into()).unwrap() {
            RequestPreparation::Inconclusive {reason,receipts}=>exhausted(reason,receipts),
            RequestPreparation::Complete(g)=>{
                let g=g.admit(&(&l).into()).unwrap();
                match FreshSession.verify(&g,&(&l).into()).unwrap() {
                    LocalCheckOutcome::Inconclusive {reason,receipts}=>exhausted(reason,receipts),
                    LocalCheckOutcome::Complete(r)=>(captured_report(&r.checked.verification,&Names{keys:&p.keys}),r.checked.results),
                }
            }
        };
        json!({"source":source,"max_work":max_work,"fixtures":fixtures,"captured_result":capture,
            "neutral_result":format!("{:?}",r.value),"receipts":budget_evidence::receipt_capture(&r.receipts)})
    }).collect();
    json!({"schema":1,"cases":rows})
}
#[test]
#[ignore = "initial local-execution capture only; later changes require an explicit reviewed delta"]
fn capture_initial_local_reference() {
    println!("LOCAL_6B1A_REFERENCE={}", local_reference());
}
#[test]
#[ignore = "manual local execution timing; run alone in release"]
fn measure_local_workload_families() {
    let mut workloads = Vec::new();
    for family in ["duplicates", "distinct_literals", "helper_chain"] {
        for size in [1, 4, 16, 64] {
            let source = workload(family, size);
            workloads.push((family.to_string(), size, source.clone(), false));
            workloads.push((
                format!("query_{family}"),
                size,
                format!("{source}s0 <- i1; s1 <- i2; s2 <- i3; s3 <- i0;"),
                true,
            ));
        }
    }
    let (_, wide, _) = edit_cases()
        .into_iter()
        .find(|(n, _, _)| n == "wide_local_guard")
        .unwrap();
    workloads.push(("wide_overlap".into(), 16, wide, true));
    workloads.push((
        "mixed_completion".into(),
        1,
        "input i, j, k; slot a, b; a <- i; a <- j; b <- k when not available(b);".into(),
        true,
    ));
    let mut rows = Vec::new();
    for (family, size, source, queries) in workloads {
        let mut samples = Vec::new();
        let mut charges = Value::Null;
        let mut result = Value::Null;
        for sample in 0..6 {
            let (_, _, p) = lower(&source);
            let l = limits();
            let start = Instant::now();
            let req = request_evidence::request(&p, &l);
            let RequestPreparation::Complete(g) =
                req.prepare(&p.corpus, &p.keys, &(&l).into()).unwrap()
            else {
                panic!()
            };
            let preparation = start.elapsed();
            let start = Instant::now();
            let g = g.admit(&(&l).into()).unwrap();
            let admission = start.elapsed();
            let start = Instant::now();
            let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap()
            else {
                panic!()
            };
            let checking = start.elapsed();
            let start = Instant::now();
            let CheckOutcome::Complete(global) = g.verify(&(&l).into()).unwrap() else {
                panic!()
            };
            let global_checking = start.elapsed();
            assert_eq!(r.checked.results.value, global.results.value);
            assert_eq!(!r.queries.is_empty(), queries);
            if !queries {
                assert!(r.checked.verification.all_obligations_proved());
            }
            if sample > 0 {
                samples.push(json!({"preparation_ns":preparation.as_nanos(),"admission_ns":admission.as_nanos(),
                "checking_ns":checking.as_nanos(),"global_checking_ns":global_checking.as_nanos(),
                "keys_ns":(p.key_computation+g.key_computation()+r.metrics.keys).as_nanos(),"local_keys_ns":r.metrics.keys.as_nanos(),
                "evaluation_ns":r.metrics.evaluation.as_nanos(),"conversion_ns":r.metrics.conversion.as_nanos(),
                "property_ns":r.metrics.property.as_nanos(),"completion_ns":r.metrics.completion.as_nanos(),"finding_context_ns":r.metrics.finding_context.as_nanos(),
                "replay_ns":r.checked.verification.finding_metrics.replay.as_nanos(),"certification_ns":r.checked.verification.finding_metrics.certification.as_nanos(),
                "cone_atoms":r.metrics.cone_atoms,"unique_atoms":r.metrics.unique_atoms,"cone_inputs":r.metrics.cone_inputs,"queries":r.queries.len()}));
            }
            charges = budget_evidence::receipt_capture(&r.checked.results.receipts);
            result = captured_report(&r.checked.verification, &Names { keys: &p.keys });
        }
        rows.push(json!({"family":family,"size":size,"source":source,"samples":samples,"receipts":charges,"result":result}));
    }
    println!("LOCAL_6B1A_TIMINGS={}", json!({"rows":rows}));
}

#[test]
fn projected_keys_track_edits_and_keep_unrelated_cones_equal() {
    let capture = |source: &str| {
        let (_, _, p) = lower(source);
        let l = limits();
        let g = request_evidence::checked(&p, &l);
        let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap() else {
            panic!()
        };
        r.queries
    };
    for (name, before, after) in edit_cases() {
        if ![
            "comment",
            "numeric_alias",
            "wide_local_guard",
            "add_literal",
            "remove_literal",
            "insert_helper_before",
        ]
        .contains(&name.as_str())
        {
            continue;
        }
        let old = capture(&before);
        let new = capture(&after);
        let equal = old.iter().filter(|(k, v)| new.get(k) == Some(v)).count();
        match name.as_str() {
            "comment" | "numeric_alias" => assert_eq!(old, new, "{name}"),
            "wide_local_guard" => {
                assert_eq!(old.len(), 16);
                assert_eq!(equal, 15);
            }
            "add_literal" | "remove_literal" => {
                assert_eq!(equal, 0, "K changes must invalidate relevant domains")
            }
            "insert_helper_before" => assert!(
                equal > 0,
                "unrelated helper insertion must preserve an eligible query"
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
fn local_condition_storage_allowances_have_an_explicit_tight_limit_delta() {
    let source = format!(
        "input i, j; slot {};\n{}",
        (0..16)
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(", "),
        (0..16)
            .map(|i| format!("a{i} <- i; a{i} <- j;\n"))
            .collect::<String>()
    );
    let (_, _, p) = lower(&source);
    let l = Limits {
        max_condition_nodes: 64,
        ..limits()
    };
    let g = request_evidence::checked(&p, &l);
    let CheckOutcome::Complete(global) = g.verify(&(&l).into()).unwrap() else {
        panic!("global report unavailable")
    };
    let LocalCheckOutcome::Complete(local) = FreshSession.verify(&g, &(&l).into()).unwrap() else {
        panic!("local report unavailable")
    };
    let inconclusive = global
        .results
        .value
        .groups
        .values()
        .filter(|v| matches!(v, ScopedResult::Inconclusive(_)))
        .count();
    assert!(inconclusive > 0);
    assert_eq!(local.checked.results.value.groups.len(), 16);
    assert!(
        local
            .checked
            .results
            .value
            .groups
            .values()
            .all(|v| matches!(v, ScopedResult::Counterexample(..)))
    );
    let actual = json!({"source":source,"max_condition_nodes":64,"old":captured_report(&global.verification,&Names{keys:&p.keys}),"new":captured_report(&local.checked.verification,&Names{keys:&p.keys}),"old_inconclusive":inconclusive});
    let delta: Value = serde_json::from_str(include_str!("../../LOCAL-DELTA-6b.1a.json")).unwrap();
    assert_eq!(actual, delta["tight_limit_delta"]);
}

#[test]
fn frozen_local_reference_and_explicit_delta_are_exact() {
    let reference: Value =
        serde_json::from_str(include_str!("../../fixtures/LOCAL-6b.1a-REFERENCE.json")).unwrap();
    assert_eq!(local_reference(), reference);
    let old: Value = serde_json::from_str(include_str!(
        "../../../check/fixtures/BUDGETS-6a.2b-REFERENCE.json"
    ))
    .unwrap();
    let mut old = planner_evidence::adapted("fresh_reference", old);
    let delta: Value = serde_json::from_str(include_str!("../../LOCAL-DELTA-6b.1a.json")).unwrap();
    let entries = delta["entries"].as_array().unwrap();
    assert_eq!(entries.len(), 32);
    let mut seen = BTreeSet::new();
    for entry in entries {
        let pointer = entry["pointer"].as_str().unwrap();
        assert!(seen.insert(pointer));
        assert!(pointer.ends_with("/receipts")); // No frozen outcome, witness or reason delta.
        let slot = old.pointer_mut(pointer).unwrap();
        assert_eq!(*slot, entry["old"]);
        assert_ne!(entry["old"], entry["new"]);
        *slot = entry["new"].clone();
    }
    assert_eq!(old["cases"], reference["cases"]);
    let budgets = reference["cases"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|r| r["fixtures"].as_array().unwrap())
        .filter(|f| f.as_str().unwrap().starts_with("budget/"))
        .count();
    assert_eq!(budgets, 20);
}

#[test]
fn local_exhaustion_preserves_independent_scopes_and_canonical_receipts() {
    let source = "input i, j, k, l, m, n; slot a, z; a <- i; a <- j; z <- i when present(k) and present(l) and present(m) and present(n); z <- j when present(k) and present(l) and present(m) and present(n);";
    let (_, _, p) = lower(source);
    let l = Limits {
        max_condition_nodes: 64,
        ..limits()
    };
    let g = request_evidence::checked(&p, &l);
    let run = || {
        let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap() else {
            panic!()
        };
        r.checked.results
    };
    let (normal, trace) = denotate_check::test_support::with_test_schedule(false, run);
    let (reverse, _) = denotate_check::test_support::with_test_schedule(true, run);
    assert_eq!(normal, reverse);
    let groups: Vec<_> = normal.value.groups.values().collect();
    assert!(matches!(groups[0], ScopedResult::Counterexample(..)));
    assert!(matches!(groups[1], ScopedResult::Inconclusive(_)));
    let keys: Vec<_> = trace
        .into_iter()
        .filter_map(|k| {
            if let QueryKey::ConeEvaluation(key) = k {
                Some(key)
            } else {
                None
            }
        })
        .collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted);
    let total = normal.receipts.total().unwrap();
    assert_eq!(
        total
            .queries
            .iter()
            .filter(|k| **k == QueryKey::FindingContext)
            .count(),
        1
    );
    assert_eq!(
        total
            .queries
            .iter()
            .filter(|k| **k == QueryKey::ConeIndex)
            .count(),
        1
    );
}
