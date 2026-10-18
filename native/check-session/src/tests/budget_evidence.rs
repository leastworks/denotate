//! Per-query budget, receipt-DAG and frozen fresh-reference acceptance.
use super::request_evidence::{checked, request};
use super::*;
use denotate_check::test_support::TestQueryRun as QueryRun;

fn run(text: &str, max_work: usize) -> (Value, Accounted<ScopedResults>) {
    let (_, _, p) = lower(text);
    let limits = Limits {
        max_work,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let req = request(&p, &limits);
    let exhausted = |reason: Inconclusive, receipts| {
        (
            json!({"status":"inconclusive","phase":reason.phase,"resource":reason.resource}),
            Accounted {
                value: req.exhausted(reason),
                receipts,
            },
        )
    };
    let g = match req.prepare(&p.corpus, &p.keys, &(&limits).into()).unwrap() {
        RequestPreparation::Complete(g) => g,
        RequestPreparation::Inconclusive { reason, receipts } => {
            return exhausted(reason, receipts);
        }
    };
    let g = g.admit(&(&limits).into()).unwrap();
    match g.verify(&(&limits).into()).unwrap() {
        CheckOutcome::Complete(r) => (
            captured_report(&r.verification, &Names { keys: &p.keys }),
            r.results,
        ),
        CheckOutcome::Inconclusive {
            reason, receipts, ..
        } => exhausted(reason, receipts),
    }
}
fn roots(receipts: &WorkReceipts) -> Vec<QueryKey> {
    receipts
        .entries()
        .filter_map(|(k, _)| {
            matches!(k, QueryKey::Certification(_) | QueryKey::Completion(_)).then_some(k.clone())
        })
        .collect()
}

#[test]
fn canonical_scopes_and_receipts_are_independent_of_query_scheduling() {
    let source = "input z, a, m; slot zz, aa, cycle_z, cycle_a; zz <- z; zz <- a when present(m); aa <- z; aa <- a; cycle_z <- z when not available(cycle_z); cycle_a <- a when not available(cycle_a);";
    let (a, trace) =
        denotate_check::test_support::with_test_schedule(false, || run(source, 20_000_000));
    let (b, reversed) =
        denotate_check::test_support::with_test_schedule(true, || run(source, 20_000_000));
    assert_eq!(a, b);
    assert_ne!(trace, reversed);
    for stage in [0, 1, 2, 3] {
        let keys: Vec<_> = trace
            .iter()
            .filter(|k| match stage {
                0 => matches!(k, QueryKey::Property(_)),
                1 => matches!(k, QueryKey::Witness(_)),
                2 => matches!(k, QueryKey::Completion(_)),
                _ => matches!(k, QueryKey::Certification(_)),
            })
            .collect();
        assert!(keys.len() >= 2);
        assert!(
            keys.windows(2).all(|w| w[0] < w[1]),
            "canonical stage {stage}"
        );
    }
    for (_, receipt) in a.1.receipts.entries() {
        assert_eq!(
            receipt.allowance,
            DeterministicLimits::from(&Limits::default())
        );
        assert_eq!(
            receipt.own.work,
            receipt.own.by_phase.values().sum::<usize>()
        );
    }
}

#[test]
fn per_query_exhaustion_keeps_finished_scopes_and_does_not_spend_other_allowances() {
    let source =
        "input i, j, k; slot a, z; a <- i; a <- j; z <- i when present(k); z <- j when present(k);";
    let (_, _, p) = lower(source);
    let ample = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let g = checked(&p, &ample);
    let CheckOutcome::Complete(full) = g.verify(&(&ample).into()).unwrap() else {
        panic!()
    };
    let witness: Vec<_> = full
        .results
        .receipts
        .entries()
        .filter_map(|(k, r)| matches!(k, QueryKey::Witness(_)).then_some(r.own.work))
        .collect();
    assert_eq!(witness.len(), 2);
    assert!(witness[0] < witness[1]);
    let limited = Limits {
        max_work: witness[0],
        ..ample.clone()
    };
    let meaning = g.program().symbolic(&ample).unwrap();
    let check = || {
        let mut receipts = full
            .results
            .receipts
            .required([QueryKey::Symbolic])
            .unwrap();
        let mut q = QueryRun {
            keys: &p.keys,
            ground: g.keys(),
            receipts: &mut receipts,
        };
        let report = meaning
            .verify_test_queries(&limited, &ample, &ample, Some(&mut q))
            .unwrap();
        assert!(matches!(
            report.groups[0].outcome,
            VerifiedOutcome::Counterexample(_)
        ));
        assert!(matches!(
            report.groups[1].outcome,
            VerifiedOutcome::Inconclusive(_)
        ));
        (captured_report(&report, &Names { keys: &p.keys }), receipts)
    };
    let (normal, _) = denotate_check::test_support::with_test_schedule(false, check);
    let (reverse, _) = denotate_check::test_support::with_test_schedule(true, check);
    assert_eq!(normal, reverse);
    let receipts = &normal.1;
    assert!(
        receipts
            .entries()
            .filter(|(k, _)| matches!(k, QueryKey::Witness(_)))
            .map(|(_, r)| r.own.work)
            .sum::<usize>()
            > limited.max_work
    );
    assert!(receipts.entries().any(|(_, r)| !r.own.exhausted.is_empty()));
}

#[test]
fn reviewed_per_query_allowance_delta_is_separate_from_planner_changes() {
    let delta: Value =
        serde_json::from_str(include_str!("../../../check/BUDGET-DELTA-6a.2b.json")).unwrap();
    let probe = &delta["probe"];
    let (_, _, p) = lower(probe["source"].as_str().unwrap());
    let ample = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    // Isolate the verification-stage split. A whole-request 100-unit limit
    // could stop in preparation and would not exercise the reviewed delta.
    let g = checked(&p, &ample);
    let CheckOutcome::Complete(full) = g.verify(&(&ample).into()).unwrap() else {
        panic!()
    };
    let statuses = |report: &Verification<'_>| {
        json!(
            report
                .groups
                .iter()
                .map(|group| match group.outcome {
                    VerifiedOutcome::Counterexample(_) => "Counterexample",
                    VerifiedOutcome::Inconclusive(_) => "Inconclusive",
                    VerifiedOutcome::Proved => "Proved",
                    VerifiedOutcome::Unsupported => "Unsupported",
                })
                .collect::<Vec<_>>()
        )
    };
    let meaning = g.program().symbolic(&ample).unwrap();
    let old_default = meaning.verify_at_most_one(&ample).unwrap();
    assert_eq!(statuses(&old_default), probe["default_outcomes_both"]);
    let names = Names { keys: &p.keys };
    let expected = captured_report(&full.verification, &names);
    assert_eq!(captured_report(&old_default, &names), expected);

    let limited = Limits {
        max_work: probe["verification_max_work"].as_u64().unwrap() as usize,
        ..ample.clone()
    };
    let old = meaning
        .verify_with_phase_limits(&limited, &ample, &ample)
        .unwrap();
    assert_eq!(statuses(&old), probe["old_outcomes"]);
    let VerifiedOutcome::Inconclusive(reason) = &old.groups[1].outcome else {
        panic!()
    };
    assert_eq!(json!(reason.resource), probe["old_exhausted_resource"]);

    let check = || {
        let mut receipts = full
            .results
            .receipts
            .required([QueryKey::Symbolic])
            .unwrap();
        let mut queries = QueryRun {
            keys: &p.keys,
            ground: g.keys(),
            receipts: &mut receipts,
        };
        let new = meaning
            .verify_test_queries(&limited, &ample, &ample, Some(&mut queries))
            .unwrap();
        assert_eq!(statuses(&new), probe["new_outcomes"]);
        assert_eq!(captured_report(&new, &names), expected);
        let witness_work: Vec<_> = receipts
            .entries()
            .filter_map(|(k, r)| matches!(k, QueryKey::Witness(_)).then_some(r.own.work))
            .collect();
        assert_eq!(json!(witness_work), probe["witness_work"]);
        receipts
    };
    let (normal, _) = denotate_check::test_support::with_test_schedule(false, check);
    let (reversed, _) = denotate_check::test_support::with_test_schedule(true, check);
    assert_eq!(normal, reversed);
}

#[test]
fn receipt_aggregation_counts_shared_work_once_and_rejects_invalidated_children() {
    let (_, output) = run(
        "input i, j; slot a, b; a <- i; a <- j; b <- i; b <- j;",
        20_000_000,
    );
    let roots = roots(&output.receipts);
    let cold = output.receipts.required(roots.clone()).unwrap();
    let expected = cold.total().unwrap();
    let mut warm = WorkReceipts::default();
    let entries: Vec<_> = cold
        .entries()
        .map(|(k, r)| (k.clone(), r.clone()))
        .collect();
    // Simulated cache hits insert receipts in reverse arrival order. No production
    // semantic cache exists yet; receipt residency is independent of value residency.
    for (key, receipt) in entries.iter().rev() {
        warm.record(key.clone(), receipt.clone()).unwrap();
    }
    let repeated = roots.iter().cloned().chain(roots.iter().cloned());
    assert_eq!(warm.aggregate(repeated).unwrap(), expected);
    assert_eq!(warm.required(roots.clone()).unwrap(), cold);
    assert_eq!(
        expected
            .queries
            .iter()
            .filter(|k| **k == QueryKey::Symbolic)
            .count(),
        1
    );
    drop(output); // All query value/presentation ownership can disappear.
    assert_eq!(warm.aggregate(roots.clone()).unwrap(), expected);
    let mut current = warm.get(&QueryKey::Preparation).unwrap().clone();
    warm.invalidate(&QueryKey::Preparation);
    assert!(matches!(
        warm.aggregate(roots.clone()),
        Err(ReceiptError::Missing(QueryKey::Preparation))
    ));
    current.own.work += 1;
    *current
        .own
        .by_phase
        .entry("new input validation".into())
        .or_default() += 1;
    warm.record(QueryKey::Preparation, current).unwrap();
    assert_eq!(warm.aggregate(roots).unwrap().work, expected.work + 1);
    assert_ne!(
        warm, cold,
        "parent dependencies resolve current child receipts"
    );
}

#[test]
fn equal_semantic_outputs_cannot_hide_changed_receipts() {
    let source =
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;";
    let (_, before) = run(source, 20_000_000);
    let (_, after) = run(
        &format!("{source} a <- i when input_value(i) is 1;"),
        20_000_000,
    );
    assert_eq!(before.value, after.value);
    assert_ne!(before.receipts, after.receipts);
    assert_ne!(before, after);
}

#[test]
fn receipt_graph_rejects_missing_cycles_conflicts_and_overflow() {
    let (_, output) = run("input i; slot a; a <- i;", 20_000_000);
    let mut ledger = output.receipts.clone();
    let mut receipt = ledger.get(&QueryKey::Preparation).unwrap().clone();
    receipt.dependencies.insert(QueryKey::Symbolic);
    assert!(matches!(
        ledger.record(QueryKey::Preparation, receipt.clone()),
        Err(ReceiptError::Conflicting(_))
    ));
    ledger.invalidate(&QueryKey::Preparation);
    ledger.record(QueryKey::Preparation, receipt).unwrap();
    assert!(matches!(ledger.total(), Err(ReceiptError::Cycle(_))));
    let mut large = output.receipts.get(&QueryKey::Preparation).unwrap().clone();
    large.allowance.max_work = usize::MAX;
    large.own.work = usize::MAX;
    large.own.by_phase = BTreeMap::from([("large".into(), usize::MAX)]);
    let mut ledger = WorkReceipts::default();
    ledger.record(QueryKey::Preparation, large.clone()).unwrap();
    ledger.record(QueryKey::Admission, large).unwrap();
    assert_eq!(ledger.total(), Err(ReceiptError::Overflow));
}

#[test]
fn interrupted_queries_return_no_accounted_result_and_recovery_is_fresh() {
    let (_, _, p) = lower("input i, j; slot a; a <- i; a <- j;");
    let limits = Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let g = checked(&p, &limits);
    let CheckOutcome::Complete(before) = g.verify(&(&limits).into()).unwrap() else {
        panic!()
    };
    let interrupted = OperationalLimits {
        cancellation: Cancellation::default(),
        timeout: Duration::ZERO,
    };
    assert!(matches!(
        g.verify(&interrupted),
        Err(CheckError::Deadline { .. })
    ));
    let interrupted = OperationalLimits::from(&limits);
    interrupted.cancellation.cancel();
    assert!(matches!(g.verify(&interrupted), Err(CheckError::Cancelled)));
    let CheckOutcome::Complete(after) = g
        .verify(
            &(&Limits {
                timeout: Duration::from_secs(60),
                ..Limits::default()
            })
                .into(),
        )
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(before.results, after.results);
}

pub(super) fn receipt_capture(receipts: &WorkReceipts) -> Value {
    let resources = |map: &BTreeMap<ResourceKey, usize>| {
        map.iter()
            .map(|(k, v)| (format!("{}/{}", k.phase, k.resource), *v))
            .collect::<BTreeMap<_, _>>()
    };
    let entries:Vec<_>=receipts.entries().map(|(key,r)|json!({
        "query":format!("{key:?}"),"dependencies":r.dependencies.iter().map(|k|format!("{k:?}")).collect::<Vec<_>>(),
        "allowance":format!("{:?}",r.allowance),"work":r.own.work,"by_phase":r.own.by_phase,
        "resource_peaks":resources(&r.own.resource_peaks),"rejected_work":r.own.rejected_work,
        "exhausted":r.own.exhausted.iter().map(|k|format!("{}/{}",k.phase,k.resource)).collect::<Vec<_>>()
    })).collect();
    let total = receipts.total().unwrap();
    json!({"queries":entries,"aggregate":{"work":total.work,"by_phase":total.by_phase,"resource_totals":resources(&total.resource_totals),"rejected_work":total.rejected_work}})
}
pub(super) fn fresh_reference() -> Value {
    let old: Value =
        serde_json::from_str(include_str!("../../../check/IDENTITIES-6a.1.json")).unwrap();
    let mut cases = BTreeMap::<(String, usize), Vec<String>>::new();
    for row in old["witnesses"].as_array().unwrap() {
        if row["invalid_source"] == true {
            continue;
        }
        cases
            .entry((
                row["source"].as_str().unwrap().into(),
                row["max_work"].as_u64().unwrap() as usize,
            ))
            .or_default()
            .push(row["fixture"].as_str().unwrap().into());
    }
    let cases:Vec<_>=cases.into_iter().map(|((source,max_work),fixtures)| {
        let (captured,accounted)=run(&source,max_work);
        json!({"source":source,"max_work":max_work,"fixtures":fixtures,"captured_result":captured,
            "neutral_result":format!("{:?}",accounted.value),"receipts":receipt_capture(&accounted.receipts)})
    }).collect();
    json!({"schema":1,"note":"Initial 6a.2b fresh reference for 6b: all distinct valid source/limit pairs from the unchanged 6a.1 report. Debug text pins the owned neutral contract for tests; it is not a persistence format. No timings. Never regenerate to accept planner, budget, or cache drift; review explicit deltas.","cases":cases})
}

#[test]
fn fresh_receipts_match_the_6a2b_reference() {
    let expected: Value = serde_json::from_str(include_str!(
        "../../../check/fixtures/BUDGETS-6a.2b-REFERENCE.json"
    ))
    .unwrap();
    assert_eq!(
        fresh_reference(),
        super::planner_evidence::adapted("fresh_reference", expected)
    );
}

#[test]
#[ignore = "initial 6a.2b receipt reference only; never regenerate to accept later drift"]
fn capture_initial_budget_reference() {
    println!("SLICE_6A2B_REFERENCE={}", fresh_reference());
}
