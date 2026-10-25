//! Local execution is compared with the unchanged global oracle on corpus programs.
use super::*;
#[path = "../../../../test-dsl/tests/support/corpus.rs"]
mod corpus;
use crate::FreshSession;
use denotate_test_dsl::{attribution::SourceView, presentation};

pub(super) fn query_inputs(source: &str) -> BTreeMap<LocalScope, LocalInput> {
    let (_, _, p) = lower(source);
    let l = limits();
    let g = request_evidence::checked(&p, &l);
    let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap() else {
        panic!()
    };
    r.queries.into_iter().map(|(k, q)| (k, q.input)).collect()
}

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
    let mut cached_session = crate::Session::default();
    for _ in 0..2 {
        let request = request_evidence::request(&p, &l);
        let RequestPreparation::Complete(cached_prepared) = cached_session
            .prepare(&request, &p.corpus, &p.keys, &(&l).into())
            .unwrap()
        else {
            panic!("cached preparation exhausted")
        };
        let cached_prepared = cached_prepared.admit(&(&l).into()).unwrap();
        let LocalCheckOutcome::Complete(cached) = cached_session
            .verify(&cached_prepared, &(&l).into())
            .unwrap()
        else {
            panic!("cached exhausted")
        };
        assert_eq!(cached.checked.results, local.checked.results);
        assert_eq!(
            render(&cached.checked.verification),
            render(&local.checked.verification)
        );
    }
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
fn local_scopes_preserve_regression_outcomes_and_current_diagnostics() {
    let cases = regression_cases();
    let sources = cases.iter().map(|r| r["source"].as_str().unwrap());
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
fn local_execution_matches_global_on_the_inputmapping_corpus() {
    let texts = corpus::texts();
    // The count is explicit so corpus coverage cannot silently shrink.
    assert_eq!(texts.len(), 39 + 84);
    for source in &texts {
        let doc = std::sync::Arc::new(Document::new(
            &mut syntax::parser().unwrap(),
            source.clone(),
            1,
            true,
        ));
        let frontend = denotate_test_dsl::analysis::prepare(
            &"file:///corpus.inputmapping".parse().unwrap(),
            1,
            doc,
            &mut denotate_test_dsl::lowering::incremental::Session::default(),
        )
        .unwrap();
        if frontend.program.is_none() {
            // Exact rejection diagnostics are pinned by the corpus expectations.
            assert!(!frontend.fast.is_empty(), "{source}");
        } else {
            compare(source);
        }
    }
}

#[test]
fn projected_keys_track_edits_and_keep_unrelated_cones_equal() {
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
        let old = query_inputs(&before);
        let new = query_inputs(&after);
        let equal = old.iter().filter(|(k, v)| new.get(k) == Some(v)).count();
        match name.as_str() {
            "comment" | "numeric_alias" => assert_eq!(old, new, "{name}"),
            "wide_local_guard" => {
                let changed: Vec<_> = old
                    .iter()
                    .filter(|(k, v)| new.get(k) != Some(v))
                    .map(|(k, _)| k)
                    .collect();
                assert!(!changed.is_empty() && equal > 0);
                for key in changed {
                    let LocalScope::Group(group) = key else {
                        panic!()
                    };
                    assert!(group.tuple.iter().any(|c| c.name.as_ref() == "s0"));
                }
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
fn independent_scopes_do_not_share_condition_storage_allowances() {
    let (_, source, _) = edit_cases()
        .into_iter()
        .find(|(name, _, _)| name == "wide_local_guard")
        .unwrap();
    let (_, _, p) = lower(&source);
    let ample = limits();
    let prepared = request_evidence::checked(&p, &ample);
    let LocalCheckOutcome::Complete(full) =
        FreshSession.verify(&prepared, &(&ample).into()).unwrap()
    else {
        panic!()
    };
    let peak = condition_storage_peak(&full.checked.results.receipts);
    let mut isolated = false;
    for nodes in 1..=peak {
        let l = Limits {
            max_condition_nodes: nodes,
            ..limits()
        };
        let g = request_evidence::checked(&p, &l);
        let CheckOutcome::Complete(global) = g.verify(&(&l).into()).unwrap() else {
            continue;
        };
        let LocalCheckOutcome::Complete(local) = FreshSession.verify(&g, &(&l).into()).unwrap()
        else {
            continue;
        };
        if global
            .results
            .value
            .groups
            .values()
            .any(|v| matches!(v, ScopedResult::Inconclusive(_)))
            && local
                .checked
                .results
                .value
                .groups
                .values()
                .all(|v| matches!(v, ScopedResult::Counterexample(..)))
        {
            assert_eq!(
                global.results.value.groups.keys().collect::<Vec<_>>(),
                local
                    .checked
                    .results
                    .value
                    .groups
                    .keys()
                    .collect::<Vec<_>>()
            );
            isolated = true;
            break;
        }
    }
    assert!(
        isolated,
        "independent scopes must receive independent allowances"
    );
}

#[test]
fn local_execution_preserves_semantic_regressions() {
    for row in regression_cases() {
        let source = row["source"].as_str().unwrap();
        let (_, _, p) = lower(source);
        let l = limits();
        let g = request_evidence::checked(&p, &l);
        let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap() else {
            panic!()
        };
        assert_eq!(
            semantic_outcomes(captured_report(
                &r.checked.verification,
                &Names { keys: &p.keys }
            )),
            row["expected"],
            "{source}"
        );
    }
}

#[test]
fn local_exhaustion_preserves_independent_scopes_and_canonical_receipts() {
    let source = "input i, j, k, l, m, n; slot a, z; a <- i; a <- j; z <- i when present(k) and present(l) and present(m) and present(n); z <- j when present(k) and present(l) and present(m) and present(n);";
    let (_, _, p) = lower(source);
    let ample = limits();
    let prepared = request_evidence::checked(&p, &ample);
    let LocalCheckOutcome::Complete(full) =
        FreshSession.verify(&prepared, &(&ample).into()).unwrap()
    else {
        panic!()
    };
    let peak = condition_storage_peak(&full.checked.results.receipts);
    let l = (1..=peak)
        .find_map(|nodes| {
            let l = Limits {
                max_condition_nodes: nodes,
                ..limits()
            };
            let g = request_evidence::checked(&p, &l);
            let LocalCheckOutcome::Complete(r) = FreshSession.verify(&g, &(&l).into()).unwrap()
            else {
                return None;
            };
            let groups: Vec<_> = r.checked.results.value.groups.values().collect();
            (matches!(groups[0], ScopedResult::Counterexample(..))
                && matches!(groups[1], ScopedResult::Inconclusive(_)))
            .then_some(l)
        })
        .expect("fixture must exercise partial exhaustion");
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
