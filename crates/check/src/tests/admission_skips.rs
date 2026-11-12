use super::rewrites::{atom, compare, rel, rule, subsets, supported_models};
use crate::{limits::Budget, *};
use denotate_ir::*;
use std::cell::RefCell;

fn admit(raw: &GroundProgram, limits: &Limits) -> (GroundProgram, Vec<AdmissionProgress>) {
    let events = RefCell::new(Vec::new());
    let p = raw
        .clone()
        .admit_observed(
            &mut Budget::new(limits),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    (p, events.into_inner())
}
fn sound(c: &Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(p, &p.rules().cloned().collect::<Vec<_>>(), &world)
        );
    }
}
fn wide(unrelated: bool) -> (Corpus, RelationId) {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let inputs: Vec<_> = (0..4)
        .map(|i| rel(&mut c, &format!("i{i}"), true))
        .collect();
    let out = rel(&mut c, "wide", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    for i in &inputs {
        rule(&mut c, out, &[(*i, false)]);
    }
    let another = rel(&mut c, "another_wide", false);
    for i in inputs {
        rule(&mut c, another, &[(i, false)]);
    }
    rule(&mut c, another, &[(out, false)]);
    if unrelated {
        let u = rel(&mut c, "u", false);
        let v = rel(&mut c, "v", false);
        rule(&mut c, out, &[(u, false)]);
        rule(&mut c, u, &[(v, true)]);
        rule(&mut c, v, &[(u, true)]);
    } else {
        rule(&mut c, out, &[(x, false)]);
    }
    rule(&mut c, x, &[(t, false), (y, true)]);
    rule(&mut c, y, &[(t, true), (x, true)]);
    (c, out)
}

#[test]
fn admission_skips_wide_coverage_and_finishes_independent_proofs() {
    for unrelated in [false, true] {
        let (c, out) = wide(unrelated);
        let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let mut exercised = false;
        for tasks in 0..16 {
            let limits = Limits {
                max_bdd_tasks: tasks,
                ..Limits::default()
            };
            let (p, events) = admit(&raw, &limits);
            sound(&c, &p);
            let skips: Vec<_> = events
                .iter()
                .filter_map(|e| e.skipped.as_ref())
                .filter(|s| s.kind == AdmissionAttemptKind::Coverage && s.head == atom(out))
                .collect();
            if !skips.is_empty() && p.admission_limit().is_none() && p.rewrite_proofs().count() > 0
            {
                exercised = true;
                assert!(
                    events
                        .iter()
                        .filter(|e| e
                            .skipped
                            .as_ref()
                            .is_some_and(|s| s.kind == AdmissionAttemptKind::Coverage))
                        .count()
                        >= 2
                );
                assert_eq!(
                    skips.len(),
                    1,
                    "unchanged coverage is not retried after another component commits"
                );
                assert_eq!(p.is_admitted(), !unrelated);
                assert!(events.last().unwrap().failure.is_none());
                if unrelated {
                    assert!(p.admission_skips().any(|s| s.head == atom(out)));
                    let report = p
                        .symbolic(&Limits::default())
                        .unwrap()
                        .verify_at_most_one(&Limits::default())
                        .unwrap();
                    assert!(
                        report
                            .unresolved
                            .iter()
                            .all(|r| r.admission_skips.is_empty()
                                && r.outcome == RegionOutcome::Unsupported)
                    );
                }
            }
        }
        assert!(exercised);
    }
}

#[test]
fn admission_skips_one_removal_check_and_commits_another_for_the_same_head() {
    let mut c = Corpus::new();
    let inputs: Vec<_> = ["p", "q", "r", "s"]
        .iter()
        .map(|n| rel(&mut c, n, true))
        .collect();
    let [p, q, r, s] = inputs.as_slice() else {
        unreachable!()
    };
    let out = rel(&mut c, "out", false);
    let u = rel(&mut c, "u", false);
    let v = rel(&mut c, "v", false);
    rule(&mut c, u, &[(v, true)]);
    rule(&mut c, v, &[(u, true)]);
    rule(&mut c, out, &[(*p, false)]);
    rule(&mut c, out, &[(*r, false)]);
    let hard = rule(&mut c, out, &[(*q, false), (*s, false), (u, false)]);
    let easy = rule(&mut c, out, &[(*p, false), (u, false)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut exercised = false;
    for bound in 0..16 {
        let (result, events) = admit(
            &raw,
            &Limits {
                max_bdd_tasks: bound,
                ..Limits::default()
            },
        );
        sound(&c, &result);
        if result.admission_limit().is_none()
            && events.iter().filter_map(|e| e.skipped.as_ref()).any(|s| {
                s.kind == AdmissionAttemptKind::Removal
                    && s.rule
                        .is_some_and(|r| raw.original_rule(r).unwrap().source == hard)
            })
            && result.rewrite_proofs().any(|p| {
                p.kind == RewriteKind::RedundantProducer && p.candidate.rule.source == easy
            })
        {
            exercised = true;
            assert!(result.rules().any(|r| r.source == hard));
            assert!(!result.rules().any(|r| r.source == easy));
        }
    }
    assert!(exercised);
}

#[test]
fn admission_partial_discharge_batches_preserve_supported_and_stable_models() {
    let mut c = Corpus::new();
    let inputs: Vec<_> = ["p", "q", "r", "s"]
        .iter()
        .map(|n| rel(&mut c, n, true))
        .collect();
    let [p, q, r, s] = inputs.as_slice() else {
        unreachable!()
    };
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "d", false);
    rule(&mut c, a, &[(*p, false), (*q, false), (b, true), (d, true)]);
    rule(&mut c, b, &[(*p, true), (a, true)]);
    rule(&mut c, d, &[(*r, false), (*s, false), (a, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut partial = [false; 2];
    for node_limit in [false, true] {
        for bound in 0..24 {
            let limits = if node_limit {
                Limits {
                    max_bdd_nodes: bound,
                    ..Limits::default()
                }
            } else {
                Limits {
                    max_bdd_tasks: bound,
                    ..Limits::default()
                }
            };
            let (result, events) = admit(&raw, &limits);
            sound(&c, &result);
            partial[usize::from(node_limit)] |= result.admission_limit().is_none()
                && result
                    .rewrite_proofs()
                    .any(|p| matches!(p.kind, RewriteKind::Discharge { .. }))
                && events.iter().any(|e| {
                    e.skipped
                        .as_ref()
                        .is_some_and(|s| s.kind == AdmissionAttemptKind::Discharge)
                });
        }
    }
    assert!(
        partial.into_iter().all(|exercised| exercised),
        "exercise task and node failures alongside a successful discharge in the original SCC"
    );
}

#[test]
fn admission_skips_failed_component_bounds_without_losing_independent_discharge() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let inputs: Vec<_> = (0..4)
        .map(|i| rel(&mut c, &format!("i{i}"), true))
        .collect();
    let wide = rel(&mut c, "wide", false);
    for i in inputs {
        rule(&mut c, wide, &[(i, false), (wide, true)]);
    }
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(t, false), (b, true)]);
    rule(&mut c, b, &[(t, true), (a, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut exercised = false;
    for bound in 0..16 {
        let (result, events) = admit(
            &raw,
            &Limits {
                max_bdd_tasks: bound,
                ..Limits::default()
            },
        );
        sound(&c, &result);
        if result.admission_limit().is_none()
            && result.rewrite_proofs().count() > 0
            && events.iter().any(|e| {
                e.skipped
                    .as_ref()
                    .is_some_and(|s| s.kind == AdmissionAttemptKind::UpperBounds)
            })
        {
            exercised = true;
            let component = result.component_for(&atom(wide)).unwrap();
            assert!(
                result
                    .admission_skips_for(component)
                    .any(|s| s.kind == AdmissionAttemptKind::UpperBounds)
            );
            assert!(
                result
                    .admission_skips_for(result.component_for(&atom(a)).unwrap())
                    .next()
                    .is_none()
            );
        }
    }
    assert!(exercised);
}

#[test]
fn admission_retries_discharge_when_another_heads_external_premise_settles() {
    let mut c = Corpus::new();
    let inputs: Vec<_> = ["p", "q", "r", "s", "t"]
        .iter()
        .map(|n| rel(&mut c, n, true))
        .collect();
    let [p, q, r, s, t] = inputs.as_slice() else {
        unreachable!()
    };
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    let ar = rule(&mut c, a, &[(*p, false), (*q, false), (b, true)]);
    rule(&mut c, b, &[(*r, false), (*s, false), (x, true), (a, true)]);
    rule(&mut c, b, &[(*t, false), (x, true), (a, true)]);
    rule(&mut c, x, &[(*p, false), (y, true)]);
    rule(&mut c, y, &[(*p, true), (x, true)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut retried = false;
    for bound in 0..32 {
        let (result, events) = admit(
            &raw,
            &Limits {
                max_bdd_tasks: bound,
                ..Limits::default()
            },
        );
        sound(&c, &result);
        let skipped = events.iter().filter_map(|e| e.skipped.as_ref()).any(|s| {
            s.kind == AdmissionAttemptKind::Discharge
                && s.rule
                    .is_some_and(|id| raw.original_rule(id).unwrap().source == ar)
        });
        if skipped
            && result.rewrite_proofs().any(|p| {
                p.candidate.rule.source == ar && matches!(p.kind, RewriteKind::Discharge { .. })
            })
        {
            retried = true;
            assert!(result.admission_limit().is_none());
            assert!(result.is_admitted());
        }
    }
    assert!(retried);
}
