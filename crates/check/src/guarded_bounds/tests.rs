use super::*;
use crate::{
    admission_progress::AdmissionReporter,
    admission_skips::{Attempt, Attempts},
    test_support::rewrites::{atom, rel, rule},
};
use denotate_ir::*;

fn summaries(
    p: &GroundProgram,
    m: &SymbolicMeaning<'_>,
    l: &Limits,
) -> BTreeMap<GroundRuleId, ProducerSummary> {
    let ctx = m.context();
    p.rules()
        .map(|rule| {
            let mut condition = ctx.true_condition();
            let mut settled = Vec::new();
            let mut exact = true;
            for literal in &rule.body {
                match m.fact(&literal.term.atom).unwrap() {
                    SymbolicFact::Settled(mut value) => {
                        if literal.polarity == Polarity::Negative {
                            value = ctx.not(&value, l).unwrap();
                        }
                        condition = ctx.and(&condition, &value, l).unwrap();
                        settled.push(SettledPremise {
                            literal: literal.clone(),
                            condition: value,
                        });
                    }
                    SymbolicFact::Blocked(_) => exact = false,
                    _ => panic!(),
                }
            }
            (
                rule.id,
                ProducerSummary {
                    rule: rule.clone(),
                    settled,
                    condition,
                    exact,
                },
            )
        })
        .collect()
}

#[test]
fn restricted_cone_bounds_equal_full_relaxed_bounds_masked_by_guard_and_worlds() {
    let l = Limits::default();
    let mut seed = 973u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for case in 0..96 {
        let mut c = Corpus::new();
        let inputs = [rel(&mut c, "i", true), rel(&mut c, "j", true)];
        let derived = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "c", false),
        ];
        // Always include a recursive component; add mixed positive/negative
        // and exact producers. The independent bound comparison is exhaustive
        // over Boolean functions, not selected observations.
        for i in 0..3 {
            rule(
                &mut c,
                derived[i],
                &[(derived[(i + 1) % 3], true), (inputs[i % 2], i % 2 == 0)],
            );
        }
        let all: Vec<_> = inputs.into_iter().chain(derived).collect();
        for _ in 0..6 {
            let body = (0..1 + random() % 3)
                .map(|_| (all[random() % all.len()], random() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, derived[random() % 3], &body);
        }
        let mut p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        if case % 2 == 0 {
            // Exercise a nontrivial W independently of the candidate guard.
            let ctx = p.condition_context(&l).unwrap();
            p.assumption_condition = Some(
                ctx.not(&ctx.input(&atom(inputs[0]), &l).unwrap(), &l)
                    .unwrap(),
            );
        }
        let m = p.symbolic(&l).unwrap();
        let summaries = summaries(&p, &m, &l);
        let mut index = BTreeMap::<_, Vec<_>>::new();
        for s in summaries.values() {
            index.entry(&s.rule.head.atom).or_default().push(s.rule.id);
        }
        for candidate in summaries.values().filter(|s| !s.exact) {
            let component = p.component_for(&candidate.rule.head.atom).unwrap();
            for literal in &candidate.rule.body {
                if p.component_for(&literal.term.atom).unwrap().id != component.id {
                    continue;
                }
                let mut budget = Budget::new(&l);
                let mut retained = 0;
                let full = crate::upper_bounds::compute_relaxed(
                    &p,
                    component,
                    &summaries,
                    m.context(),
                    &mut retained,
                    &mut budget,
                    None,
                    true,
                    Some(candidate.rule.id),
                )
                .unwrap();
                let cone = prepare(
                    &p,
                    component,
                    candidate,
                    &literal.term.atom,
                    &summaries,
                    &index,
                    m.context(),
                    &mut retained,
                    &mut budget,
                )
                .unwrap();
                let restricted =
                    compute(&cone, m.context(), &mut retained, &mut budget, None).unwrap();
                for (atom, bound) in &restricted.conditions {
                    let expected = m
                        .context()
                        .and(&full.conditions[atom], &cone.domain, &l)
                        .unwrap();
                    assert!(
                        m.context()
                            .apply(
                                &expected,
                                bound,
                                biodivine_lib_bdd::op_function::xor,
                                &mut budget
                            )
                            .unwrap()
                            .is_false(),
                        "case {case}"
                    );
                }
                assert_eq!(retained, full.nodes() + restricted.nodes());
            }
        }
    }
}

fn wide(n: usize) -> (Corpus, RuleId, RuleId) {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let gate = rel(&mut c, "gate", true);
    let priority = rel(&mut c, "priority", true);
    let b = rel(&mut c, "booked", false);
    let f = rel(&mut c, "fails", false);
    let a = rel(&mut c, "claim", false);
    let i = rel(&mut c, "inspected", false);
    let h = rel(&mut c, "held", false);
    let clear = rel(&mut c, "cleared", false);
    let xs: Vec<_> = (0..n)
        .map(|j| rel(&mut c, &format!("p{j}"), true))
        .collect();
    let ys: Vec<_> = (0..n)
        .map(|j| rel(&mut c, &format!("r{j}"), true))
        .collect();
    for (x, y) in xs.into_iter().zip(ys) {
        rule(
            &mut c,
            b,
            &[(kind, false), (x, false), (y, false), (clear, false)],
        );
    }
    let broad = rule(&mut c, f, &[(gate, false), (b, true)]);
    let narrow = rule(&mut c, a, &[(kind, true), (f, true)]);
    rule(&mut c, i, &[(kind, false)]);
    rule(&mut c, i, &[(a, false)]);
    rule(&mut c, h, &[(priority, false), (i, false)]);
    rule(&mut c, clear, &[(gate, false), (h, true)]);
    (c, broad, narrow)
}

#[test]
fn broad_failure_never_suppresses_a_smaller_guard_cone_and_storage_is_released() {
    let (c, broad, narrow) = wide(9);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let m = p.symbolic(&l).unwrap();
    let summaries = summaries(&p, &m, &l);
    let mut index = BTreeMap::<_, Vec<_>>::new();
    for s in summaries.values() {
        index.entry(&s.rule.head.atom).or_default().push(s.rule.id);
    }
    let l = Limits {
        max_bdd_nodes: 128,
        ..l
    };
    let mut budget = Budget::new(&l);
    let mut attempts = Attempts::default();
    let progress = AdmissionReporter::new(None);
    let mut retained = 0;
    for (source, success) in [(broad, false), (narrow, true)] {
        let candidate = summaries
            .values()
            .find(|s| s.rule.source == source)
            .unwrap();
        let component = p.component_for(&candidate.rule.head.atom).unwrap();
        let literal = candidate
            .rule
            .body
            .iter()
            .find(|l| {
                l.polarity == Polarity::Negative
                    && matches!(m.fact(&l.term.atom).unwrap(), SymbolicFact::Blocked(_))
            })
            .unwrap();
        let cone = prepare(
            &p,
            component,
            candidate,
            &literal.term.atom,
            &summaries,
            &index,
            m.context(),
            &mut retained,
            &mut budget,
        )
        .unwrap();
        let result = attempts
            .run(
                Attempt::GuardedBounds(candidate.rule.id, literal.term.occurrence),
                &candidate.rule.head.atom,
                &p,
                &mut retained,
                &mut budget,
                &progress,
                |retained, budget| compute(&cone, m.context(), retained, budget, None),
            )
            .unwrap();
        assert_eq!(result.is_some(), success);
        assert_eq!(
            retained,
            result.as_ref().map_or_else(|| cone.nodes(), |r| r.nodes())
        );
        if let Some(bounds) = result {
            assert!(
                p.settle_guarded(
                    candidate,
                    literal,
                    &m,
                    &bounds,
                    &mut retained,
                    &mut budget,
                    &progress
                )
                .unwrap()
                .is_some()
            );
        }
        retained = 0;
    }
    // Preprocessing storage exhaustion is local too, before a partial cone
    // can enter the cache. An unrelated tiny attempt can still run afterward.
    let candidate = summaries.values().find(|s| s.rule.source == broad).unwrap();
    let literal = candidate
        .rule
        .body
        .iter()
        .find(|l| {
            l.polarity == Polarity::Negative
                && matches!(m.fact(&l.term.atom).unwrap(), SymbolicFact::Blocked(_))
        })
        .unwrap();
    let small = Limits {
        max_condition_nodes: 10,
        ..l
    };
    let mut budget = Budget::new(&small);
    let mut attempts = Attempts::default();
    let result = attempts
        .run(
            Attempt::GuardedCone(candidate.rule.id, literal.term.occurrence),
            &candidate.rule.head.atom,
            &p,
            &mut retained,
            &mut budget,
            &progress,
            |retained, budget| {
                prepare(
                    &p,
                    p.component_for(&candidate.rule.head.atom).unwrap(),
                    candidate,
                    &literal.term.atom,
                    &summaries,
                    &index,
                    m.context(),
                    retained,
                    budget,
                )
            },
        )
        .unwrap();
    assert!(result.is_none());
    assert_eq!(retained, 0);
    assert!(
        attempts
            .run(
                Attempt::GuardedBounds(candidate.rule.id, literal.term.occurrence),
                &candidate.rule.head.atom,
                &p,
                &mut retained,
                &mut budget,
                &progress,
                |retained, budget| {
                    *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
                    Ok(())
                }
            )
            .unwrap()
            .is_some()
    );
}
#[test]
fn identical_outside_head_cones_reuse_bounds_without_leaking_retention() {
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let booked = rel(&mut c, "booked", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, booked, &[(kind, false), (a, false), (b, false)]);
    rule(&mut c, a, &[(kind, true), (booked, true)]);
    rule(&mut c, b, &[(kind, true), (booked, true)]);
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let m = p.symbolic(&l).unwrap();
    let summaries = summaries(&p, &m, &l);
    let events = std::cell::RefCell::new(Vec::new());
    let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
    let progress = AdmissionReporter::new(Some(&observer));
    let mut retained = 0;
    let proofs = p
        .guarded_settlements(
            &m,
            &summaries,
            &summaries.keys().copied().collect(),
            &mut retained,
            &mut Budget::new(&l),
            &progress,
            &mut Attempts::default(),
        )
        .unwrap();
    assert!(proofs.is_empty()); // constant premises stay for removal/discharge
    assert_eq!(
        retained, 0,
        "the invocation cache must release every retained node"
    );
    assert!(events.borrow().iter().any(|e| {
        e.guarded
            .as_ref()
            .is_some_and(|g| g.reused && g.state == "completed")
    }));
    assert!(
        events
            .borrow()
            .iter()
            .any(|e| e.attempts.values().any(|a| a.reused_result > 0))
    );
    // Optional retention must yield when there is room for either cone, but not
    // both at once. Search the boundary rather than pinning a storage budget.
    let targets = summaries
        .values()
        .filter(|s| s.rule.head.atom != atom(booked))
        .map(|s| s.rule.id)
        .collect();
    let mut exercised = false;
    for cap in 1..200 {
        let limits = Limits {
            max_condition_nodes: cap,
            ..l.clone()
        };
        let events = std::cell::RefCell::new(Vec::new());
        let observer = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
        let reporter = AdmissionReporter::new(Some(&observer));
        let mut retained = 0;
        let result = p.guarded_settlements(
            &m,
            &summaries,
            &targets,
            &mut retained,
            &mut Budget::new(&limits),
            &reporter,
            &mut Attempts::default(),
        );
        if result.is_err() {
            continue;
        }
        assert_eq!(retained, 0);
        let events = events.borrow();
        if events.iter().any(|e| {
            e.attempts
                .get(&AdmissionAttemptKind::GuardedBounds)
                .is_some_and(|a| a.completed == 2 && a.reused_result == 0)
        }) {
            assert!(events.iter().all(|e| e.skipped.is_none()));
            exercised = true;
            break;
        }
    }
    assert!(
        exercised,
        "both candidates must fit by evicting the optional cache"
    );
}
