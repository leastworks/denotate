use crate::{
    limits::Budget,
    test_support::rewrites::{compare, rel, rule, subsets, supported_models},
    *,
};
use denotate_ir::*;
use std::cell::RefCell;

fn run(
    raw: &GroundProgram,
    limits: &Limits,
    reuse: bool,
) -> (GroundProgram, Vec<AdmissionProgress>) {
    let events = RefCell::new(Vec::new());
    let observe = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
    let mut budget = Budget::new(limits);
    let p = if reuse {
        raw.clone().admit_observed(&mut budget, Some(&observe))
    } else {
        raw.clone()
            .admit_without_negative_reuse(&mut budget, Some(&observe))
    }
    .unwrap();
    (p, events.into_inner())
}

pub(super) fn equal(left: &GroundProgram, right: &GroundProgram) {
    assert_eq!(left.is_admitted(), right.is_admitted());
    assert_eq!(
        left.rules().collect::<Vec<_>>(),
        right.rules().collect::<Vec<_>>()
    );
    // Compare proof contents, excluding invocation-local graph/snapshot handles.
    let ctx = left.condition_context(&Limits::default()).unwrap();
    let condition = |a: &Condition, b: &Condition| {
        assert!(
            ctx.apply(
                a,
                b,
                biodivine_lib_bdd::op_function::xor,
                &mut Budget::new(&Limits::default())
            )
            .unwrap()
            .is_false()
        );
    };
    let summary = |a: &ProducerSummary, b: &ProducerSummary| {
        assert_eq!(a.rule, b.rule);
        assert_eq!(a.exact, b.exact);
        assert_eq!(a.settled.len(), b.settled.len());
        condition(&a.condition, &b.condition);
        for (a, b) in a.settled.iter().zip(&b.settled) {
            assert_eq!(a.literal, b.literal);
            condition(&a.condition, &b.condition);
        }
    };
    assert_eq!(
        left.rewrite_proofs().count(),
        right.rewrite_proofs().count()
    );
    for (a, b) in left.rewrite_proofs().zip(right.rewrite_proofs()) {
        assert_eq!(a.kind, b.kind);
        assert_eq!(a.candidate(), b.candidate());
        assert_eq!(a.direct_rules(), b.direct_rules());
        assert_eq!(
            std::mem::discriminant(&a.justification),
            std::mem::discriminant(&b.justification)
        );
        if let (Some(a), Some(b)) = (a.structural(), b.structural()) {
            assert_eq!(format!("{a:?}"), format!("{b:?}"));
        }
        if let (Some(a), Some(b)) = (a.bound_removal(), b.bound_removal()) {
            condition(&a.body_upper, &b.body_upper);
        }
        if let (Some(a), Some(b)) = (a.conditional(), b.conditional()) {
            summary(&a.candidate, &b.candidate);
            condition(&a.coverage, &b.coverage);
            assert_eq!(a.producers.len(), b.producers.len());
            for (a, b) in a.producers.iter().zip(&b.producers) {
                summary(a, b);
            }
            assert_eq!(a.upper_bounds.is_some(), b.upper_bounds.is_some());
            if let (Some(a), Some(b)) = (&a.upper_bounds, &b.upper_bounds) {
                assert_eq!(a.producers.len(), b.producers.len());
                for (a, b) in a.producers.iter().zip(&b.producers) {
                    summary(a, b);
                }
                for (a, b) in [
                    (&a.conditions, &b.conditions),
                    (&a.guarantees, &b.guarantees),
                ] {
                    assert_eq!(a.keys().collect::<Vec<_>>(), b.keys().collect::<Vec<_>>());
                    for (key, value) in a {
                        condition(value, &b[key]);
                    }
                }
            }
        }
    }
    assert_eq!(
        left.admission_skips().collect::<Vec<_>>(),
        right.admission_skips().collect::<Vec<_>>()
    );
    assert_eq!(left.admission_limit(), right.admission_limit());
    assert_eq!(left.downstream_incomplete(), right.downstream_incomplete());
}

fn sound(c: &Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(p, &p.rules().cloned().collect::<Vec<_>>(), &world),
        );
    }
}

fn multiround(count: usize) -> Corpus {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    for n in 0..count {
        let a = rel(&mut c, &format!("a{n}"), false);
        let b = rel(&mut c, &format!("b{n}"), false);
        rule(&mut c, a, &[(i, false)]);
        rule(&mut c, a, &[(b, true)]);
        rule(&mut c, b, &[(a, true)]);
    }
    let kept = rel(&mut c, "kept", false);
    let term = rel(&mut c, "term", false);
    rule(&mut c, kept, &[(j, false)]);
    rule(&mut c, kept, &[(j, true)]);
    rule(&mut c, kept, &[(term, false)]);
    rule(&mut c, term, &[(i, false), (kept, true)]);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    rule(&mut c, x, &[(j, false), (y, true)]);
    rule(&mut c, y, &[(j, true), (x, true)]);
    c
}

#[test]
fn unchanged_negatives_skip_their_coverage_and_bounds_across_rounds() {
    let c = multiround(12);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let (on, events) = run(&raw, &limits, true);
    let (off, _) = run(&raw, &limits, false);
    equal(&on, &off);
    assert!(!on.is_admitted());
    assert!(on.admission_limit().is_none());
    assert_eq!(on.admission_skips().count(), 0);
    assert!(
        on.rewrite_proofs()
            .any(|p| p.kind == RewriteKind::RedundantProducer)
    );
    let rounds: Vec<_> = events
        .iter()
        .filter(|e| e.stage == "attempt-summary")
        .collect();
    let after_removal = &rounds[1].attempts[&AdmissionAttemptKind::Removal];
    assert!(after_removal.reused_negative > 0);
    assert_eq!(
        after_removal.new + after_removal.rerun_negative,
        0,
        "unrelated completed negatives must not rerun after the first removal batch"
    );
    for kind in [
        AdmissionAttemptKind::Removal,
        AdmissionAttemptKind::BoundRemoval,
        AdmissionAttemptKind::Discharge,
    ] {
        assert!(
            rounds
                .iter()
                .any(|e| e.attempts.get(&kind).is_some_and(|a| a.reused_negative > 0)),
            "no reuse for {kind:?}: {rounds:?}"
        );
    }
    assert!(
        rounds.iter().any(|e| {
            e.attempts
                .get(&AdmissionAttemptKind::BoundRemoval)
                .is_some_and(|a| a.reused_negative > 0)
                && [
                    AdmissionAttemptKind::Coverage,
                    AdmissionAttemptKind::UpperBounds,
                    AdmissionAttemptKind::GuaranteedBounds,
                ]
                .iter()
                .all(|k| {
                    e.attempts
                        .get(k)
                        .is_none_or(|a| a.new + a.rerun_negative + a.retried_skip == 0)
                })
        }),
        "cached consumers must not build prerequisites: {rounds:?}"
    );
}

#[test]
fn unchanged_attempts_match_exhaustive_oracles_with_and_without_limits() {
    let c = multiround(1);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    for tasks in [0, 1, 2, 4, 8, 16, 64, 100_000] {
        let limits = Limits {
            max_bdd_tasks: tasks,
            ..Limits::default()
        };
        let (on, _) = run(&raw, &limits, true);
        let (off, _) = run(&raw, &limits, false);
        sound(&c, &on);
        sound(&c, &off);
        if on.admission_skips().count() == 0 && off.admission_skips().count() == 0 {
            equal(&on, &off);
        }
    }
    // Derive sweep points from the run, not a pinned work count. Metadata costs
    // and saved operations can change which batches fit; both paths stay sound.
    let defaults = Limits::default();
    let mut budget = Budget::tracked(&defaults);
    raw.clone()
        .admit_without_negative_reuse(&mut budget, None)
        .unwrap();
    let full_work = budget.snapshot().work;
    let mut differing = 0;
    for step in 1..=20 {
        let limits = Limits {
            max_work: full_work * step / 16,
            ..Limits::default()
        };
        let (on, _) = run(&raw, &limits, true);
        let (off, _) = run(&raw, &limits, false);
        sound(&c, &on);
        sound(&c, &off);
        let status = |p: &GroundProgram| {
            (
                p.is_admitted(),
                p.admission_limit().map(|r| (r.phase, r.resource)),
                p.rewrite_proofs().count(),
            )
        };
        if status(&on) != status(&off) {
            differing += 1;
            eprintln!(
                "work sweep {step}/16: reuse {:?}; reference {:?}",
                status(&on),
                status(&off)
            );
        }
        if [(&on), (&off)].iter().all(|p| {
            p.admission_limit().is_none()
                && p.downstream_incomplete().is_none()
                && p.admission_skips().count() == 0
        }) {
            equal(&on, &off);
        }
    }
    eprintln!("work sweep: {differing} reviewed differences across 20 limits");
}

#[test]
fn random_small_unchanged_attempts_preserve_proofs_and_meanings() {
    let mut seed = 0x12abc_u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut negative = 0;
    for _ in 0..192 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let d = rel(&mut c, "d", false);
        rule(&mut c, a, &[(i, false)]);
        rule(&mut c, a, &[(b, true)]);
        rule(&mut c, b, &[(a, true)]);
        let all = [i, j, a, b, d];
        for _ in 0..next() % 7 {
            let head = all[2 + next() as usize % 3];
            let body: Vec<_> = (0..1 + next() % 3)
                .map(|_| (all[next() as usize % all.len()], next() % 2 == 0))
                .collect();
            rule(&mut c, head, &body);
        }
        let limits = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let (on, events) = run(&raw, &limits, true);
        let (off, _) = run(&raw, &limits, false);
        equal(&on, &off);
        sound(&c, &on);
        negative += events
            .iter()
            .filter(|e| e.stage == "attempt-summary")
            .flat_map(|e| e.attempts.values())
            .map(|a| a.negative)
            .sum::<usize>();
    }
    assert!(negative > 0);
}
