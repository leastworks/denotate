use crate::{
    limits::Budget,
    test_support::rewrites::{compare, rel, rule, subsets, supported_models},
    *,
};
use denotate_ir::*;
use std::cell::RefCell;

fn cycle(c: &mut Corpus) -> (RelationId, RelationId) {
    let i = rel(c, "flag", true);
    let a = rel(c, "cycle_a", false);
    let b = rel(c, "cycle_b", false);
    rule(c, a, &[(i, false), (b, true)]);
    rule(c, b, &[(i, true), (a, true)]);
    (a, b)
}
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
#[test]
fn cycle_first_admits_before_downstream_chain_and_reviews_disappearing_warning() {
    for depth in [1, 4] {
        let mut c = Corpus::new();
        let (a, _) = cycle(&mut c);
        let i = rel(&mut c, "other_input", true);
        let mut previous = a;
        let mut redundant = Vec::new();
        for n in 0..depth {
            let d = rel(&mut c, &format!("downstream{n}"), false);
            rule(&mut c, d, &[(i, false)]);
            redundant.push(rule(&mut c, d, &[(i, false), (previous, false)]));
            previous = d;
        }
        let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let (p, events) = admit(&raw, &Limits::default());
        assert!(p.is_admitted());
        assert!(p.downstream_incomplete().is_none());
        assert!(
            events
                .iter()
                .any(|e| e.phase == AdmissionPhase::Relevant && e.discharged_negations > 0)
        );
        // These candidates become exact before phase B. Their old warnings are
        // intentionally absent; admitted meanings still match both oracles.
        assert!(
            p.rewrite_proofs()
                .all(|r| !redundant.contains(&r.candidate().source))
        );
        sound(&c, &p);
    }
}
#[test]
fn cycle_first_keeps_downstream_removals_when_the_cycle_stays_unsupported() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(b, true)]);
    rule(&mut c, b, &[(a, true)]);
    let i = rel(&mut c, "i", true);
    let d = rel(&mut c, "downstream", false);
    rule(&mut c, d, &[(i, false)]);
    let redundant = rule(&mut c, d, &[(i, false), (a, false)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let (p, events) = admit(&raw, &Limits::default());
    assert!(!p.is_admitted());
    assert!(
        p.rewrite_proofs()
            .any(|r| r.candidate().source == redundant)
    );
    assert!(
        events
            .iter()
            .any(|e| e.phase == AdmissionPhase::Downstream && e.removed_rules > 0)
    );
    sound(&c, &p);
}
#[test]
fn cycle_first_skips_expensive_unrelated_evaluation_and_wide_downstream_heads() {
    for downstream in [false, true] {
        let mut c = Corpus::new();
        let (a, _) = cycle(&mut c);
        let inputs: Vec<_> = (0..24)
            .map(|i| rel(&mut c, &format!("i{i:02}"), true))
            .collect();
        let wide = rel(&mut c, "wide", false);
        // Thousands of distinct products, deliberately outside the cycle cone.
        for bits in 0..4096 {
            let mut body: Vec<_> = (0..12)
                .map(|i| (inputs[i * 2 + usize::from(bits & (1 << i) != 0)], false))
                .collect();
            if downstream {
                body.push((a, false));
            }
            rule(&mut c, wide, &body);
        }
        let limits = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let (p, events) = admit(&raw, &limits);
        assert!(p.is_admitted());
        assert!(p.admission_limit().is_none());
        assert!(
            events
                .iter()
                .filter_map(|e| e.current.as_ref())
                .all(|c| c.representative.relation != wide)
        );
    }
}
fn guarded(
    unsupported: bool,
    count: usize,
    with_cycle: bool,
    expensive: bool,
) -> (GroundProgram, Vec<RuleId>) {
    let mut c = Corpus::new();
    if with_cycle {
        cycle(&mut c);
    }
    if unsupported {
        let a = rel(&mut c, "unresolved_a", false);
        let b = rel(&mut c, "unresolved_b", false);
        rule(&mut c, a, &[(b, true)]);
        rule(&mut c, b, &[(a, true)]);
    }
    let s = c.declare_sort("Value").unwrap();
    let first = c.declare_constant("first", s).unwrap();
    let second = c.declare_constant("second", s).unwrap();
    let value = c
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    let dependency = expensive.then(|| hard_region(&mut c));
    let mut guards = Vec::new();
    for n in 0..count {
        let h = rel(&mut c, &format!("guard{n}"), false);
        let head = c.atom(h, []).unwrap();
        let yes = c.atom(value, [Term::Constant(first)]).unwrap();
        let no = c.atom(value, [Term::Constant(second)]).unwrap();
        let mut body = vec![Literal::Positive(yes), Literal::Negative(no)];
        if let Some(dependency) = dependency {
            body.push(Literal::Positive(c.atom(dependency, []).unwrap()));
        }
        guards.push(c.add_rule(head, body).unwrap());
    }
    let p = GroundProgram::prepare_with_input_groups(
        &c,
        &Domains::from([(s, vec![first, second])]),
        &[InputAtMostOne {
            relation: value,
            group_by: vec![],
        }],
        &Limits::default(),
    )
    .unwrap();
    (p, guards)
}
#[test]
fn cycle_first_preserves_settled_input_guard_warnings_including_no_cycle_programs() {
    for with_cycle in [false, true] {
        let (raw, guards) = guarded(false, 1, with_cycle, false);
        let (p, _) = admit(&raw, &Limits::default());
        assert!(p.is_admitted());
        assert!(
            p.rewrite_proofs()
                .any(|p| guards.contains(&p.candidate().source)
                    && matches!(p.kind, RewriteKind::Discharge { .. }))
        );
    }
}
#[test]
fn cycle_first_downstream_exhaustion_preserves_admitted_and_unsupported_regions() {
    for unsupported in [false, true] {
        let (raw, _) = guarded(unsupported, 30, true, false);
        let mut exercised = false;
        // Find a logical exhaustion in phase B, without making accounting a golden.
        for max_work in (100..20_000).step_by(100) {
            let limits = Limits {
                max_work,
                ..Limits::default()
            };
            let (p, events) = admit(&raw, &limits);
            if p.downstream_incomplete().is_none() {
                continue;
            }
            assert!(p.admission_limit().is_none());
            assert_eq!(p.is_admitted(), !unsupported);
            assert_eq!(events.last().unwrap().phase, AdmissionPhase::Downstream);
            let m = p.symbolic(&Limits::default()).unwrap();
            let report = m.verify_at_most_one(&Limits::default()).unwrap();
            assert_eq!(report.unresolved.len(), usize::from(unsupported));
            assert!(
                report
                    .unresolved
                    .iter()
                    .all(|r| matches!(r.outcome, RegionOutcome::Unsupported))
            );
            exercised = true;
            break;
        }
        assert!(exercised);
    }
}

// Paired disjunctions with all left variables preceding all right variables:
// a small authored formula whose ordered BDD exceeds the ordinary allowance.
fn hard_region(c: &mut Corpus) -> RelationId {
    let left: Vec<_> = (0..18)
        .map(|i| rel(c, &format!("left{i:02}"), true))
        .collect();
    let right: Vec<_> = (0..18)
        .map(|i| rel(c, &format!("right{i:02}"), true))
        .collect();
    let clauses: Vec<_> = (0..18)
        .map(|i| {
            let clause = rel(c, &format!("clause{i:02}"), false);
            rule(c, clause, &[(left[i], false)]);
            rule(c, clause, &[(right[i], false)]);
            (clause, false)
        })
        .collect();
    let hard = rel(c, "hard", false);
    rule(c, hard, &clauses);
    hard
}
#[test]
fn cycle_first_unrelated_hard_bdd_does_not_precede_cycle_proofs_at_default_limits() {
    let mut c = Corpus::new();
    cycle(&mut c);
    hard_region(&mut c);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert!(matches!(
        raw.symbolic(&limits),
        Err(CheckError::LimitExceeded { .. })
    ));
    let (p, _) = admit(&raw, &limits);
    assert!(p.is_admitted());
    assert!(p.admission_limit().is_none() && p.downstream_incomplete().is_none());
}
#[test]
fn cycle_first_default_limits_report_downstream_exhaustion_without_relabeling_cycles() {
    for unsupported in [false, true] {
        let (raw, _) = guarded(unsupported, 1, true, true);
        let (p, events) = admit(&raw, &Limits::default());
        assert_eq!(p.is_admitted(), !unsupported);
        assert!(p.admission_limit().is_none());
        assert!(p.downstream_incomplete().is_some());
        assert_eq!(events.last().unwrap().phase, AdmissionPhase::Downstream);
        assert!(
            p.components()
                .filter(|c| c.cycle.is_some())
                .all(|c| p.admission_skips_for(c).next().is_none())
        );
    }
}
