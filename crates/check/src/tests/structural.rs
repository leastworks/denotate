use super::rewrites::{atom, compare, rel, rule};
use crate::{limits::Budget, *};
use denotate_ir::*;
use std::{cell::RefCell, collections::BTreeSet};

fn structural(c: &Corpus, cartesian: bool) -> (GroundProgram, Vec<AdmissionProgress>) {
    let defaults = Limits::default();
    let raw = if cartesian {
        GroundProgram::prepare_cartesian(c, &Domains::new(), &defaults)
    } else {
        GroundProgram::prepare(c, &Domains::new(), &defaults)
    }
    .unwrap();
    let events = RefCell::new(vec![]);
    let limits = Limits {
        max_bdd_tasks: 0,
        max_bdd_nodes: 0,
        ..defaults
    };
    let p = raw
        .admit_observed(
            &mut Budget::new(&limits),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    compare(c, &Domains::new(), &p);
    assert!(p.rewrite_proofs().all(|p| p.structural().is_some()));
    (p, events.into_inner())
}
fn blocked(c: &mut Corpus) -> denotate_ir::RelationId {
    let u = rel(c, "u", false);
    let v = rel(c, "v", false);
    rule(c, u, &[(v, true)]);
    rule(c, v, &[(u, true)]);
    u
}
#[test]
fn structural_truth_false_and_dead_rules_propagate_with_shared_evidence() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "d", false);
    let dead = rel(&mut c, "dead", false);
    let after = rel(&mut c, "after", false);
    let cycle = rel(&mut c, "cycle", false);
    let fact = rule(&mut c, a, &[]);
    let first = rule(&mut c, b, &[(a, false)]);
    let second = rule(&mut c, d, &[(b, false)]);
    let redundant = rule(&mut c, d, &[(cycle, false)]);
    let killed = rule(&mut c, cycle, &[(d, true)]);
    let dead_rule = rule(&mut c, dead, &[(d, true)]);
    let after_rule = rule(&mut c, after, &[(dead, false)]);
    let (p, events) = structural(&c, false);
    assert!(p.is_admitted());
    assert!(p.admission_limit().is_none());
    assert!(
        events
            .iter()
            .any(|e| e.stage == "structural-committed" && e.removed_rules > 0)
    );
    assert!(!events.iter().any(|e| e.stage == "symbolic"));
    for r in [redundant, killed, dead_rule, after_rule] {
        assert!(!p.rules().any(|x| x.source == r));
    }
    let proof = p
        .rewrite_proofs()
        .find(|p| p.candidate().source == redundant)
        .unwrap();
    let sources: BTreeSet<_> = proof.supporting_rules().iter().map(|r| r.source).collect();
    for r in [fact, first, second] {
        assert!(sources.contains(&r));
    }
    let replay = p.evaluate([], &Limits::default()).unwrap();
    for r in [a, b, d] {
        assert_eq!(replay.fact(&atom(r)).unwrap(), FactState::Settled(true));
    }
    for r in [cycle, dead, after] {
        assert_eq!(replay.fact(&atom(r)).unwrap(), FactState::Settled(false));
    }
}
#[test]
fn structural_shadowed_definitions_unfold_both_chains_and_break_three_negations() {
    for reverse in [false, true] {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let f = rel(&mut c, "field", false);
        let outer = rel(&mut c, "outer", false);
        let inner = rel(&mut c, "inner", false);
        let left = rel(&mut c, "left", false);
        let right = rel(&mut c, "right", false);
        let term = rel(&mut c, "term", false);
        let constraint = rel(&mut c, "constraint", false);
        let kept = rel(&mut c, "kept", false);
        let mut definitions = vec![
            (f, vec![(left, false)]),
            (f, vec![(right, false)]),
            (left, vec![(outer, false)]),
            (right, vec![(inner, false)]),
            (outer, vec![(i, false)]),
            (inner, vec![(outer, false), (term, false)]),
            (term, vec![(constraint, true)]),
            (constraint, vec![(kept, true)]),
            (kept, vec![(f, true)]),
        ];
        if reverse {
            definitions.reverse();
        }
        let mut redundant = None;
        for (h, b) in definitions {
            let r = rule(&mut c, h, &b);
            if h == f && b == [(right, false)] {
                redundant = Some(r);
            }
        }
        let (p, events) = structural(&c, false);
        assert!(p.is_admitted());
        assert!(p.admission_limit().is_none());
        assert!(!p.rules().any(|r| Some(r.source) == redundant));
        assert!(!events.iter().any(|e| e.stage == "symbolic"));
        let proof = p
            .rewrite_proofs()
            .find(|p| Some(p.candidate().source) == redundant)
            .unwrap();
        assert!(
            matches!(&proof.structural().unwrap().reason, StructuralReason::Subsumed {unfolded,..} if unfolded.len()>=4)
        );
    }
}
#[test]
fn structural_subsumption_keeps_polarity_multi_producers_negative_and_recursive_boundaries() {
    let mut c = Corpus::new();
    let u = blocked(&mut c);
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let a = rel(&mut c, "a", false);
    let multi = rel(&mut c, "multi", false);
    let neg = rel(&mut c, "neg", false);
    let looped = rel(&mut c, "looped", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, multi, &[(i, false)]);
    rule(&mut c, multi, &[(j, false)]);
    rule(&mut c, neg, &[(i, false)]);
    rule(&mut c, looped, &[(looped, false), (j, false)]);
    let kept = vec![
        rule(&mut c, a, &[(u, false), (i, false)]),
        rule(&mut c, a, &[(u, false), (i, true)]),
        rule(&mut c, out, &[(u, false), (multi, false)]),
        rule(&mut c, out, &[(u, false), (i, false)]),
        rule(&mut c, out, &[(u, false), (neg, true)]),
        rule(&mut c, out, &[(u, false), (looped, false)]),
        rule(&mut c, out, &[(u, false), (looped, false), (j, false)]),
    ];
    let (p, _) = structural(&c, true);
    for r in kept {
        assert!(p.rules().any(|x| x.source == r), "retained {r:?}");
    }
}
#[test]
fn structural_duplicate_input_dependent_bodies_keep_one_real_survivor() {
    let mut c = Corpus::new();
    let u = blocked(&mut c);
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(u, false), (i, false)]);
    rule(&mut c, a, &[(u, false), (i, false)]);
    rule(&mut c, a, &[(u, false), (j, false), (i, false)]);
    let (p, _) = structural(&c, false);
    assert_eq!(p.rules().filter(|r| r.head.atom.relation == a).count(), 1);
    assert_eq!(p.rewrite_proofs().count(), 2);
    for proof in p.rewrite_proofs() {
        let StructuralReason::Subsumed { by, .. } = &proof.structural().unwrap().reason else {
            panic!()
        };
        assert!(p.rule(*by).is_some());
    }
}
#[test]
fn structural_tiny_generated_programs_match_independent_stable_model_oracle() {
    let mut seed = 20u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (seed >> 32) as usize
    };
    for _ in 0..400 {
        let mut c = Corpus::new();
        let rs: Vec<_> = (0..6)
            .map(|i| rel(&mut c, &format!("r{i}"), i < 2))
            .collect();
        for _ in 0..(2 + next() % 9) {
            let h = rs[2 + next() % 4];
            let b: Vec<_> = (0..next() % 4)
                .map(|_| (rs[next() % 6], next() % 2 == 1))
                .collect();
            rule(&mut c, h, &b);
        }
        structural(&c, false);
    }
}

#[test]
fn structural_worklist_revisits_consumers_after_a_producer_becomes_unique() {
    let mut c = Corpus::new();
    let u = blocked(&mut c);
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let out = rel(&mut c, "out", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, out, &[(a, false)]);
    let removed = rule(&mut c, out, &[(u, false), (i, false), (j, false)]);
    rule(&mut c, a, &[(b, false)]);
    rule(&mut c, b, &[(u, false), (i, false)]);
    rule(&mut c, b, &[(u, false), (i, false), (j, false)]);
    let (p, _) = structural(&c, false);
    assert!(!p.rules().any(|r| r.source == removed));
    assert_eq!(p.rewrite_proofs().count(), 2);
}

#[test]
fn structural_exhaustion_commits_no_partial_worklist() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "d", false);
    rule(&mut c, a, &[]);
    rule(&mut c, a, &[(b, false)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, d, &[(b, false)]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut completed = false;
    let mut exhausted = false;
    for max_work in (0..2000).step_by(11) {
        let p = raw
            .clone()
            .admit(&Limits {
                max_work,
                ..Limits::default()
            })
            .unwrap();
        compare(&c, &Domains::new(), &p);
        if p.admission_limit().is_some() {
            exhausted = true;
            assert_eq!(p.rules().count(), raw.rules().count());
            assert_eq!(p.rewrite_proofs().count(), 0);
        } else {
            completed = true;
            assert!(p.is_admitted());
            assert_eq!(p.rules().count(), 1);
        }
    }
    assert!(completed && exhausted);
}

#[test]
fn structural_wide_heads_finish_at_default_limits_with_or_without_a_cover() {
    for covered in [false, true] {
        let mut c = Corpus::new();
        let u = blocked(&mut c);
        let common = rel(&mut c, "common", true);
        let out = rel(&mut c, "out", false);
        for i in 0..6000 {
            let input = rel(&mut c, &format!("i{i}"), true);
            rule(&mut c, out, &[(u, false), (common, false), (input, false)]);
        }
        if covered {
            rule(&mut c, out, &[(u, false), (common, false)]);
        }
        let limits = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let proofs = crate::structural::reduce(&p, &mut Budget::new(&limits)).unwrap();
        assert_eq!(proofs.len(), if covered { 6000 } else { 0 });
        assert!(proofs.iter().all(|p| p.candidate.head.atom.relation == out));
    }
}

#[test]
fn structural_settled_helpers_support_blocked_removals_without_gaining_warnings() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let settled = rel(&mut c, "settled", false);
    let positive = rel(&mut c, "positive", false);
    let u = blocked(&mut c);
    let out = rel(&mut c, "out", false);
    let fact = rule(&mut c, settled, &[]);
    let alternative = rule(&mut c, settled, &[(i, false)]);
    // Input-free positive recursion is already settled by the existing concrete
    // evaluator, exactly as on folded preparation. It is not a removal target.
    let recursive = rule(&mut c, positive, &[(positive, false)]);
    let dead = rule(&mut c, out, &[(positive, false), (u, false)]);
    let (p, _) = structural(&c, true);
    for source in [fact, alternative, recursive] {
        assert!(p.rules().any(|r| r.source == source));
        assert!(!p.rewrite_proofs().any(|r| r.candidate().source == source));
    }
    let proof = p
        .rewrite_proofs()
        .find(|p| p.candidate().source == dead)
        .unwrap();
    assert!(matches!(
        proof.structural().unwrap().reason,
        StructuralReason::Dead { .. }
    ));
    assert!(
        proof
            .supporting_rules()
            .iter()
            .any(|r| r.source == recursive)
    );
}

#[test]
fn direct_false_evidence_distinguishes_no_producer_from_positive_recursion() {
    let mut c = Corpus::new();
    let u = blocked(&mut c);
    let p = rel(&mut c, "p", false);
    let missing = rel(&mut c, "missing", false);
    let out = rel(&mut c, "out", false);
    let no_source = rel(&mut c, "no_source", false);
    let recursive = rule(&mut c, p, &[(p, false)]);
    let dead_cycle = rule(&mut c, out, &[(p, false), (u, false)]);
    let dead_missing = rule(&mut c, no_source, &[(missing, false), (u, false)]);
    let (ground, _) = structural(&c, true);
    let proof = |source| {
        ground
            .rewrite_proofs()
            .find(|r| r.candidate().source == source)
            .unwrap()
            .structural()
            .unwrap()
    };
    assert_eq!(
        proof(dead_cycle).settlement(&atom(p)),
        (false, StructuralSettlement::NoDerivation)
    );
    assert_eq!(
        proof(dead_cycle)
            .direct_rules()
            .iter()
            .map(|r| r.source)
            .collect::<Vec<_>>(),
        [recursive]
    );
    assert_eq!(
        proof(dead_missing).settlement(&atom(missing)),
        (false, StructuralSettlement::NoProducer)
    );
    assert!(proof(dead_missing).direct_rules().is_empty());
}
