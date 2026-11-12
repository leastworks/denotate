use super::rewrites::{atom, compare, rel, rule, subsets};
use crate::{limits::Budget, *};
use denotate_ir::Corpus;
use std::cell::RefCell;

#[test]
fn producer_removals_settle_supported_cycles_before_bounds_in_either_rule_order() {
    for reverse in [false, true] {
        for complementary in [false, true] {
            let mut c = Corpus::new();
            let chosen = rel(&mut c, "chosen", true);
            let seed = rel(&mut c, "seed", complementary);
            let kept = rel(&mut c, "kept", false);
            let term = rel(&mut c, "term", false);
            let next = rel(&mut c, "next", false);
            let next_term = rel(&mut c, "next_term", false);
            let mut rules = vec![
                (kept, vec![(seed, false)]),
                (kept, vec![(term, false)]),
                (term, vec![(chosen, false), (kept, true)]),
                (next, vec![(kept, false)]),
                (next, vec![(next_term, false)]),
                (next_term, vec![(chosen, false), (next, true)]),
            ];
            if complementary {
                // Neither producer is always true alone; together they cover
                // every world, independently of the blocked component.
                rules.push((kept, vec![(seed, true)]));
            } else {
                rules.push((seed, vec![]));
            }
            if reverse {
                rules.reverse();
            }
            for (head, body) in rules {
                rule(&mut c, head, &body);
            }
            let limits = Limits::default();
            let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
            assert!(!raw.is_admitted());
            let events = RefCell::new(Vec::new());
            let p = raw
                .admit_observed(
                    &mut Budget::new(&limits),
                    Some(&|e| events.borrow_mut().push(e.clone())),
                )
                .unwrap();
            assert!(p.is_admitted());
            assert!(p.admission_limit().is_none());
            assert!(p.rewrite_proofs().all(|proof| {
                proof.kind == RewriteKind::RedundantProducer
                    && proof.symbolic().is_none_or(|p| p.upper_bounds.is_none())
            }));
            assert!(
                events.borrow().iter().all(|e| e.stage != "upper-bounds"),
                "cycles eliminated by independent producers need no cycle bounds"
            );
            assert!(compare(&c, &Domains::new(), &p) > 0);
            for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
                let replay = p.evaluate(world, &limits).unwrap();
                for r in [kept, next] {
                    assert_eq!(replay.fact(&atom(r)).unwrap(), FactState::Settled(true));
                    assert!(replay.derivation(&atom(r)).is_some());
                }
                for r in [term, next_term] {
                    assert_eq!(replay.fact(&atom(r)).unwrap(), FactState::Settled(false));
                }
            }
        }
    }
}

#[test]
fn producer_removals_do_not_treat_a_possible_outside_producer_as_certain() {
    let mut c = Corpus::new();
    let seed = rel(&mut c, "seed", true);
    let chosen = rel(&mut c, "chosen", true);
    let kept = rel(&mut c, "kept", false);
    let term = rel(&mut c, "term", false);
    rule(&mut c, kept, &[(seed, false)]);
    let cyclic = rule(&mut c, kept, &[(term, false)]);
    rule(&mut c, term, &[(chosen, false), (kept, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    assert!(!p.is_admitted());
    assert!(p.admission_limit().is_none());
    assert!(p.rules().any(|r| r.source == cyclic));
    assert_eq!(p.rewrite_proofs().count(), 0);
    assert!(compare(&c, &Domains::new(), &p) > 0);
}

#[test]
fn producer_removals_survive_later_cycle_bound_exhaustion() {
    let mut c = Corpus::new();
    let t = rel(&mut c, "t", true);
    let kept = rel(&mut c, "kept", false);
    let term = rel(&mut c, "term", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    // Put the cycle needing bounds first: scan order must not delay removal.
    rule(&mut c, x, &[(t, false), (y, true)]);
    rule(&mut c, y, &[(t, true), (x, true)]);
    rule(&mut c, kept, &[]);
    let redundant = rule(&mut c, kept, &[(term, false)]);
    rule(&mut c, term, &[(t, false), (kept, true)]);
    let defaults = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &defaults).unwrap();
    let mut found = false;
    // Exercise an exhausted later operation without fixing any budget or work
    // count as the expected value. Earlier committed evidence must survive it.
    for max_condition_nodes in (0..2000).step_by(4) {
        let limits = Limits {
            max_condition_nodes,
            ..defaults.clone()
        };
        let last = RefCell::new(None);
        let p = raw
            .clone()
            .admit_observed(
                &mut Budget::new(&limits),
                Some(&|e| *last.borrow_mut() = Some(e.clone())),
            )
            .unwrap();
        let event = last.into_inner().unwrap();
        if event.stage != "upper-bounds" || event.failure.is_none() {
            continue;
        }
        assert!(event.removed_rules > 0);
        assert!(p.admission_limit().is_some());
        assert!(!p.rules().any(|r| r.source == redundant));
        assert!(
            p.rewrite_proofs()
                .all(|r| r.kind == RewriteKind::RedundantProducer)
        );
        let meaning = p.symbolic(&defaults).unwrap();
        assert!(
            matches!(meaning.fact(&atom(kept)).unwrap(), SymbolicFact::Settled(c) if c.is_true())
        );
        assert!(matches!(
            meaning.fact(&atom(x)).unwrap(),
            SymbolicFact::Inconclusive(_)
        ));
        assert!(compare(&c, &Domains::new(), &p) > 0);
        found = true;
        break;
    }
    assert!(
        found,
        "exercise bounds exhaustion after a committed removal"
    );
}
