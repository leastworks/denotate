use super::rewrites::{atom, rel, rule, stable_models, subsets};
use crate::{certification::CertificationDependencies, limits::Budget, *};
use denotate_ir::*;
use std::collections::BTreeSet;

// Exhaustive reference: enumerate full assignments, without generalized exclusion.
// Replay/certification are unchanged operations; independently check every successful
// certificate against stable models of the original, Cartesian-grounded program.
fn compare(c: &Corpus, domains: &Domains, p: &GroundProgram, target: RelationId) {
    let limits = Limits::default();
    let m = p.symbolic(&limits).unwrap();
    let ctx = m.context();
    let inputs: Vec<_> = p.ordered_inputs().into_iter().cloned().collect();
    let mut worlds = subsets(&inputs);
    // Match absent-first BDD traversal, without using its witness or cube machinery.
    worlds.sort_by_key(|w| inputs.iter().map(|a| w.contains(a)).collect::<Vec<_>>());
    let tuples: Vec<_> = p
        .atoms()
        .filter(|a| a.relation == target)
        .cloned()
        .collect();
    let oracle = GroundProgram::prepare_cartesian(c, domains, &limits).unwrap();
    let oracle_atoms = oracle.atoms().cloned().collect::<Vec<_>>();
    let oracle_inputs = oracle.input_atoms().cloned().collect();
    let oracle_rules = oracle.rules().cloned().collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    let mut unresolved = false;
    let mut coverage_unresolved = false;
    let mut missing = false;
    for world in worlds {
        let replay = match p.evaluate(world.iter().cloned(), &limits) {
            Ok(r) => r,
            Err(CheckError::InvalidInputGroup(_)) => continue,
            Err(e) => panic!("unexpected reference replay: {e:?}"),
        };
        assert!(
            ctx.evaluate(&ctx.permitted_worlds(), world.iter().cloned(), &limits)
                .unwrap()
        );
        let facts: Vec<_> = tuples.iter().map(|a| replay.fact(a).unwrap()).collect();
        let certified = if facts.iter().any(|f| matches!(f, FactState::Blocked(_))) {
            match p
                .certify_observation(world.iter().cloned(), &limits)
                .unwrap()
            {
                CertificationOutcome::Certified(certificate) => {
                    let models =
                        stable_models(&oracle_atoms, &oracle_inputs, &oracle_rules, &world);
                    assert_eq!(models, BTreeSet::from([certificate.facts.clone()]));
                    Some(certificate)
                }
                CertificationOutcome::NotCertified => None,
                CertificationOutcome::Inconclusive(e) => panic!("small reference exhausted: {e:?}"),
            }
        } else {
            None
        };
        for (tuple, fact) in tuples.iter().zip(&facts) {
            let value = match fact {
                FactState::Settled(value) => Some(*value),
                FactState::Blocked(_) => certified.as_ref().map(|c| c.facts.contains(tuple)),
            };
            match value {
                Some(true) => {
                    seen.insert(tuple.clone());
                }
                Some(false) => {}
                None => unresolved = true,
            }
        }
        // Coverage stops at its first settled absence; a known-present candidate
        // already suffices, even when another candidate is blocked.
        if !missing && !facts.contains(&FactState::Settled(true)) {
            if facts.iter().all(|f| *f == FactState::Settled(false)) {
                missing = true;
            } else if let Some(c) = &certified {
                missing = tuples.iter().all(|a| !c.facts.contains(a));
            } else {
                coverage_unresolved = true;
            }
        }
    }
    let empty = m
        .check_emptiness(&limits, EmptinessExamples::default(), None)
        .unwrap();
    let empty = empty.values().next().unwrap();
    assert!(empty.inconclusive.is_none(), "{empty:?}");
    assert_eq!(empty.present, seen.len());
    assert_eq!(empty.unresolved, unresolved);
    assert_eq!(empty.proved(), seen.is_empty() && !unresolved);
    for example in &empty.examples {
        assert!(seen.contains(&example.tuple));
        assert_eq!(
            settled(p, &example.observation, &[example.tuple.clone()]),
            Some(true)
        );
    }
    let coverage = m.check_coverage(&limits, None).unwrap();
    let coverage = coverage.values().next().unwrap();
    assert!(coverage.inconclusive.is_none(), "{coverage:?}");
    assert_eq!(coverage.examined, 1);
    assert_eq!(coverage.missing, usize::from(missing));
    assert_eq!(coverage.unsupported, usize::from(coverage_unresolved));
    assert_eq!(coverage.proved(), !missing && !coverage_unresolved);
    for example in &coverage.examples {
        assert_eq!(settled(p, &example.observation, &tuples), Some(false));
    }
}

fn settled(p: &GroundProgram, world: &Observation, tuples: &[GroundAtom]) -> Option<bool> {
    let limits = Limits::default();
    let r = p.evaluate(world.present.iter().cloned(), &limits).unwrap();
    let states = tuples
        .iter()
        .map(|a| r.fact(a).unwrap())
        .collect::<Vec<_>>();
    if states.contains(&FactState::Settled(true)) {
        return Some(true);
    }
    if states.iter().all(|s| *s == FactState::Settled(false)) {
        return Some(false);
    }
    match p
        .certify_observation(world.present.iter().cloned(), &limits)
        .unwrap()
    {
        CertificationOutcome::Certified(c) => Some(tuples.iter().any(|a| c.facts.contains(a))),
        CertificationOutcome::NotCertified => None,
        CertificationOutcome::Inconclusive(e) => panic!("example exhausted: {e:?}"),
    }
}

fn obligations(c: &mut Corpus, target: RelationId) {
    c.empty("absent", target, "").unwrap();
    c.at_least_one("covered", target, [], "").unwrap();
}

#[test]
fn generalized_search_agrees_with_full_worlds_and_stable_models() {
    // No-input cycle; signed input guards; outside permanent and guarded cycles;
    // several rounds of pruning; both a blocked atom and its negative dependent.
    for guard in [None, Some(false), Some(true)] {
        for outside in 0..3 {
            for depth in 0..3 {
                let mut c = Corpus::new();
                let trigger = rel(&mut c, "trigger", true);
                let release = rel(&mut c, "release", true);
                rel(&mut c, "irrelevant", true);
                let blocked = rel(&mut c, "blocked", false);
                let mut body = vec![(blocked, true)];
                if let Some(negative) = guard {
                    body.insert(0, (trigger, negative));
                }
                rule(&mut c, blocked, &body);
                let mut target = blocked;
                for i in 0..depth {
                    let next = rel(&mut c, &format!("dependent_{i}"), false);
                    if i == 0 {
                        // A second cycle can be disabled only after its provider settles.
                        rule(&mut c, next, &[(target, false), (next, true)]);
                    } else {
                        rule(&mut c, next, &[(target, true)]);
                    }
                    target = next;
                }
                if outside > 0 {
                    let other = rel(&mut c, "unrelated", false);
                    let mut body = vec![(other, true)];
                    if outside == 2 {
                        body.insert(0, (release, true));
                    }
                    rule(&mut c, other, &body);
                }
                obligations(&mut c, target);
                let d = Domains::new();
                for admit in [false, true] {
                    let p = GroundProgram::prepare(&c, &d, &Limits::default()).unwrap();
                    let p = if admit {
                        p.admit(&Limits::default()).unwrap()
                    } else {
                        p
                    };
                    compare(&c, &d, &p, target);
                }
            }
        }
    }
}

#[test]
fn unrelated_release_input_is_kept_and_permanent_failure_is_not_scoped_away() {
    for permanent in [false, true] {
        let mut c = Corpus::new();
        let trigger = rel(&mut c, "trigger", true);
        let release = rel(&mut c, "release", true);
        let blocked = rel(&mut c, "blocked", false);
        let result = rel(&mut c, "result", false);
        let other = rel(&mut c, "unrelated", false);
        rule(&mut c, blocked, &[(trigger, false), (blocked, true)]);
        rule(&mut c, result, &[(blocked, true)]);
        let mut body = vec![(other, true)];
        if !permanent {
            body.insert(0, (release, true));
        }
        rule(&mut c, other, &body);
        obligations(&mut c, result);
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        compare(&c, &Domains::new(), &p, result);
        let m = p.symbolic(&Limits::default()).unwrap();
        let reports = m
            .check_emptiness(&Limits::default(), EmptinessExamples::default(), None)
            .unwrap();
        let report = reports.values().next().unwrap();
        assert_eq!(report.present, usize::from(!permanent));
        assert!(report.unresolved);
        for e in &report.examples {
            assert!(e.observation.present.contains(&atom(release)));
            assert!(!e.observation.present.contains(&atom(trigger)));
        }
    }
}

#[test]
fn coverage_keeps_all_candidates_and_correlated_assumptions() {
    for second_present in [false, true] {
        let mut c = Corpus::new();
        let sort = c.declare_sort("Choice").unwrap();
        let a = c.declare_constant("a", sort).unwrap();
        let b = c.declare_constant("b", sort).unwrap();
        let target = c
            .declare_relation(
                "result",
                RelationRole::Derived,
                [Parameter::new("choice", sort)],
            )
            .unwrap();
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        let correlated = rel(&mut c, "correlated", true);
        let bad_x = rel(&mut c, "bad_x", false);
        let bad_y = rel(&mut c, "bad_y", false);
        rule(&mut c, bad_x, &[(x, true), (bad_x, true)]);
        rule(&mut c, bad_y, &[(y, true), (bad_y, true)]);
        for (value, provider, negative) in [(a, bad_x, false), (b, bad_y, second_present)] {
            let head = c.atom(target, [value.into()]).unwrap();
            let body = c.atom(provider, []).unwrap();
            c.add_rule(
                head,
                [if negative {
                    Literal::Negative(body)
                } else {
                    Literal::Positive(body)
                }],
            )
            .unwrap();
        }
        // A selected, derived restriction correlates a relevant input with an
        // input outside the search dependencies. It is not safe to extend a
        // projected witness with arbitrary absent inputs.
        let mismatch = rel(&mut c, "mismatch", false);
        rule(&mut c, mismatch, &[(x, false), (correlated, true)]);
        rule(&mut c, mismatch, &[(x, true), (correlated, false)]);
        let assumption = c
            .assume_empty_in(Namespace::default(), "correlated_inputs", mismatch)
            .unwrap();
        obligations(&mut c, target);
        let domains = Domains::from([(sort, vec![a, b])]);
        let limits = Limits::default();
        let mut p = GroundProgram::prepare(&c, &domains, &limits).unwrap();
        p.install_assumptions(
            &[c.assumption(assumption).unwrap().restriction.clone()],
            None,
            &mut Budget::new(&limits),
        )
        .unwrap();
        let p = p.admit(&limits).unwrap();
        compare(&c, &domains, &p, target);
        let m = p.symbolic(&limits).unwrap();
        let reports = m.check_coverage(&limits, None).unwrap();
        let report = reports.values().next().unwrap();
        assert_eq!(report.missing, usize::from(!second_present));
        assert_eq!(report.unsupported, 1);
        for example in &report.examples {
            assert!(example.observation.present.contains(&atom(x)));
            assert!(example.observation.present.contains(&atom(y)));
            assert!(example.observation.present.contains(&atom(correlated)));
        }
    }
}

#[test]
fn input_independent_cycle_with_many_inputs_finishes_unresolved_at_default_limits() {
    let mut c = Corpus::new();
    let cycle = rel(&mut c, "cycle", false);
    rule(&mut c, cycle, &[(cycle, true)]);
    for i in 0..64 {
        rel(&mut c, &format!("independent_{i}"), true);
    }
    obligations(&mut c, cycle);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits)
        .unwrap()
        .admit(&limits)
        .unwrap();
    let m = p.symbolic(&limits).unwrap();
    let empty = m
        .check_emptiness(&limits, EmptinessExamples::default(), None)
        .unwrap();
    let empty = empty.values().next().unwrap();
    assert!(empty.inconclusive.is_none());
    assert!(empty.unresolved && !empty.proved());
    assert_eq!(empty.present, 0);
    let coverage = m.check_coverage(&limits, None).unwrap();
    let coverage = coverage.values().next().unwrap();
    assert!(coverage.inconclusive.is_none());
    assert_eq!((coverage.missing, coverage.unsupported), (0, 1));
    assert!(!coverage.proved());
}

#[test]
fn incomplete_dependency_analysis_returns_a_limit_not_an_empty_scope() {
    let mut c = Corpus::new();
    let input = rel(&mut c, "input", true);
    let target = rel(&mut c, "target", false);
    // The absent-first world stays blocked, so BOTH callers need exclusion.
    rule(&mut c, target, &[(input, true), (target, true)]);
    obligations(&mut c, target);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    // Learn the complete cost, then exhaust before its final operation. This is
    // failure injection, not a golden budget or a production policy threshold.
    let mut budget = Budget::new(&limits);
    CertificationDependencies::new(&p, [atom(target)], &mut budget).unwrap();
    let short = Limits {
        max_work: budget.used() - 1,
        ..limits.clone()
    };
    assert!(matches!(
        CertificationDependencies::new(&p, [atom(target)], &mut Budget::new(&short)),
        Err(CheckError::LimitExceeded { .. })
    ));
    let cancelled = Limits::default();
    cancelled.cancellation.cancel();
    assert!(matches!(
        CertificationDependencies::new(&p, [atom(target)], &mut Budget::new(&cancelled)),
        Err(CheckError::Cancelled)
    ));

    // Exercise propagation through BOTH reporting callers. Search for a failing
    // allowance instead of pinning the current implementation's work charges.
    let m = p.symbolic(&limits).unwrap();
    let mut empty_failed = false;
    let mut coverage_failed = false;
    for max_work in 0..10_000 {
        let limited = Limits {
            max_work,
            ..limits.clone()
        };
        let empty = m
            .check_emptiness(&limited, EmptinessExamples::default(), None)
            .unwrap();
        let coverage = m.check_coverage(&limited, None).unwrap();
        let empty = empty.values().next().unwrap();
        let coverage = coverage.values().next().unwrap();
        let in_cone = |reason: &Option<Inconclusive>| {
            reason.as_ref().is_some_and(|r| {
                matches!(r.phase, "dependency cones" | "diagnostic dependency inputs")
            })
        };
        if in_cone(&empty.inconclusive) {
            assert!(!empty.proved());
            empty_failed = true;
        }
        if in_cone(&coverage.inconclusive) {
            assert!(!coverage.proved());
            coverage_failed = true;
        }
        if empty_failed && coverage_failed {
            break;
        }
    }
    assert!(empty_failed && coverage_failed);
}
