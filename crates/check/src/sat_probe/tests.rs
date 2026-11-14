use super::*;
use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets, supported_models};
use denotate_ir::Corpus;

fn run(c: &Corpus, target: RelationId, constraints: &[Restriction]) -> SatProbeReport {
    let l = Limits::default();
    let p = GroundProgram::prepare_cartesian(c, &Domains::new(), &l).unwrap();
    probe_component(
        &p,
        p.component_for(&atom(target)).unwrap().id,
        constraints,
        &SatProbeLimits::default(),
        &l,
    )
    .unwrap()
}
#[test]
fn ambiguous_pair_is_verified_in_one_shared_world() {
    let mut plain = Corpus::new();
    let a0 = rel(&mut plain, "a", false);
    let b0 = rel(&mut plain, "b", false);
    rule(&mut plain, a0, &[(b0, true)]);
    rule(&mut plain, b0, &[(a0, true)]);
    let input_free = run(&plain, a0, &[]);
    assert_eq!(input_free.answer, SatProbeAnswer::Sat);
    assert!(input_free.pair.unwrap().world.is_empty());
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, false), (b, true)]);
    rule(&mut c, b, &[(x, false), (a, true)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatProbeAnswer::Sat);
    let pair = r.pair.unwrap();
    assert_eq!(pair.world, BTreeSet::from([atom(x)]));
    assert_eq!(pair.differing, BTreeSet::from([atom(a), atom(b)]));
    assert_eq!(
        run(&c, a, &[(x, Cardinality::Empty, vec![])]).answer,
        SatProbeAnswer::Unsat
    );
}
#[test]
fn positive_self_support_is_refined_without_claiming_existence() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(a, false)]);
    let r = run(&c, a, &[]);
    assert!(r.supported_pair_seen);
    assert!(r.refinements > 0);
    assert_eq!(r.answer, SatProbeAnswer::Unsat);
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(a, true)]);
    assert_eq!(run(&c, a, &[]).answer, SatProbeAnswer::Unsat); // zero stable models!
}
#[test]
fn unfounded_upstream_cannot_create_an_ambiguity_witness() {
    let mut c = Corpus::new();
    let u = rel(&mut c, "u", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, u, &[(u, false)]);
    rule(&mut c, a, &[(u, false), (b, true)]);
    rule(&mut c, b, &[(u, false), (a, true)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatProbeAnswer::Unsat);
    assert!(r.refinements > 0);
    // An external producer can support that same loop in another world. A
    // refinement must not forbid u unconditionally and lose this stable pair.
    let x = rel(&mut c, "x", true);
    rule(&mut c, u, &[(x, false)]);
    let supported = run(&c, a, &[]);
    assert_eq!(supported.answer, SatProbeAnswer::Sat);
    assert!(supported.pair.unwrap().world.contains(&atom(x)));
}
#[test]
fn exhaustion_and_cancellation_are_not_answers() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(a, false)]);
    let l = Limits::default();
    let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
    let id = p.component_for(&atom(a)).unwrap().id;
    let probe = SatProbeLimits {
        max_refinements: 0,
        ..Default::default()
    };
    assert_eq!(
        probe_component(&p, id, &[], &probe, &l).unwrap().answer,
        SatProbeAnswer::Unknown
    );
    for l in [
        Limits {
            max_atoms: 0,
            ..l.clone()
        },
        Limits {
            max_rules: 0,
            ..l.clone()
        },
        Limits {
            max_dependencies: 0,
            ..l.clone()
        },
        Limits {
            max_work: 0,
            ..l.clone()
        },
        Limits {
            timeout: Duration::ZERO,
            ..l.clone()
        },
    ] {
        assert_eq!(
            probe_component(&p, id, &[], &Default::default(), &l)
                .unwrap()
                .answer,
            SatProbeAnswer::Unknown
        );
    }
    l.cancellation.cancel();
    assert!(matches!(
        probe_component(&p, id, &[], &Default::default(), &l),
        Err(CheckError::Cancelled)
    ));
}
#[test]
fn random_tiny_probes_agree_with_exhaustive_stable_models() {
    let mut seed = 13579u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for _ in 0..100 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let ds = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "d", false),
        ];
        let all = [i, j, ds[0], ds[1], ds[2]];
        for _ in 0..7 {
            let h = ds[next() % 3];
            let body = (0..next() % 4)
                .map(|_| (all[next() % 5], next() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, h, &body);
        }
        let l = Limits::default();
        let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        for comp in p.components().filter(|c| c.recursive) {
            // An independent cone specification using authored ground rule bodies.
            let mut atoms = comp.atoms.iter().cloned().collect::<BTreeSet<_>>();
            loop {
                let old = atoms.len();
                for r in p
                    .rules()
                    .filter(|r| atoms.contains(&r.head.atom))
                    .collect::<Vec<_>>()
                {
                    atoms.extend(r.body.iter().map(|l| l.term.atom.clone()));
                }
                if atoms.len() == old {
                    break;
                }
            }
            let inputs = atoms
                .iter()
                .filter(|a| p.inputs.contains(*a))
                .cloned()
                .collect::<BTreeSet<_>>();
            let rules = p
                .rules()
                .filter(|r| atoms.contains(&r.head.atom))
                .cloned()
                .collect::<Vec<_>>();
            let r = probe_component(&p, comp.id, &[], &Default::default(), &l).unwrap();
            if r.answer == SatProbeAnswer::Unknown {
                assert!(r.reason.unwrap().contains("upstream negative"));
                continue;
            }
            let mut ambiguous = false;
            for w in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
                let stable = stable_models(
                    &atoms.iter().cloned().collect::<Vec<_>>(),
                    &inputs,
                    &rules,
                    &w,
                );
                let projected = stable
                    .iter()
                    .map(|m| {
                        comp.atoms
                            .iter()
                            .filter(|a| m.contains(*a))
                            .cloned()
                            .collect::<BTreeSet<_>>()
                    })
                    .collect::<BTreeSet<_>>();
                ambiguous |= projected.len() > 1;
                if let Some(pair) = &r.pair {
                    if pair.world == w {
                        assert!(pair.models.iter().all(|m| projected.contains(m)));
                        assert_ne!(pair.models[0], pair.models[1]);
                    }
                }
                // Stable is a subset of supported; initial UNSAT is a stronger
                // claim, and refinements must not be described that way.
                if !r.supported_pair_seen {
                    let supported = supported_models(&p, &rules, &w);
                    let projected = supported
                        .iter()
                        .map(|m| {
                            comp.atoms
                                .iter()
                                .filter(|a| m.contains(*a))
                                .cloned()
                                .collect::<BTreeSet<_>>()
                        })
                        .collect::<BTreeSet<_>>();
                    assert!(projected.len() <= 1);
                }
            }
            assert_eq!(r.answer == SatProbeAnswer::Sat, ambiguous);
        }
    }
}

#[test]
fn solver_polls_cancellation_during_a_real_search() {
    let l = Limits::default();
    let mut b = Budget::new(&l);
    let polls = std::rc::Rc::new(std::cell::Cell::new(0));
    let seen = polls.clone();
    let token = l.cancellation.clone();
    let mut cnf = Cnf {
        solver: Solver::new(
            Default::default(),
            Stop {
                cancellation: token.clone(),
                start: Instant::now(),
                timeout: l.timeout,
                hook: Some(Box::new(move || {
                    seen.set(seen.get() + 1);
                    if seen.get() == 2 {
                        token.cancel();
                    }
                })),
            },
        ),
        clauses: 0,
        literals: 0,
    };
    let mut birds = Vec::new();
    for _ in 0..9 {
        let row = (0..8).map(|_| cnf.var(&mut b).unwrap()).collect::<Vec<_>>();
        cnf.clause(row.clone(), &mut b).unwrap();
        birds.push(row);
    }
    for hole in 0..8 {
        cnf.at_most_one(&birds.iter().map(|r| r[hole]).collect::<Vec<_>>(), &mut b)
            .unwrap();
    }
    assert_eq!(cnf.solver.solve_limited(&[]), lbool::UNDEF);
    assert!(polls.get() >= 2);
    assert!(matches!(
        cnf.solver.cb().check(),
        Err(CheckError::Cancelled)
    ));
}
#[test]
fn unrelated_components_are_not_encoded_or_assumed_settled() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(b, true)]);
    rule(&mut c, b, &[(a, true)]);
    for i in 0..100 {
        let unused = rel(&mut c, &format!("unused{i}"), false);
        rule(&mut c, unused, &[(unused, true)]);
    }
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let small = Limits {
        max_atoms: 20,
        max_rules: 40,
        max_bdd_nodes: 0,
        max_bdd_tasks: 0,
        max_bdd_variables: 0,
        ..l
    };
    let r = probe_component(
        &p,
        p.component_for(&atom(a)).unwrap().id,
        &[],
        &Default::default(),
        &small,
    )
    .unwrap();
    assert_eq!(r.answer, SatProbeAnswer::Sat);
    assert_eq!(r.cone_atoms, 2);
    // Once such a component is a provider, do not pretend its meaning is settled.
    let upstream = rel(&mut c, "upstream", false);
    rule(&mut c, upstream, &[(upstream, true)]);
    rule(&mut c, a, &[(upstream, false)]);
    let report = run(&c, a, &[]);
    assert_eq!(report.answer, SatProbeAnswer::Unknown);
    assert!(report.reason.unwrap().contains("upstream negative"));
}
