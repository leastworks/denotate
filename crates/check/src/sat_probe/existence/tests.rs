use super::*;
use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets};

fn run(
    c: &denotate_ir::Corpus,
    target: RelationId,
    restrictions: &[Restriction],
) -> SatExistenceReport {
    super::super::tests::run(c, target, restrictions)
        .existence
        .unwrap()
}
#[test]
fn odd_loop_world_is_not_filtered_out_by_completion() {
    let mut c = denotate_ir::Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(x, false), (a, true)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatExistenceAnswer::NoMeaning, "{r:?}");
    assert_eq!(r.world.unwrap(), BTreeSet::from([atom(x)]));
    assert_eq!(
        run(&c, a, &[(x, Cardinality::Empty, vec![])]).answer,
        SatExistenceAnswer::EveryWorld
    );
    let impossible = rel(&mut c, "impossible", false);
    assert_eq!(
        run(&c, a, &[(impossible, Cardinality::AtLeastOne, vec![])]).answer,
        SatExistenceAnswer::InconsistentAssumptions
    );
    let mut c = denotate_ir::Corpus::new();
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(a, true)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatExistenceAnswer::NoMeaning);
    assert!(r.world.unwrap().is_empty());
}
#[test]
fn supported_models_do_not_establish_existence_and_assumptions_are_stable() {
    let mut c = denotate_ir::Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    // Completion has b=true, a=false, but its reduct cannot derive b. The only
    // stable value of b exposes the odd loop. This case defeats completion-only.
    rule(&mut c, a, &[(a, true), (b, true)]);
    rule(&mut c, b, &[(b, false)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatExistenceAnswer::NoMeaning, "{r:?}");
    assert!(r.refinements > 0);
    assert_eq!(
        run(&c, a, &[(b, Cardinality::AtLeastOne, vec![])]).answer,
        SatExistenceAnswer::InconsistentAssumptions
    );
}
#[test]
fn cover_preserves_false_bodies_and_does_not_enumerate_irrelevant_inputs() {
    let mut c = denotate_ir::Corpus::new();
    let a = rel(&mut c, "a", false);
    let never = rel(&mut c, "never", false);
    rule(&mut c, a, &[(a, false)]);
    for i in 0..80 {
        let x = rel(&mut c, &format!("x{i}"), true);
        rule(&mut c, a, &[(never, false), (x, false)]);
    }
    // Every body stays false because of a derived false premise. Covering this
    // model needs no inputs even though all 80 belong to its dependency cone.
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatExistenceAnswer::EveryWorld, "{r:?}");
    assert!(r.world.is_none());

    // True derivation leaves alone would omit x and cover the bad world too.
    let x = rel(&mut c, "bad_guard", true);
    rule(&mut c, a, &[(x, false), (a, true)]);
    let r = run(&c, a, &[]);
    assert_eq!(r.answer, SatExistenceAnswer::NoMeaning, "{r:?}");
    assert!(r.world.unwrap().contains(&atom(x)));
}
#[test]
fn existence_limits_and_cancellation_stay_unknown_or_cancelled() {
    let mut c = denotate_ir::Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(a, true), (b, true)]);
    rule(&mut c, b, &[(b, false)]);
    let l = Limits::default();
    let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
    let id = p.component_for(&atom(a)).unwrap().id;
    for limits in [
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
        let r = search(&p, id, &[], &Default::default(), &limits).unwrap();
        assert_eq!(r.answer, SatExistenceAnswer::Unknown);
        assert!(r.reason.is_some());
        assert!(r.world.is_none());
    }
    let r = search(
        &p,
        id,
        &[],
        &SatProbeLimits {
            max_refinements: 0,
            ..Default::default()
        },
        &l,
    )
    .unwrap();
    assert_eq!(r.answer, SatExistenceAnswer::Unknown);
    assert!(r.reason.unwrap().contains("refinements"));
    l.cancellation.cancel();
    assert!(matches!(
        search(&p, id, &[], &Default::default(), &l),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn model_covers_and_existence_agree_with_exhaustive_stable_models() {
    let mut seed = 24681u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for case in 0..100 {
        let mut c = denotate_ir::Corpus::new();
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        let ds = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "d", false),
        ];
        let all = [x, y, ds[0], ds[1], ds[2]];
        // Keep all derived atoms in one component, including ambiguous programs:
        // this test exercises existence independently of the uniqueness result.
        for i in 0..3 {
            rule(&mut c, ds[i], &[(ds[(i + 1) % 3], false)]);
        }
        for _ in 0..7 {
            let h = ds[next() % 3];
            let body = (0..next() % 4)
                .map(|_| (all[next() % 5], next() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, h, &body);
        }
        let l = Limits::default();
        let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        let id = p.component_for(&atom(ds[0])).unwrap().id;
        let restrictions = match case % 3 {
            0 => vec![],
            1 => vec![(x, Cardinality::Empty, vec![])],
            _ => vec![(y, Cardinality::AtLeastOne, vec![])],
        };
        let mut budget = Budget::new(&l);
        let cone = cone(&p, id, &restrictions, &mut budget).unwrap();
        let atoms = all.map(atom);
        let inputs = BTreeSet::from([atom(x), atom(y)]);
        let rules = p.rules().cloned().collect::<Vec<_>>();
        let worlds = subsets(&[atom(x), atom(y)]);
        let models = worlds
            .iter()
            .map(|w| stable_models(&atoms, &inputs, &rules, w))
            .collect::<Vec<_>>();
        for (world, stable) in worlds.iter().zip(&models) {
            for model in stable {
                let values = cone
                    .atoms
                    .iter()
                    .map(|a| model.contains(a))
                    .collect::<Vec<_>>();
                let cube = cover(&cone, &values, &mut budget).unwrap();
                for (other, other_models) in worlds.iter().zip(&models) {
                    if cube
                        .iter()
                        .all(|i| other.contains(&cone.atoms[*i]) == world.contains(&cone.atoms[*i]))
                    {
                        let mut expected =
                            model.difference(&inputs).cloned().collect::<BTreeSet<_>>();
                        expected.extend(other.iter().cloned());
                        assert!(
                            other_models.contains(&expected),
                            "cover lost a stable model in case {case}"
                        );
                    }
                }
            }
        }
        let bad_worlds = worlds
            .iter()
            .zip(&models)
            .filter(|(w, _)| match case % 3 {
                1 => !w.contains(&atom(x)),
                2 => w.contains(&atom(y)),
                _ => true,
            })
            .filter(|(_, ms)| ms.is_empty())
            .map(|(w, _)| w)
            .collect::<Vec<_>>();
        let report = search(&p, id, &restrictions, &Default::default(), &l).unwrap();
        assert_eq!(
            report.answer,
            if bad_worlds.is_empty() {
                SatExistenceAnswer::EveryWorld
            } else {
                SatExistenceAnswer::NoMeaning
            },
            "case {case}: {report:?}"
        );
        if let Some(w) = report.world {
            // Unused inputs are absent from the encoded cone and false in the witness.
            assert!(bad_worlds.contains(&&w));
        }
    }
}
