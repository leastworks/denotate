use super::*;
use crate::test_support::rewrites::{rel, rule, subsets};
use denotate_ir::{Corpus, QualifiedKey, RelationKey};

fn fixture(reverse: bool) -> (GroundProgram, SemanticKeys) {
    let mut c = Corpus::new();
    let mut keys = SemanticKeys::default();
    let mut inputs = BTreeMap::new();
    let mut names = vec!["a", "b", "c", "x", "y", "z"];
    if reverse {
        names.reverse();
    }
    for name in names {
        inputs.insert(name, rel(&mut c, name, true));
    }
    for (a, b) in [("a", "x"), ("b", "y"), ("c", "z")] {
        let out = rel(&mut c, &format!("{a}{b}"), false);
        for _ in 0..if a == "a" { 3 } else { 1 } {
            rule(&mut c, out, &[(inputs[a], false), (inputs[b], false)]);
        }
    }
    for r in c.relations() {
        keys.bind_relation(
            &c,
            r.id,
            RelationKey::Named(QualifiedKey::new("order", r.name.as_str())),
        )
        .unwrap();
    }
    (
        GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap(),
        keys,
    )
}
fn keyed_order(p: &GroundProgram, k: &SemanticKeys) -> Vec<AtomKey> {
    p.ordered_inputs()
        .into_iter()
        .map(|a| AtomKey::from_atom(k, a).unwrap())
        .collect()
}

#[test]
fn structural_order_is_deterministic_and_uses_dependencies_not_allocation() {
    let l = Limits::default();
    let mut orders = Vec::new();
    for reverse in [false, true, false] {
        let (p, k) = fixture(reverse);
        let p = p
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&l))
            .unwrap();
        assert_eq!(p.input_order_report().effective, InputOrder::Structural);
        let order = keyed_order(&p, &k);
        // Three independent pairs can each be placed adjacent, whatever their names.
        for rule in &p.core.rules {
            let positions: Vec<_> = rule
                .body
                .iter()
                .map(|l| {
                    order
                        .iter()
                        .position(|a| *a == AtomKey::from_atom(&k, &l.term.atom).unwrap())
                        .unwrap()
                })
                .collect();
            assert_eq!(positions[0].abs_diff(positions[1]), 1);
        }
        orders.push(order);
    }
    assert!(orders.windows(2).all(|p| p[0] == p[1]));
}

#[test]
fn disjoint_and_overlapping_preferences_preserve_every_input_constraint() {
    let l = Limits::default();
    for overlap in [false, true] {
        let (mut p, k) = fixture(false);
        let original = p.inputs.iter().cloned().collect::<Vec<_>>();
        p.input_groups = vec![
            // Co-read pairs are (a,x), (b,y), (c,z); each group crosses them.
            vec![original[0].clone(), original[1].clone()],
            vec![original[3].clone(), original[4].clone()],
        ];
        if overlap {
            p.input_groups.extend([
                vec![original[0].clone(), original[4].clone()],
                vec![original[1].clone(), original[3].clone()],
            ]);
        }
        let key = p
            .clone()
            .choose_input_order(&k, &[], InputOrder::Key, &mut Budget::new(&l))
            .unwrap();
        let ordered = p
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&l))
            .unwrap();
        for world in subsets(&original) {
            let permitted = key
                .input_groups
                .iter()
                .all(|g| g.iter().filter(|a| world.contains(*a)).count() <= 1);
            for program in [&key, &ordered] {
                assert_eq!(
                    program.evaluate(world.iter().cloned(), &l).is_ok(),
                    permitted
                );
            }
            if permitted {
                let facts = |p: &GroundProgram| {
                    p.evaluate(world.iter().cloned(), &l)
                        .unwrap()
                        .established_facts()
                        .cloned()
                        .collect::<BTreeSet<_>>()
                };
                assert_eq!(facts(&key), facts(&ordered));
            }
        }
    }
}

#[test]
fn structural_cutoff_falls_back_but_global_exhaustion_and_cancellation_propagate() {
    let (p, k) = fixture(false);
    let l = Limits::default();
    let key = p
        .clone()
        .choose_input_order(&k, &[], InputOrder::Key, &mut Budget::new(&l))
        .unwrap();
    let mut budget = Budget::tracked(&l);
    let fallback = p
        .clone()
        .choose_input_order_bounded(&k, &[], InputOrder::Structural, &mut budget, 1)
        .unwrap();
    assert_eq!(fallback.input_order_report().effective, InputOrder::Key);
    assert!(fallback.input_order_report().fallback.is_some());
    assert!(budget.snapshot().work > 0);
    assert_eq!(keyed_order(&key, &k), keyed_order(&fallback, &k));
    for world in subsets(&p.inputs.iter().cloned().collect::<Vec<_>>()) {
        let facts = |g: &GroundProgram| {
            g.evaluate(world.iter().cloned(), &l)
                .unwrap()
                .established_facts()
                .cloned()
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(facts(&key), facts(&fallback));
    }
    let tight = Limits {
        max_work: 0,
        ..l.clone()
    };
    assert!(matches!(
        p.clone()
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&tight)),
        Err(CheckError::LimitExceeded {
            resource: "work",
            ..
        })
    ));
    let expired = Limits {
        timeout: std::time::Duration::ZERO,
        ..l.clone()
    };
    assert!(matches!(
        p.clone()
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&expired)),
        Err(CheckError::Deadline { .. })
    ));
    l.cancellation.cancel();
    assert!(matches!(
        p.choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&l)),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn reordered_clones_reject_conditions_from_the_old_map() {
    let (p, k) = fixture(false);
    let l = Limits::default();
    let key = p
        .clone()
        .choose_input_order(&k, &[], InputOrder::Key, &mut Budget::new(&l))
        .unwrap();
    let reverse = p
        .choose_input_order(&k, &[], InputOrder::ReverseKey, &mut Budget::new(&l))
        .unwrap();
    assert_eq!(
        keyed_order(&key, &k).into_iter().rev().collect::<Vec<_>>(),
        keyed_order(&reverse, &k)
    );
    let a = key.inputs.first().unwrap();
    let old = key.condition_context(&l).unwrap().input(a, &l).unwrap();
    let context = reverse.condition_context(&l).unwrap();
    assert!(matches!(
        context.and(&old, &context.true_condition(), &l),
        Err(CheckError::ForeignCondition)
    ));
    let restored = reverse.with_atom_key_order(&k).unwrap();
    let restored_context = restored.condition_context(&l).unwrap();
    assert!(matches!(
        restored_context.and(
            &context.true_condition(),
            &restored_context.true_condition(),
            &l
        ),
        Err(CheckError::ForeignCondition)
    ));
}

#[test]
fn exclusive_writer_ring_agrees_with_stable_and_supported_models_in_every_order() {
    use crate::test_support::rewrites::{atom, stable_models, supported_models};
    // Tiny version of the zoo's writer ring: each lane writes one distinct kind.
    // Enumerate unrestricted worlds too, to verify that W is still enforced.
    for writers in [2, 3] {
        let mut c = Corpus::new();
        let mut routes = Vec::new();
        let mut contexts = Vec::new();
        let mut relays = Vec::new();
        for i in 0..writers {
            let route = rel(&mut c, &format!("route{i}"), true);
            let fa = rel(&mut c, &format!("fa{i}"), true);
            let fb = rel(&mut c, &format!("fb{i}"), true);
            let context = rel(&mut c, &format!("context{i}"), false);
            rule(&mut c, context, &[(route, false), (fa, false), (fb, true)]);
            routes.push(atom(route));
            contexts.push(context);
            relays.push(rel(&mut c, &format!("relay{i}"), false));
        }
        for i in 0..writers {
            rule(
                &mut c,
                relays[i],
                &[(contexts[i], false), (relays[(i + 1) % writers], true)],
            );
        }
        let mut keys = SemanticKeys::default();
        for r in c.relations() {
            keys.bind_relation(
                &c,
                r.id,
                RelationKey::Named(QualifiedKey::new("ring", r.name.as_str())),
            )
            .unwrap();
        }
        let l = Limits::default();
        let mut raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        raw.input_groups = vec![routes.clone()];
        let atoms: Vec<_> = raw.atoms().cloned().collect();
        let inputs: BTreeSet<_> = raw.input_atoms().cloned().collect();
        let rules: Vec<_> = raw.rules().cloned().collect();
        let worlds: Vec<_> = subsets(&inputs.iter().cloned().collect::<Vec<_>>())
            .into_iter()
            .map(|world| {
                let permitted = routes.iter().filter(|a| world.contains(*a)).count() <= 1;
                let models = if permitted {
                    let stable = stable_models(&atoms, &inputs, &rules, &world);
                    assert_eq!(stable.len(), 1);
                    assert_eq!(stable, supported_models(&raw, &rules, &world));
                    Some(stable)
                } else {
                    None
                };
                (world, models)
            })
            .collect();
        for order in [
            InputOrder::Key,
            InputOrder::ReverseKey,
            InputOrder::Structural,
        ] {
            let p = raw
                .clone()
                .choose_input_order(&keys, &[], order, &mut Budget::new(&l))
                .unwrap()
                .admit(&l)
                .unwrap();
            assert_eq!(p.input_order_report().effective, order);
            assert!(p.is_admitted());
            let rewritten: Vec<_> = p.rules().cloned().collect();
            for (world, models) in &worlds {
                let replay = p.evaluate(world.iter().cloned(), &l);
                assert_eq!(replay.is_ok(), models.is_some());
                if let Some(expected) = models {
                    assert_eq!(*expected, stable_models(&atoms, &inputs, &rewritten, world));
                    assert_eq!(*expected, supported_models(&p, &rewritten, world));
                    assert_eq!(
                        *expected.first().unwrap(),
                        replay.unwrap().established_facts().cloned().collect()
                    );
                }
            }
        }
    }
}

#[test]
fn shared_supports_preserve_the_expanded_heuristic_and_edge_weights() {
    for reverse in [false, true] {
        let (mut p, k) = fixture(reverse);
        p = p.with_atom_key_order(&k).unwrap();
        p.input_groups = vec![p.inputs.iter().take(3).cloned().collect()];
        let l = Limits {
            max_work: usize::MAX,
            max_input_order_entries: usize::MAX,
            max_input_order_work: usize::MAX,
            ..Limits::default()
        };
        let mut b = Budget::new(&l);
        let mut meter = Meter {
            budget: &mut b,
            visits: 0,
            entries: 0,
            peak: 0,
            cap: usize::MAX,
            work_cap: usize::MAX,
        };
        let before = p
            .reference_place(&k, &[], &mut meter, &mut InputOrderReport::default())
            .unwrap_or_else(|_| panic!("reference cutoff"));
        let expected = before
            .iter()
            .map(|i| p.ordered_inputs()[*i].clone())
            .collect::<Vec<_>>();
        let actual = p
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&l))
            .unwrap();
        assert_eq!(
            expected,
            actual.ordered_input_atoms().cloned().collect::<Vec<_>>()
        );
    }
}

#[test]
fn a_wide_aggregate_shared_by_many_readers_no_longer_repeats_its_support() {
    let mut c = Corpus::new();
    let aggregate = rel(&mut c, "aggregate", false);
    for i in 0..600 {
        let input = rel(&mut c, &format!("input{i:04}"), true);
        rule(&mut c, aggregate, &[(input, false)]);
    }
    for i in 0..2000 {
        let reader = rel(&mut c, &format!("reader{i:04}"), false);
        rule(&mut c, reader, &[(aggregate, true)]);
    }
    let mut keys = SemanticKeys::default();
    for r in c.relations() {
        keys.bind_relation(
            &c,
            r.id,
            RelationKey::Named(QualifiedKey::new("stress", r.name.as_str())),
        )
        .unwrap();
    }
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l)
        .unwrap()
        .with_atom_key_order(&keys)
        .unwrap();
    let mut b = Budget::new(&l);
    let mut m = Meter {
        budget: &mut b,
        visits: 0,
        entries: 0,
        peak: 0,
        cap: 1_000_000,
        work_cap: 4_000_000,
    };
    assert!(
        p.reference_place(&keys, &[], &mut m, &mut InputOrderReport::default())
            .is_err()
    );
    let p = p
        .choose_input_order(&keys, &[], InputOrder::Structural, &mut Budget::new(&l))
        .unwrap();
    assert_eq!(p.input_order_report().effective, InputOrder::Structural);
    let world = p.evaluate([], &l).unwrap();
    assert_eq!(world.established_facts().count(), 2000);
}
