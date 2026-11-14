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
        rule(&mut c, out, &[(inputs[a], false), (inputs[b], false)]);
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
fn disjoint_groups_are_contiguous_and_overlapping_groups_keep_every_constraint() {
    let l = Limits::default();
    for overlap in [false, true] {
        let (mut p, k) = fixture(false);
        let original = p.inputs.iter().cloned().collect::<Vec<_>>();
        p.input_groups = vec![
            vec![original[0].clone(), original[3].clone()],
            vec![original[1].clone(), original[4].clone()],
        ];
        if overlap {
            p.input_groups.extend([
                vec![original[0].clone(), original[1].clone()],
                vec![original[3].clone(), original[4].clone()],
            ]);
        }
        let key = p
            .clone()
            .choose_input_order(&k, &[], InputOrder::Key, &mut Budget::new(&l))
            .unwrap();
        let ordered = p
            .choose_input_order(&k, &[], InputOrder::Structural, &mut Budget::new(&l))
            .unwrap();
        if !overlap {
            for g in &ordered.input_groups {
                let positions: Vec<_> = g
                    .iter()
                    .map(|a| {
                        ordered
                            .ordered_inputs()
                            .iter()
                            .position(|b| *b == a)
                            .unwrap()
                    })
                    .collect();
                assert_eq!(positions[0].abs_diff(positions[1]), 1);
            }
        }
        for world in subsets(&original) {
            assert_eq!(
                key.evaluate(world.iter().cloned(), &l).is_ok(),
                ordered.evaluate(world.iter().cloned(), &l).is_ok()
            );
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
