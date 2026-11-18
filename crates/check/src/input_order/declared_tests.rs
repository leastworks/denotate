use super::*;
use crate::test_support::rewrites::{rel, subsets};
use denotate_ir::{
    Cardinality, ConstantKey, Corpus, Literal, Parameter, QualifiedKey, RelationKey, RelationRole,
    SortKey, Term,
};

// Non-leading group column deliberately scatters groups under raw key order.
fn fixture(n: usize, kind: Cardinality, reverse: bool) -> (GroundProgram, SemanticKeys) {
    let mut c = Corpus::new();
    let mut keys = SemanticKeys::default();
    let g = c.declare_sort("Group").unwrap();
    let v = c.declare_sort("Value").unwrap();
    let mut names = (0..n).map(|i| format!("g{i:03}")).collect::<Vec<_>>();
    if reverse {
        names.reverse();
    }
    let groups: Vec<_> = names
        .iter()
        .map(|name| c.declare_constant(name, g).unwrap())
        .collect();
    let mut values = ["a", "b"];
    if reverse {
        values.reverse();
    }
    let values: Vec<_> = values
        .iter()
        .map(|name| c.declare_constant(*name, v).unwrap())
        .collect();
    let input = c
        .declare_relation(
            "value",
            RelationRole::Input,
            [Parameter::new("v", v), Parameter::new("g", g)],
        )
        .unwrap();
    c.constrain_input(input, kind, ["g".into()]).unwrap();
    let left = rel(&mut c, "left", true);
    let right = rel(&mut c, "right", true);
    let any = rel(&mut c, "any", false);
    let use_left = rel(&mut c, "use_left", false);
    let use_right = rel(&mut c, "use_right", false);
    for group in &groups {
        for value in &values {
            let a = c
                .atom(input, [Term::Constant(*value), Term::Constant(*group)])
                .unwrap();
            let head = c.atom(any, []).unwrap();
            c.add_rule(head, [Literal::Positive(a)]).unwrap();
            let (anchor, out) = if c.constant(*value).unwrap().name == "a" {
                (left, use_left)
            } else {
                (right, use_right)
            };
            for _ in 0..12 {
                let a = c
                    .atom(input, [Term::Constant(*value), Term::Constant(*group)])
                    .unwrap();
                let anchor = c.atom(anchor, []).unwrap();
                let head = c.atom(out, []).unwrap();
                c.add_rule(head, [Literal::Positive(a), Literal::Positive(anchor)])
                    .unwrap();
            }
        }
    }
    for sort in c.sorts() {
        keys.bind_sort(
            &c,
            sort.id,
            SortKey(QualifiedKey::new("groups", sort.name.as_str())),
        )
        .unwrap();
    }
    for constant in c.constants() {
        keys.bind_constant(
            &c,
            constant.id,
            ConstantKey {
                sort: keys.sort(constant.sort).unwrap().clone(),
                name: constant.name.as_str().into(),
            },
        )
        .unwrap();
    }
    for relation in c.relations() {
        keys.bind_relation(
            &c,
            relation.id,
            RelationKey::Named(QualifiedKey::new("groups", relation.name.as_str())),
        )
        .unwrap();
    }
    (
        GroundProgram::prepare(
            &c,
            &Domains::from([(g, groups), (v, values)]),
            &Limits::default(),
        )
        .unwrap(),
        keys,
    )
}

#[test]
fn declared_blocks_are_contiguous_keyed_and_have_a_grouped_fallback() {
    for kind in [Cardinality::AtMostOne, Cardinality::ExactlyOne] {
        for cap in [0, usize::MAX] {
            let mut orders = Vec::new();
            for reverse in [false, true] {
                let (p, keys) = fixture(3, kind, reverse);
                let limits = Limits::default();
                let p = p
                    .choose_input_order_bounded(
                        &keys,
                        &[],
                        InputOrder::Structural,
                        &mut Budget::new(&limits),
                        cap,
                    )
                    .unwrap();
                assert_eq!(
                    p.order_report.effective,
                    if cap == 0 {
                        EffectiveInputOrder::GroupedKey
                    } else {
                        EffectiveInputOrder::Structural
                    }
                );
                assert_eq!(p.order_report.scattered_declared_groups, 0);
                let ordered = p.ordered_inputs();
                for group in &p.universe_groups {
                    let positions: Vec<_> = ordered
                        .iter()
                        .enumerate()
                        .filter(|(_, a)| group.atoms.contains(a))
                        .map(|(i, _)| i)
                        .collect();
                    assert_eq!(
                        positions.last().unwrap() - positions[0] + 1,
                        positions.len()
                    );
                    let member_keys: Vec<_> = positions
                        .iter()
                        .map(|i| AtomKey::from_atom(&keys, ordered[*i]).unwrap())
                        .collect();
                    assert!(member_keys.windows(2).all(|p| p[0] < p[1]));
                }
                orders.push(
                    ordered
                        .into_iter()
                        .map(|a| AtomKey::from_atom(&keys, a).unwrap())
                        .collect::<Vec<_>>(),
                );
            }
            assert_eq!(orders[0], orders[1]);
        }
    }
}

#[test]
fn declared_orders_agree_with_exhaustive_worlds_including_selected_constraints() {
    for kind in [Cardinality::AtMostOne, Cardinality::ExactlyOne] {
        let (mut p, keys) = fixture(2, kind, false);
        // Overlaps the two declared blocks; selected assumptions are not blocks.
        p.input_groups = vec![
            p.universe_groups
                .iter()
                .map(|g| g.atoms[0].clone())
                .collect(),
        ];
        let limits = Limits::default();
        let inputs: Vec<_> = p.inputs.iter().cloned().collect();
        let expected = subsets(&inputs)
            .into_iter()
            .map(|world| {
                let permitted = p.universe_groups.iter().all(|g| {
                    let present = g.atoms.iter().filter(|a| world.contains(*a)).count();
                    if kind == Cardinality::ExactlyOne {
                        present == 1
                    } else {
                        present <= 1
                    }
                }) && p.input_groups[0]
                    .iter()
                    .filter(|a| world.contains(*a))
                    .count()
                    <= 1;
                let mut facts = world.clone();
                if permitted {
                    // All producers read only inputs: an independent one-step oracle.
                    for rule in &p.core.rules {
                        if rule.body.iter().all(|l| world.contains(&l.term.atom)) {
                            facts.insert(rule.head.atom.clone());
                        }
                    }
                }
                (world, permitted, facts)
            })
            .collect::<Vec<_>>();
        for (order, cap) in [
            (InputOrder::Key, usize::MAX),
            (InputOrder::ReverseKey, usize::MAX),
            (InputOrder::Structural, usize::MAX),
            (InputOrder::Structural, 0),
        ] {
            let q = p
                .clone()
                .choose_input_order_bounded(&keys, &[], order, &mut Budget::new(&limits), cap)
                .unwrap();
            assert_eq!(
                q.order_report.scattered_declared_groups,
                if order == InputOrder::Structural {
                    0
                } else {
                    2
                }
            );
            let meaning = q.symbolic(&limits).unwrap();
            for (world, permitted, facts) in &expected {
                assert_eq!(
                    meaning
                        .context()
                        .evaluate(
                            &meaning.context().permitted_worlds(),
                            world.iter().cloned(),
                            &limits
                        )
                        .is_ok(),
                    *permitted
                );
                if *permitted {
                    for (atom, condition) in &meaning.conditions {
                        assert_eq!(
                            meaning
                                .context()
                                .evaluate(condition, world.iter().cloned(), &limits)
                                .unwrap(),
                            facts.contains(atom)
                        );
                    }
                }
                let replay = q.evaluate(world.iter().cloned(), &limits);
                assert_eq!(replay.is_ok(), *permitted);
                if *permitted {
                    assert_eq!(
                        &replay
                            .unwrap()
                            .established_facts()
                            .cloned()
                            .collect::<BTreeSet<_>>(),
                        facts
                    );
                }
            }
        }
    }
}

#[test]
fn declared_group_scale_completes_with_local_masks() {
    for kind in [Cardinality::AtMostOne, Cardinality::ExactlyOne] {
        for n in [4, 8, 16, 32] {
            let (p, keys) = fixture(n, kind, false);
            let limits = Limits::default();
            if n <= 8 {
                let mut before = p.clone().with_atom_key_order(&keys).unwrap();
                let mut budget = Budget::new(&limits);
                let mut meter = Meter {
                    budget: &mut budget,
                    visits: 0,
                    entries: 0,
                    peak: 0,
                    cap: usize::MAX,
                    work_cap: usize::MAX,
                };
                let order = before
                    .reference_place(&keys, &[], &mut meter, &mut InputOrderReport::default())
                    .unwrap_or_else(|_| panic!("reference cutoff"));
                before.input_order = Some(
                    order
                        .into_iter()
                        .map(|i| before.input_order.as_ref().unwrap()[i].clone())
                        .collect(),
                );
                let meaning = before.symbolic(&limits).unwrap();
                println!(
                    "old preferences {kind:?} n={n}: U={}, largest mask={}",
                    meaning.context().permitted_worlds().node_count(),
                    meaning
                        .universe_masks
                        .iter()
                        .map(Condition::node_count)
                        .max()
                        .unwrap()
                );
            }
            let p = p
                .choose_input_order(
                    &keys,
                    &[],
                    InputOrder::Structural,
                    &mut Budget::new(&limits),
                )
                .unwrap();
            let meaning = p.symbolic(&limits).unwrap();
            assert!(meaning.is_complete());
            let u = meaning.context().permitted_worlds().node_count();
            let mask = meaning
                .universe_masks
                .iter()
                .map(Condition::node_count)
                .max()
                .unwrap();
            println!("declared groups {kind:?} n={n}: U={u}, largest mask={mask}");
            // Completion is the regression contract; node measurements are not goldens.
            for group in &p.universe_groups {
                assert!(meaning.conditions.contains_key(&group.atoms[0]));
            }
        }
    }
}
