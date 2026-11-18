use crate::{
    limits::Budget,
    test_support::symbolic::{nullary, relation, rule},
    *,
};
use denotate_ir::*;

#[test]
fn assumption_cones_preserve_whole_program_w_and_input_order() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let x = c.declare_constant("x", s).unwrap();
    let y = c.declare_constant("y", s).unwrap();
    let input = c
        .declare_relation("input", RelationRole::Input, [Parameter::new("x", s)])
        .unwrap();
    let outside = relation(&mut c, "outside", true);
    let derived = c
        .declare_relation("derived", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let head = c.atom(derived, [Term::variable("X", s)]).unwrap();
    let body = c.atom(input, [Term::variable("X", s)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    // Transitive stratified negation, not just an input copy.
    let absent = relation(&mut c, "absent", false);
    let h = c.atom(absent, []).unwrap();
    let b = c.atom(derived, [Term::Constant(x)]).unwrap();
    c.add_rule(h, [Literal::Negative(b)]).unwrap();
    let d = Domains::from([(s, vec![x, y])]);
    let limits = Limits::default();
    let inputs = vec![
        GroundAtom::new(input, [x]),
        nullary(outside),
        GroundAtom::new(input, [y]),
    ];
    for reverse in [false, true] {
        let mut order = inputs.clone();
        if reverse {
            order.reverse();
        }
        with_test_input_order(order, || {
            let raw = GroundProgram::prepare(&c, &d, &limits).unwrap();
            let whole = raw.symbolic(&limits).unwrap();
            for kind in [
                Cardinality::Empty,
                Cardinality::AtMostOne,
                Cardinality::AtLeastOne,
                Cardinality::ExactlyOne,
            ] {
                for grouped in [false, true] {
                    if kind == Cardinality::Empty && grouped {
                        continue;
                    }
                    let group_by = if grouped { vec![0] } else { vec![] };
                    let restriction = match kind {
                        Cardinality::Empty => Restriction::Empty { relation: derived },
                        Cardinality::AtMostOne => Restriction::AtMostOne {
                            relation: derived,
                            group_by,
                        },
                        Cardinality::AtLeastOne => Restriction::AtLeastOne {
                            relation: derived,
                            group_by,
                        },
                        Cardinality::ExactlyOne => Restriction::ExactlyOne {
                            relation: derived,
                            group_by,
                        },
                    };
                    for select_absent in [false, true] {
                        let mut restrictions = vec![restriction.clone()];
                        if select_absent {
                            restrictions.push(Restriction::Empty { relation: absent });
                        }
                        let mut scoped = raw.clone();
                        scoped
                            .install_assumptions(&restrictions, None, &mut Budget::new(&limits))
                            .unwrap();
                        let w = scoped
                            .condition_context(&limits)
                            .unwrap()
                            .permitted_worlds();
                        for bits in 0usize..8 {
                            let world = inputs
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| bits & (1 << i) != 0)
                                .map(|(_, a)| a.clone())
                                .collect::<Vec<_>>();
                            let count = [x, y]
                                .into_iter()
                                .filter(|v| {
                                    let SymbolicFact::Settled(value) =
                                        whole.fact(&GroundAtom::new(derived, [*v])).unwrap()
                                    else {
                                        panic!()
                                    };
                                    whole
                                        .context()
                                        .evaluate(&value, world.clone(), &limits)
                                        .unwrap()
                                })
                                .count();
                            let expected = match kind {
                                Cardinality::Empty => count == 0,
                                Cardinality::AtMostOne => grouped || count <= 1,
                                Cardinality::AtLeastOne => count >= if grouped { 2 } else { 1 },
                                Cardinality::ExactlyOne => {
                                    if grouped {
                                        count == 2
                                    } else {
                                        count == 1
                                    }
                                }
                            } && (!select_absent || world.contains(&inputs[0]));
                            // The unrestricted context evaluates W even on excluded worlds.
                            assert_eq!(
                                whole.context().evaluate(&w, world, &limits).unwrap(),
                                expected,
                                "{kind:?}, grouped={grouped}, bits={bits}"
                            );
                        }
                    }
                }
            }
            let mut empty = raw.clone();
            empty
                .install_assumptions(&[], None, &mut Budget::new(&limits))
                .unwrap();
            assert!(
                empty
                    .condition_context(&limits)
                    .unwrap()
                    .permitted_worlds()
                    .is_true()
            );
        });
    }
}

#[test]
fn assumption_cones_skip_unrelated_exhaustion_but_preserve_reports() {
    let mut c = Corpus::new();
    let selected = relation(&mut c, "selected", true);
    let wide = relation(&mut c, "wide", false);
    for i in 0..8 {
        let input = relation(&mut c, &format!("input_{i}"), true);
        rule(&mut c, wide, &[(input, false)]);
    }
    let blocked = relation(&mut c, "blocked", false);
    rule(&mut c, blocked, &[(blocked, true)]);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let failed = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let observed = failed.clone();
    let profile = Profile::new(|_| {});
    profile.observe_conditions(move |event| {
        if matches!(
            event.observation,
            ConditionObservation::FailedOperation { .. }
        ) {
            observed.store(true, std::sync::atomic::Ordering::Relaxed);
        }
    });
    let low = Limits {
        profile,
        max_bdd_nodes: 5,
        ..limits
    };
    let whole = raw.symbolic(&low).unwrap();
    assert!(matches!(
        whole.fact(&nullary(wide)).unwrap(),
        SymbolicFact::Inconclusive(_)
    ));
    assert!(failed.swap(false, std::sync::atomic::Ordering::Relaxed));
    let mut scoped = raw.clone();
    scoped
        .install_assumptions(
            &[Restriction::AtLeastOne {
                relation: selected,
                group_by: vec![],
            }],
            None,
            &mut Budget::new(&low),
        )
        .unwrap();
    assert!(
        !failed.load(std::sync::atomic::Ordering::Relaxed),
        "unrelated evaluation must not run during W construction"
    );
    // Scoping preparation must not remove executable components or their reports.
    let admitted = scoped.admit(&low).unwrap();
    assert!(!admitted.is_admitted());
    let after = admitted.symbolic(&low).unwrap();
    assert!(matches!(
        after.fact(&nullary(blocked)).unwrap(),
        SymbolicFact::Blocked(_)
    ));
    assert!(matches!(
        after.fact(&nullary(wide)).unwrap(),
        SymbolicFact::Inconclusive(_)
    ));
    // The same exhaustion inside the selected cone remains an explicit failure.
    let mut needed = raw.clone();
    assert!(
        needed
            .install_assumptions(
                &[Restriction::AtLeastOne {
                    relation: wide,
                    group_by: vec![]
                }],
                None,
                &mut Budget::new(&low)
            )
            .is_err()
    );
    assert!(needed.assumption_condition.is_none());
}
