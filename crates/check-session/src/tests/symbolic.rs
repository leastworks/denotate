pub(super) use denotate_check::test_support::symbolic::assert_symbolic_agrees;
use denotate_check::test_support::symbolic::*;
use denotate_check::*;
use denotate_ir::*;
use denotate_test_dsl::library;
use std::time::Duration;
struct Mapping {
    corpus: Corpus,
    library: library::MappingLibrary,
    inputs: Vec<ConstantId>,
    slots: Vec<ConstantId>,
}
impl Mapping {
    fn new() -> Self {
        let mut corpus = Corpus::new();
        let library = library::build(&mut corpus).unwrap();
        let inputs = ["ia", "ib", "ibb", "ic", "id", "idd"]
            .into_iter()
            .map(|name| corpus.declare_constant(name, library.input).unwrap())
            .collect();
        let slots = ["a", "b", "c", "d"]
            .into_iter()
            .map(|name| corpus.declare_constant(name, library.slot).unwrap())
            .collect();
        Self {
            corpus,
            library,
            inputs,
            slots,
        }
    }
    fn available(&self, slot: usize) -> GroundAtom {
        GroundAtom::new(self.library.available, [self.slots[slot]])
    }
    fn present(&self, input: usize) -> GroundAtom {
        GroundAtom::new(self.library.value, [self.inputs[input], self.library.other])
    }
    fn supply(&self, input: usize, slot: usize) -> GroundAtom {
        GroundAtom::new(
            self.library.supplies,
            [self.inputs[input], self.slots[slot]],
        )
    }
    fn mapping(&mut self, input: usize, slot: usize, guards: Vec<(GroundAtom, bool)>) -> RuleId {
        let head = self
            .corpus
            .atom(
                self.library.mapped_to,
                [self.inputs[input].into(), self.slots[slot].into()],
            )
            .unwrap();
        let body: Vec<_> = guards
            .into_iter()
            .map(|(atom, neg)| {
                let a = self
                    .corpus
                    .atom(atom.relation, atom.arguments.into_iter().map(Term::from))
                    .unwrap();
                if neg {
                    Literal::Negative(a)
                } else {
                    Literal::Positive(a)
                }
            })
            .collect();
        self.corpus.add_rule(head, body).unwrap()
    }
    fn prepare(&self) -> GroundProgram {
        GroundProgram::prepare(
            &self.corpus,
            &Domains::from([
                (self.library.input, self.inputs.clone()),
                (self.library.slot, self.slots.clone()),
                (self.library.integer, vec![self.library.other]),
            ]),
            &Limits::default(),
        )
        .unwrap()
    }
}

#[test]
fn overlap_is_exactly_the_three_input_conjunction_and_preserves_the_full_cone() {
    let mut f = Mapping::new();
    f.mapping(0, 0, vec![]);
    let left = f.mapping(1, 1, vec![(f.available(0), false)]);
    let right = f.mapping(2, 1, vec![(f.available(0), false)]);
    let p = f.prepare();
    assert_symbolic_agrees(&p);
    let limits = Limits::default();
    let m = p.symbolic(&limits).unwrap();
    let report = m.check_at_most_one(&limits).unwrap();
    assert!(report.whole_program_admitted);
    assert_eq!(report.groups.len(), 1);
    let check = &report.groups[0];
    assert_eq!(check.group.obligation, f.library.unique_input);
    assert_eq!(check.group.key, [f.slots[1]]);
    assert!(check.cone.facts.contains(&f.available(0)));
    assert!(
        check
            .cone
            .rules
            .iter()
            .any(|id| p.rule(*id).unwrap().source == left)
    );
    assert!(
        check
            .cone
            .rules
            .iter()
            .any(|id| p.rule(*id).unwrap().source == right)
    );
    let GroupOutcome::Overlap(overlap) = &check.outcome else {
        panic!("{:?}", check.outcome)
    };
    let ctx = m.context();
    let x = ctx.input(&f.present(0), &limits).unwrap();
    let y = ctx.input(&f.present(1), &limits).unwrap();
    let z = ctx.input(&f.present(2), &limits).unwrap();
    assert!(
        ctx.equivalent(&condition(&m, f.available(0)), &x, &limits)
            .unwrap()
    );
    let xy = ctx.and(&x, &y, &limits).unwrap();
    let xz = ctx.and(&x, &z, &limits).unwrap();
    assert!(
        ctx.equivalent(&condition(&m, f.supply(1, 1)), &xy, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(&condition(&m, f.supply(2, 1)), &xz, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(overlap, &ctx.and(&xy, &z, &limits).unwrap(), &limits)
            .unwrap()
    );
    for bits in 0..64 {
        let observation = (0..6)
            .filter(|i| bits & (1 << i) != 0)
            .map(|i| f.present(i));
        assert_eq!(
            ctx.evaluate(overlap, observation, &limits).unwrap(),
            bits & 7 == 7
        );
    }
}

#[test]
fn complementary_guards_prove_while_duplicate_paths_and_one_input_many_slots_are_not_conflicts() {
    let limits = Limits::default();
    let mut f = Mapping::new();
    f.mapping(0, 0, vec![]);
    f.mapping(1, 1, vec![(f.available(0), false)]);
    f.mapping(2, 1, vec![(f.available(0), true)]);
    let p = f.prepare();
    assert_symbolic_agrees(&p);
    assert!(matches!(
        p.symbolic(&limits)
            .unwrap()
            .check_at_most_one(&limits)
            .unwrap()
            .groups[0]
            .outcome,
        GroupOutcome::Proved
    ));
    let mut f = Mapping::new();
    f.mapping(1, 1, vec![]);
    f.mapping(1, 1, vec![]); // Distinct statements, same tuple.
    f.mapping(1, 1, vec![(f.present(0), false)]); // Another OR alternative.
    f.mapping(1, 0, vec![]); // Same Input may populate another Slot.
    let p = f.prepare();
    assert_symbolic_agrees(&p);
    let m = p.symbolic(&limits).unwrap();
    assert!(m.check_at_most_one(&limits).unwrap().groups.is_empty());
    assert!(
        m.context()
            .equivalent(
                &condition(&m, f.supply(1, 1)),
                &m.context().input(&f.present(1), &limits).unwrap(),
                &limits,
            )
            .unwrap()
    );
}

#[test]
fn independent_overlap_survives_blocked_groups_without_narrowing_input_worlds() {
    let limits = Limits::default();
    for require_ic in [false, true] {
        for broken_c in [false, true] {
            let mut f = Mapping::new();
            f.mapping(0, 0, vec![]);
            f.mapping(1, 1, vec![(f.available(0), false)]);
            let mut guards = vec![(f.available(0), false)];
            if require_ic {
                guards.push((f.present(3), false));
            }
            f.mapping(2, 1, guards);
            let c_rule = f.mapping(
                3,
                2,
                if broken_c {
                    vec![(f.available(2), true)]
                } else {
                    vec![]
                },
            );
            f.mapping(4, 3, vec![(f.available(2), true)]);
            f.mapping(5, 3, vec![]);
            let p = f.prepare();
            assert_symbolic_agrees(&p);
            let m = p.symbolic(&limits).unwrap();
            let report = m.check_at_most_one(&limits).unwrap();
            assert_eq!(report.whole_program_admitted, !broken_c);
            assert_eq!(report.unresolved_components.len(), usize::from(broken_c));
            assert_eq!(report.groups.len(), 2);
            let b = report
                .groups
                .iter()
                .find(|g| g.group.key == [f.slots[1]])
                .unwrap();
            let d = report
                .groups
                .iter()
                .find(|g| g.group.key == [f.slots[3]])
                .unwrap();
            let GroupOutcome::Overlap(overlap) = &b.outcome else {
                panic!("{:?}", b.outcome)
            };
            assert!(b.cone.blocked_by.is_empty());
            assert!(!b.cone.facts.contains(&f.available(2)));
            assert!(
                !b.cone
                    .rules
                    .iter()
                    .any(|id| p.rule(*id).unwrap().source == c_rule)
            );
            for bits in 0..64 {
                let observation = (0..6)
                    .filter(|i| bits & (1 << i) != 0)
                    .map(|i| f.present(i));
                assert_eq!(
                    m.context().evaluate(overlap, observation, &limits).unwrap(),
                    bits & 7 == 7 && (!require_ic || bits & 8 != 0)
                );
            }
            if broken_c {
                assert!(matches!(d.outcome, GroupOutcome::Unsupported));
                assert!(!d.cone.blocked_by.is_empty());
                assert!(matches!(
                    m.fact(&f.supply(4, 3)).unwrap(),
                    SymbolicFact::Blocked(_)
                ));
                assert!(matches!(
                    m.fact(&f.available(2)).unwrap(),
                    SymbolicFact::Blocked(_)
                ));
            } else {
                assert!(matches!(d.outcome, GroupOutcome::Overlap(_)));
            }
        }
    }
}

#[test]
fn bdd_and_property_limits_return_errors_not_successful_partial_results() {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let y = relation(&mut c, "y", true);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    for low in [
        Limits {
            max_bdd_variables: 1,
            ..limits.clone()
        },
        Limits {
            max_bdd_nodes: 2,
            ..limits.clone()
        },
        Limits {
            max_condition_nodes: 5,
            ..limits.clone()
        },
        Limits {
            max_work: 0,
            ..limits.clone()
        },
    ] {
        assert!(matches!(
            p.symbolic(&low),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
    assert!(matches!(
        p.symbolic(&Limits {
            timeout: Duration::ZERO,
            ..limits.clone()
        }),
        Err(CheckError::Deadline { .. })
    ));
    let ctx = p.condition_context(&limits).unwrap();
    let x = ctx.input(&nullary(x), &limits).unwrap();
    let y = ctx.input(&nullary(y), &limits).unwrap();
    assert!(!ctx.equivalent(&x, &y, &limits).unwrap());
    for low in [
        Limits {
            max_bdd_tasks: 0,
            ..limits.clone()
        },
        Limits {
            max_bdd_nodes: 3,
            ..limits.clone()
        },
        Limits {
            max_work: 0,
            ..limits.clone()
        },
    ] {
        assert!(matches!(
            ctx.equivalent(&x, &y, &low),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
    assert!(matches!(
        ctx.and(
            &x,
            &y,
            &Limits {
                max_bdd_tasks: 0,
                ..limits.clone()
            }
        ),
        Err(CheckError::LimitExceeded {
            resource: "BDD tasks",
            ..
        })
    ));
    assert!(matches!(
        ctx.and(
            &x,
            &y,
            &Limits {
                max_bdd_nodes: 3,
                ..limits.clone()
            }
        ),
        Err(CheckError::LimitExceeded {
            resource: "BDD nodes",
            ..
        })
    ));
    let mut f = Mapping::new();
    f.mapping(1, 1, vec![]);
    f.mapping(2, 1, vec![]);
    let p = f.prepare();
    let m = p.symbolic(&limits).unwrap();
    for low in [
        Limits {
            max_work: 0,
            ..limits.clone()
        },
        Limits {
            max_bdd_tasks: 0,
            ..limits.clone()
        },
        Limits {
            max_condition_nodes: 0,
            ..limits.clone()
        },
    ] {
        match m.check_at_most_one(&low) {
            Err(CheckError::LimitExceeded { .. }) => {}
            Ok(report) => assert!(
                report
                    .groups
                    .iter()
                    .all(|g| matches!(g.outcome, GroupOutcome::Inconclusive(_)))
            ),
            other => panic!("unexpected result: {other:?}"),
        }
    }
}
