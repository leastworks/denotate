use crate::*;
use denotate_ir::*;
use denotate_test_dsl::library;
use std::{
    collections::BTreeSet,
    time::{Duration, Instant},
};

pub(super) fn assert_symbolic_agrees(program: &GroundProgram) {
    let limits = Limits::default();
    let symbolic = program.symbolic(&limits).unwrap();
    let report = symbolic.check_at_most_one(&limits).unwrap();
    let inputs: Vec<_> = program.input_atoms().cloned().collect();
    assert!(inputs.len() <= 10);
    assert_eq!(symbolic.is_complete(), program.is_admitted());
    for bits in 0..(1usize << inputs.len()) {
        let present: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, a)| a.clone())
            .collect();
        let concrete = program.evaluate(present.clone(), &limits).unwrap();
        for atom in program.atoms() {
            match (symbolic.fact(atom).unwrap(), concrete.fact(atom).unwrap()) {
                (SymbolicFact::Settled(c), FactState::Settled(expected)) => {
                    assert_eq!(
                        symbolic
                            .context()
                            .evaluate(&c, present.clone(), &limits)
                            .unwrap(),
                        expected,
                        "atom {atom:?}, observation {bits}"
                    );
                }
                (SymbolicFact::Blocked(a), FactState::Blocked(b)) => assert_eq!(a, b),
                states => panic!("atom {atom:?}, observation {bits}: {states:?}"),
            }
        }
        for check in &report.groups {
            if !check.cone.blocked_by.is_empty() {
                assert!(matches!(check.outcome, GroupOutcome::Unsupported));
                continue;
            }
            let count = check
                .group
                .tuples
                .iter()
                .filter(|atom| concrete.fact(atom).unwrap() == FactState::Settled(true))
                .count();
            match &check.outcome {
                GroupOutcome::Proved => assert!(count <= 1),
                GroupOutcome::Overlap(condition) => assert_eq!(
                    symbolic
                        .context()
                        .evaluate(condition, present.clone(), &limits)
                        .unwrap(),
                    count > 1,
                    "group {:?}, observation {bits}",
                    check.group.key
                ),
                GroupOutcome::Unsupported => panic!("admitted cone was not checked"),
            }
        }
    }
}

fn relation(c: &mut Corpus, name: &str, input: bool) -> RelationId {
    c.declare_relation(
        name,
        if input {
            RelationRole::Input
        } else {
            RelationRole::Derived
        },
        [],
    )
    .unwrap()
}
fn rule(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)]) -> RuleId {
    let h = c.atom(head, []).unwrap();
    let b: Vec<_> = body
        .iter()
        .map(|(r, negative)| {
            let a = c.atom(*r, []).unwrap();
            if *negative {
                Literal::Negative(a)
            } else {
                Literal::Positive(a)
            }
        })
        .collect();
    c.add_rule(h, b).unwrap()
}
fn condition(m: &SymbolicMeaning<'_>, atom: GroundAtom) -> Condition {
    match m.fact(&atom).unwrap() {
        SymbolicFact::Settled(c) => c,
        s => panic!("{s:?}"),
    }
}
fn nullary(r: RelationId) -> GroundAtom {
    GroundAtom::new(r, [])
}

#[test]
fn boolean_queries_do_not_require_admissibility_and_reject_foreign_conditions() {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let bad = relation(&mut c, "bad", false);
    rule(&mut c, bad, &[(bad, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert!(!p.is_admitted());
    let ctx = p.condition_context(&limits).unwrap();
    let x_c = ctx.input(&nullary(x), &limits).unwrap();
    let not_x = ctx.not(&x_c, &limits).unwrap();
    let never = ctx.and(&x_c, &not_x, &limits).unwrap();
    let always = ctx.or(&x_c, &not_x, &limits).unwrap();
    assert!(!never.can_hold());
    assert!(!always.can_fail());
    assert!(x_c.can_hold() && x_c.can_fail());
    assert!(!ctx.may_overlap(&x_c, &not_x, &limits).unwrap());
    assert!(ctx.implies(&x_c, &always, &limits).unwrap());
    assert!(!ctx.implies(&always, &x_c, &limits).unwrap());
    assert!(
        ctx.equivalent(&ctx.not(&not_x, &limits).unwrap(), &x_c, &limits)
            .unwrap()
    );
    assert!(ctx.input(&nullary(bad), &limits).is_err());
    assert!(ctx.evaluate(&x_c, [nullary(bad)], &limits).is_err());
    let other = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let foreign = other.condition_context(&limits).unwrap().true_condition();
    assert!(matches!(
        ctx.and(&x_c, &foreign, &limits),
        Err(CheckError::ForeignCondition)
    ));
    assert!(matches!(
        ctx.not(&foreign, &limits),
        Err(CheckError::ForeignCondition)
    ));
    assert_eq!(
        ctx.equivalent(&x_c, &foreign, &limits),
        Err(CheckError::ForeignCondition)
    );
    assert_eq!(
        ctx.evaluate(&foreign, [], &limits),
        Err(CheckError::ForeignCondition)
    );
    // Recreating a context for the SAME immutable program uses the same universe.
    let same = p
        .condition_context(&limits)
        .unwrap()
        .input(&nullary(x), &limits)
        .unwrap();
    assert!(ctx.equivalent(&x_c, &same, &limits).unwrap());
}

#[test]
fn acyclic_components_skip_confirmation_without_losing_alternative_derivations() {
    for length in [8, 64] {
        let limits = Limits::default();
        let mut c = Corpus::new();
        let x = relation(&mut c, "x", true);
        let y = relation(&mut c, "y", true);
        let mut head = x;
        for n in 0..length {
            let next = relation(&mut c, &format!("r{n}"), false);
            rule(&mut c, next, &[(head, false)]);
            // Multiple producers must all run even without an internal edge.
            rule(&mut c, next, &[(y, false)]);
            head = next;
        }
        let mut p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        assert!(p.components().all(|c| !c.recursive));
        assert_symbolic_agrees(&p);
        let m = p.symbolic(&limits).unwrap();
        let expected: Vec<_> = p
            .atoms()
            .map(|a| (a.clone(), condition(&m, a.clone())))
            .collect();
        let one_pass_work = m.metrics().work;
        let ctx = m.context();
        let either = ctx
            .or(
                &ctx.input(&nullary(x), &limits).unwrap(),
                &ctx.input(&nullary(y), &limits).unwrap(),
                &limits,
            )
            .unwrap();
        assert!(
            ctx.equivalent(&condition(&m, nullary(head)), &either, &limits)
                .unwrap()
        );
        drop(m);

        // Test-only conservative schedule: force the former extra pass while
        // leaving the same program and its input universe intact.
        for component in &mut p.components {
            component.recursive = true;
        }
        let conservative = p.symbolic(&limits).unwrap();
        for (atom, expected) in expected {
            assert!(
                conservative
                    .context()
                    .equivalent(&condition(&conservative, atom), &expected, &limits)
                    .unwrap()
            );
        }
        assert!(conservative.metrics().work > one_pass_work);
    }
}

#[test]
fn long_growing_guard_chain_exceeds_default_limits_without_a_successful_meaning() {
    let limits = Limits::default();
    let size = 1_000;
    let (corpus, domains) = super::sparse::mapping_corpus(size, true);
    let program = GroundProgram::prepare(&corpus, &domains, &limits).unwrap();
    assert!(program.is_admitted());
    assert!(program.components().all(|c| !c.recursive));
    assert_eq!(program.atoms().count(), 4 * size);
    assert_eq!(program.rules().count(), 3 * size);
    assert_eq!(program.dependencies().count(), 4 * size - 1);
    let replay = program
        .evaluate(program.input_atoms().cloned(), &limits)
        .unwrap();
    assert_eq!(replay.established_facts().count(), 4 * size);

    // Sparse grounding and concrete replay succeed, but retaining all growing
    // prefix conditions in independently owned BDD vectors exceeds the current
    // defaults. Revisit this expectation if the backend/storage model changes.
    assert!(matches!(
        program.symbolic(&limits),
        Err(CheckError::LimitExceeded { .. })
    ));
}

#[test]
#[ignore = "manual growing-condition measurement; run alone with --release --nocapture"]
fn measure_growing_guard_chain() {
    let limits = Limits::default();
    println!(
        "slots,atoms,rules,dependencies,prepare_ms,symbolic_ms,replay_ms,retained_nodes,work,result"
    );
    for size in [20, 100, 250, 500, 1_000] {
        let (corpus, domains) = super::sparse::mapping_corpus(size, true);
        let start = Instant::now();
        let program = GroundProgram::prepare(&corpus, &domains, &limits).unwrap();
        let prepare_ms = start.elapsed().as_secs_f64() * 1_000.0;
        let start = Instant::now();
        let result = program.symbolic(&limits);
        let symbolic_ms = start.elapsed().as_secs_f64() * 1_000.0;
        let start = Instant::now();
        let replay = program
            .evaluate(program.input_atoms().cloned(), &limits)
            .unwrap();
        let replay_ms = start.elapsed().as_secs_f64() * 1_000.0;
        assert_eq!(replay.established_facts().count(), 4 * size);
        let (nodes, work, status) = match result {
            Ok(meaning) => {
                // Inputs, mapped_to, supplies and available all retain a condition.
                let expected = (3 * size * size + 19 * size) / 2;
                assert_eq!(meaning.metrics().retained_condition_nodes, expected);
                (
                    expected.to_string(),
                    meaning.metrics().work.to_string(),
                    "complete".to_owned(),
                )
            }
            Err(CheckError::LimitExceeded { phase, resource }) => (
                "-".to_owned(),
                "-".to_owned(),
                format!("LimitExceeded: {phase}/{resource}"),
            ),
            Err(error) => panic!("unexpected measurement failure: {error}"),
        };
        println!(
            "{size},{},{},{},{prepare_ms:.2},{symbolic_ms:.2},{replay_ms:.2},{nodes},{work},{status}",
            program.atoms().count(),
            program.rules().count(),
            program.dependencies().count()
        );
    }
}

#[test]
fn recursive_conditions_keep_broadening_until_their_meanings_stabilize() {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let y = relation(&mut c, "y", true);
    let p = relation(&mut c, "p", false);
    let q = relation(&mut c, "q", false);
    let not_p = relation(&mut c, "not_p", false);
    let dead = relation(&mut c, "dead", false);
    let not_dead = relation(&mut c, "not_dead", false);
    let impossible = relation(&mut c, "impossible", false);
    let not_impossible = relation(&mut c, "not_impossible", false);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(p, false)]);
    rule(&mut c, p, &[(x, false)]);
    rule(&mut c, q, &[(y, false)]);
    // Once p covers x OR y, this narrower derivation adds no worlds.
    rule(&mut c, p, &[(x, false), (y, false)]);
    rule(&mut c, not_p, &[(p, true)]);
    rule(&mut c, dead, &[(dead, false)]);
    rule(&mut c, not_dead, &[(dead, true)]);
    rule(&mut c, impossible, &[(x, false), (x, true)]);
    rule(&mut c, not_impossible, &[(impossible, true)]);
    let limits = Limits::default();
    let program = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert_symbolic_agrees(&program);
    let m = program.symbolic(&limits).unwrap();
    let ctx = m.context();
    let either = ctx
        .or(
            &ctx.input(&nullary(x), &limits).unwrap(),
            &ctx.input(&nullary(y), &limits).unwrap(),
            &limits,
        )
        .unwrap();
    assert!(
        ctx.equivalent(&condition(&m, nullary(p)), &either, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(&condition(&m, nullary(q)), &either, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(
            &condition(&m, nullary(not_p)),
            &ctx.not(&either, &limits).unwrap(),
            &limits,
        )
        .unwrap()
    );
    assert!(condition(&m, nullary(dead)).is_false());
    assert!(condition(&m, nullary(not_dead)).is_true());
    assert!(!m.conditions.contains_key(&nullary(dead)));
    assert!(program.is_possible(&nullary(impossible)).unwrap());
    assert!(condition(&m, nullary(impossible)).is_false());
    assert!(condition(&m, nullary(not_impossible)).is_true());
    assert!(!m.conditions.contains_key(&nullary(impossible)));
    let cone = program
        .dependency_cone([nullary(not_dead)], &limits)
        .unwrap();
    assert!(cone.facts.contains(&nullary(dead))); // Structural absence, no component.
    assert_eq!(cone.components.len(), 1);
}

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
        GroundAtom::new(self.library.present, [self.inputs[input]])
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
fn cone_retains_other_producers_even_if_a_true_alternative_hides_them_booleanly() {
    let mut c = Corpus::new();
    let t = relation(&mut c, "t", true);
    let bad = relation(&mut c, "bad", false);
    let out = relation(&mut c, "out", false);
    rule(&mut c, bad, &[(bad, true)]);
    let first = rule(&mut c, out, &[]);
    let second = rule(&mut c, out, &[(t, false), (bad, false)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let m = p.symbolic(&limits).unwrap();
    assert!(matches!(
        m.fact(&nullary(out)).unwrap(),
        SymbolicFact::Blocked(_)
    ));
    let cone = p.dependency_cone([nullary(out)], &limits).unwrap();
    let sources: BTreeSet<_> = cone
        .rules
        .iter()
        .map(|id| p.rule(*id).unwrap().source)
        .collect();
    assert!(sources.contains(&first) && sources.contains(&second));
    assert!(cone.facts.contains(&nullary(t)));
    assert!(cone.facts.contains(&nullary(bad)));
    assert_eq!(cone.blocked_by.len(), 1);
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
        Limits {
            timeout: Duration::ZERO,
            ..limits.clone()
        },
    ] {
        assert!(matches!(
            p.symbolic(&low),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
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
        Limits {
            timeout: Duration::ZERO,
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
        Limits {
            timeout: Duration::ZERO,
            ..limits.clone()
        },
    ] {
        assert!(matches!(
            m.check_at_most_one(&low),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
}

#[test]
fn constant_groups_work_with_zero_input_variables_including_trivial_groups() {
    let limits = Limits::default();
    for count in [0, 1, 3] {
        let mut c = Corpus::new();
        let s = c.declare_sort("Value").unwrap();
        let values: Vec<_> = (0..3)
            .map(|i| c.declare_constant(format!("v{i}"), s).unwrap())
            .collect();
        let r = c
            .declare_relation("r", RelationRole::Derived, [Parameter::new("value", s)])
            .unwrap();
        for value in &values[..count] {
            let head = c.atom(r, [(*value).into()]).unwrap();
            c.add_rule(head, []).unwrap();
        }
        c.at_most_one("one", r, Vec::<Column>::new(), "one value")
            .unwrap();
        let p = GroundProgram::prepare(&c, &Domains::from([(s, values)]), &limits).unwrap();
        assert_symbolic_agrees(&p);
        let m = p.symbolic(&limits).unwrap();
        assert_eq!(m.context().inputs().count(), 0);
        let report = m.check_at_most_one(&limits).unwrap();
        assert!(report.whole_program_admitted);
        if count <= 1 {
            assert!(report.groups.is_empty());
        } else {
            assert_eq!(report.groups.len(), 1);
            assert_eq!(report.groups[0].group.tuples.len(), 3);
            let GroupOutcome::Overlap(overlap) = &report.groups[0].outcome else {
                panic!("missing constant conflict")
            };
            assert!(overlap.is_true());
            assert!(m.context().evaluate(overlap, [], &limits).unwrap());
        }
    }
}
