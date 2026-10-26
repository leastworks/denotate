use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;
pub fn assert_symbolic_agrees(program: &GroundProgram) {
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
                GroupOutcome::Inconclusive(cause) => panic!("unexpected limit: {cause:?}"),
            }
        }
    }
    let verified = symbolic.verify_at_most_one(&limits).unwrap();
    assert_eq!(verified.whole_program_admitted(), program.is_admitted());
    for group in &verified.groups {
        if let VerifiedOutcome::Counterexample(example) = &group.outcome {
            assert!(
                example
                    .observation
                    .present
                    .is_disjoint(&example.observation.absent)
            );
            assert_eq!(
                example
                    .observation
                    .present
                    .union(&example.observation.absent)
                    .cloned()
                    .collect::<BTreeSet<_>>(),
                inputs.iter().cloned().collect()
            );
            let replay = program
                .evaluate(example.observation.present.iter().cloned(), &limits)
                .unwrap();
            assert!(example.tuples.len() >= 2);
            for tuple in &example.tuples {
                assert_eq!(replay.fact(tuple).unwrap(), FactState::Settled(true));
            }
            assert_eq!(
                example.replay_scope == ReplayScope::WholeProgram,
                program.is_admitted()
                    || matches!(
                        example.certification,
                        Some(CertificationOutcome::Certified(_))
                    )
            );
            for (fact, step) in &example.evidence {
                assert_eq!(replay.fact(fact).unwrap(), FactState::Settled(true));
                if let GroundEvidence::Derived { rule, premises } = &step.evidence {
                    assert_eq!(&rule.head.atom, fact);
                    assert_eq!(program.rule(rule.id), Some(rule));
                    assert_eq!(rule.body.len(), premises.len());
                    for premise in premises {
                        match premise {
                            PremiseEvidence::Discharged { .. } => {
                                panic!("baseline did not run admission rewrites")
                            }
                            PremiseEvidence::Positive { fact, .. } => {
                                assert!(example.evidence[fact].order < step.order)
                            }
                            PremiseEvidence::Absent { fact, provider, .. } => {
                                if let Some(CertificationOutcome::Certified(certified)) =
                                    &example.certification
                                {
                                    assert!(!certified.facts.contains(fact));
                                    match provider {
                                        CompletedProvider::Component(id) => {
                                            assert!(certified.providers[id].contains(fact))
                                        }
                                        CompletedProvider::InputSnapshot => {
                                            assert!(certified.observation.absent.contains(fact))
                                        }
                                        CompletedProvider::NoPossibleProducer => {
                                            assert!(!program.is_possible(fact).unwrap())
                                        }
                                    }
                                } else {
                                    assert_eq!(
                                        replay.absence_provider(fact).unwrap().as_ref(),
                                        Some(provider)
                                    );
                                }
                            }
                        }
                    }
                } else {
                    assert!(example.observation.present.contains(fact));
                }
            }
        }
    }
}

pub fn relation(c: &mut Corpus, name: &str, input: bool) -> RelationId {
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
pub fn rule(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)]) -> RuleId {
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
pub fn condition(m: &SymbolicMeaning<'_>, atom: GroundAtom) -> Condition {
    match m.fact(&atom).unwrap() {
        SymbolicFact::Settled(c) => c,
        s => panic!("{s:?}"),
    }
}
pub fn nullary(r: RelationId) -> GroundAtom {
    GroundAtom::new(r, [])
}
