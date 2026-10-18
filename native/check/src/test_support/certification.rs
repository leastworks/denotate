use super::rewrites::{stable_models, subsets};
use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;
pub fn compare(c: &Corpus, domains: &Domains, admit: bool) -> usize {
    let limits = Limits::default();
    let oracle = GroundProgram::prepare_cartesian(c, domains, &limits).unwrap();
    let atoms: Vec<_> = oracle.atoms().cloned().collect();
    let inputs: BTreeSet<_> = oracle.input_atoms().cloned().collect();
    let rules: Vec<_> = oracle.rules().cloned().collect();
    let p = GroundProgram::prepare(c, domains, &limits).unwrap();
    let p = if admit { p.admit(&limits).unwrap() } else { p };
    let before = format!("{p:?}");
    let mut certified = 0;
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let models = stable_models(&atoms, &inputs, &rules, &world);
        match p
            .certify_observation(world.iter().cloned(), &limits)
            .unwrap()
        {
            CertificationOutcome::Certified(replay) => {
                certified += 1;
                assert_eq!(models.len(), 1);
                assert_eq!(models.first(), Some(&replay.facts));
                assert_eq!(replay.observation.present, world);
                assert_eq!(
                    replay.evidence.keys().cloned().collect::<BTreeSet<_>>(),
                    replay.facts
                );
                for step in &replay.pruning {
                    assert_ne!(step.value, step.premise.polarity == Polarity::Positive);
                    assert!(p.rule(step.rule).unwrap().body.contains(&step.premise));
                    if let CompletedProvider::Component(id) = &step.provider {
                        assert!(replay.providers[id].contains(&step.premise.term.atom));
                    }
                }
                for (fact, step) in &replay.evidence {
                    match &step.evidence {
                        GroundEvidence::Input => assert!(world.contains(fact)),
                        GroundEvidence::Derived { rule, premises } => {
                            assert_eq!(p.original_rule(rule.id), Some(rule));
                            for premise in premises {
                                match premise {
                                    PremiseEvidence::Positive { fact, .. } => {
                                        assert!(replay.evidence[fact].order < step.order)
                                    }
                                    PremiseEvidence::Absent { fact, provider, .. } => {
                                        assert!(!replay.facts.contains(fact));
                                        if let CompletedProvider::Component(id) = provider {
                                            assert!(replay.providers[id].contains(fact));
                                        }
                                    }
                                    PremiseEvidence::Discharged { proof, .. } => {
                                        assert!(p.rewrite_proof(*proof).is_some());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            CertificationOutcome::NotCertified => {}
            CertificationOutcome::Inconclusive(cause) => {
                panic!("tiny oracle fixture exhausted {cause:?}")
            }
        }
        assert_eq!(
            format!("{p:?}"),
            before,
            "specialization mutated the original"
        );
    }
    certified
}
