use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;
pub fn assert_equivalent(corpus: &Corpus, domains: &Domains, sparse: &GroundProgram) {
    let limits = Limits::default();
    let full = GroundProgram::prepare_cartesian(corpus, domains, &limits).unwrap();
    assert_eq!(sparse.is_admitted(), full.is_admitted());
    let inputs: Vec<_> = full.input_atoms().cloned().collect();
    assert!(
        inputs.len() <= 10,
        "exhaustive oracle is for small input spaces"
    );
    for bits in 0..(1usize << inputs.len()) {
        let observation: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, a)| a.clone())
            .collect();
        let actual = sparse.evaluate(observation.clone(), &limits).unwrap();
        let expected = full.evaluate(observation, &limits).unwrap();
        for atom in full.atoms() {
            match (actual.fact(atom).unwrap(), expected.fact(atom).unwrap()) {
                (FactState::Settled(a), FactState::Settled(b)) => {
                    assert_eq!(a, b, "{atom:?}, observation {bits}")
                }
                (FactState::Blocked(a), FactState::Blocked(b)) => {
                    let actual_roots: BTreeSet<_> = a
                        .iter()
                        .map(|id| sparse.component(*id).unwrap().atoms.clone())
                        .collect();
                    let expected_roots: BTreeSet<_> = b
                        .iter()
                        .map(|id| full.component(*id).unwrap().atoms.clone())
                        .collect();
                    assert_eq!(actual_roots, expected_roots, "{atom:?}, observation {bits}");
                }
                states => panic!("{atom:?}, observation {bits}: {states:?}"),
            }
        }
    }
}
