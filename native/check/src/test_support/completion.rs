use super::rewrites::{stable_models, subsets, supported_models};
use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;
pub fn oracle(c: &Corpus, domains: &Domains, p: &GroundProgram) {
    let limits = Limits::default();
    let raw = GroundProgram::prepare_cartesian(c, domains, &limits).unwrap();
    let m = p.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    assert_eq!(report.unresolved.len(), 1);
    let outcome = &report.unresolved[0].completion;
    let atoms: Vec<_> = raw.atoms().cloned().collect();
    let inputs: BTreeSet<_> = raw.input_atoms().cloned().collect();
    let rules: Vec<_> = raw.rules().cloned().collect();
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let solutions = supported_models(&raw, &rules, &world);
        let bad = match outcome {
            CompletionOutcome::NoMeaning(f) => m
                .context()
                .evaluate(&f.bad_input, world.iter().cloned(), &limits)
                .unwrap(),
            CompletionOutcome::NoContradiction => false,
            other => panic!("unexpected completion result: {other:?}"),
        };
        assert_eq!(bad, solutions.is_empty());
        if bad {
            assert!(stable_models(&atoms, &inputs, &rules, &world).is_empty());
        }
    }
    if let CompletionOutcome::NoMeaning(f) = outcome {
        assert!(stable_models(&atoms, &inputs, &rules, &f.observation.present).is_empty());
    }
}
