use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;
pub fn rel(c: &mut Corpus, name: &str, input: bool) -> RelationId {
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
pub fn atom(r: RelationId) -> GroundAtom {
    GroundAtom::new(r, [])
}
pub fn rule(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)]) -> RuleId {
    let head = c.atom(head, []).unwrap();
    let body: Vec<_> = body
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
    c.add_rule(head, body).unwrap()
}

// Independent truth oracle: no BDD, SCC/admission result, sparse grounding or
// production evaluator. Exponential enumeration is deliberately capped.
pub fn subsets(atoms: &[GroundAtom]) -> Vec<BTreeSet<GroundAtom>> {
    assert!(atoms.len() <= 12, "tiny stable-model oracle only");
    (0..1usize << atoms.len())
        .map(|bits| {
            atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| bits & (1 << i) != 0)
                .map(|(_, a)| a.clone())
                .collect()
        })
        .collect()
}
// Enumerate guesses only for atoms not functionally fixed by the input world
// or unused positive output definitions. This eliminates added value-copy leaves
// without using SCCs, admission, BDDs or a production evaluator. Positive cycles
// remain guessed, preserving supported (not necessarily stable) models too.
pub fn candidates(
    derived: &[GroundAtom],
    inputs: &BTreeSet<GroundAtom>,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> Vec<BTreeSet<GroundAtom>> {
    let fixed: BTreeSet<_> = derived
        .iter()
        .filter(|a| {
            let producers: Vec<_> = rules.iter().filter(|r| r.head.atom == **a).collect();
            !producers.is_empty()
                && producers
                    .iter()
                    .all(|r| r.body.iter().all(|l| l.polarity == Polarity::Positive))
                && (producers
                    .iter()
                    .all(|r| r.body.iter().all(|l| inputs.contains(&l.term.atom)))
                    || !rules
                        .iter()
                        .any(|r| r.body.iter().any(|l| l.term.atom == **a)))
        })
        .cloned()
        .collect();
    let guessed: Vec<_> = derived
        .iter()
        .filter(|a| !fixed.contains(*a))
        .cloned()
        .collect();
    subsets(&guessed)
        .into_iter()
        .map(|mut candidate| {
            candidate.extend(world.iter().cloned());
            loop {
                let before = candidate.len();
                for r in rules {
                    if fixed.contains(&r.head.atom)
                        && r.body.iter().all(|l| candidate.contains(&l.term.atom))
                    {
                        candidate.insert(r.head.atom.clone());
                    }
                }
                if before == candidate.len() {
                    break;
                }
            }
            candidate
        })
        .collect()
}

pub fn stable_models(
    atoms: &[GroundAtom],
    inputs: &BTreeSet<GroundAtom>,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> BTreeSet<BTreeSet<GroundAtom>> {
    let derived: Vec<_> = atoms
        .iter()
        // Headless atoms cannot belong to a stable model. This only shrinks
        // exhaustive assignment enumeration; no production pruning is reused.
        .filter(|a| !inputs.contains(*a) && rules.iter().any(|r| r.head.atom == **a))
        .cloned()
        .collect();
    candidates(&derived, inputs, rules, world)
        .into_iter()
        .filter_map(|candidate| {
            // Gelfond-Lifschitz reduct of the AUTHORED ground rules.
            let reduct: Vec<_> = rules
                .iter()
                .filter(|r| {
                    !r.body.iter().any(|l| {
                        l.polarity == Polarity::Negative && candidate.contains(&l.term.atom)
                    })
                })
                .collect();
            let mut least = world.clone();
            loop {
                let before = least.len();
                for r in &reduct {
                    if r.body
                        .iter()
                        .filter(|l| l.polarity == Polarity::Positive)
                        .all(|l| least.contains(&l.term.atom))
                    {
                        least.insert(r.head.atom.clone());
                    }
                }
                if before == least.len() {
                    break;
                }
            }
            (least == candidate).then_some(candidate)
        })
        .collect()
}

pub fn supported_models(
    p: &GroundProgram,
    rules: &[GroundRule],
    world: &BTreeSet<GroundAtom>,
) -> BTreeSet<BTreeSet<GroundAtom>> {
    let derived: Vec<_> = p
        .atoms()
        .filter(|a| !p.inputs.contains(*a))
        .cloned()
        .collect();
    candidates(&derived, &p.inputs, rules, world)
        .into_iter()
        .filter_map(|candidate| {
            derived
                .iter()
                .all(|a| {
                    candidate.contains(a)
                        == rules.iter().any(|r| {
                            r.head.atom == *a
                                && r.body.iter().all(|l| {
                                    candidate.contains(&l.term.atom)
                                        == (l.polarity == Polarity::Positive)
                                })
                        })
                })
                .then_some(candidate)
        })
        .collect()
}

pub fn compare(c: &Corpus, domains: &Domains, rewritten: &GroundProgram) -> usize {
    compare_permitted(c, domains, rewritten, |_| true)
}

/// The caller independently defines permitted input worlds (not through the
/// checker's BDD W), so contextual rewrites are compared only where they apply.
pub fn compare_permitted(
    c: &Corpus,
    domains: &Domains,
    rewritten: &GroundProgram,
    permitted: impl Fn(&BTreeSet<GroundAtom>) -> bool,
) -> usize {
    let oracle = GroundProgram::prepare_cartesian(c, domains, &Limits::default()).unwrap();
    let atoms: Vec<_> = oracle.atoms().cloned().collect();
    let inputs: BTreeSet<_> = oracle.input_atoms().cloned().collect();
    let originals: Vec<_> = oracle.rules().cloned().collect();
    let active: Vec<_> = rewritten.rules().cloned().collect();
    let mut nonempty = 0;
    let meaning = rewritten.symbolic(&Limits::default()).unwrap();
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        if !permitted(&world) {
            continue;
        }
        let before = stable_models(&atoms, &inputs, &originals, &world);
        assert_eq!(before, stable_models(&atoms, &inputs, &active, &world));
        nonempty += usize::from(!before.is_empty());
        let replay = rewritten
            .evaluate(world.iter().cloned(), &Limits::default())
            .unwrap();
        if rewritten.is_admitted() {
            assert_eq!(
                before.len(),
                1,
                "admission requires a unique original stable model"
            );
            assert_eq!(
                *before.first().unwrap(),
                replay.established_facts().cloned().collect()
            );
        }
        for a in &atoms {
            if let SymbolicFact::Settled(condition) = meaning.fact(a).unwrap() {
                let truth = meaning
                    .context()
                    .evaluate(&condition, world.iter().cloned(), &Limits::default())
                    .unwrap();
                assert_eq!(replay.fact(a).unwrap(), FactState::Settled(truth));
                for model in &before {
                    assert_eq!(model.contains(a), truth);
                }
            }
        }
    }
    nonempty
}
