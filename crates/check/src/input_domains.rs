//! Evaluate a complete static eligibility cone before seeding any input atoms.
use super::*;

pub(super) fn evaluate(
    corpus: &Corpus,
    domains: &Domains,
    budget: &mut Budget<'_>,
) -> Result<BTreeMap<RelationId, BTreeSet<GroundAtom>>> {
    if !corpus.relations().any(|r| r.input_domain.is_some()) {
        return Ok(BTreeMap::new());
    }
    let mut stage = "provider discovery";
    let result = (|| {
        let cone = corpus.input_domain_cone_with(|| budget.tick("input domains"))?;
        let mut program = GroundProgram::empty(corpus, domains.clone());
        stage = "provider grounding";
        sparse::populate_domain_cone(corpus, &mut program, budget, &cone)?;
        stage = "provider dependency analysis";
        graph::analyze(&mut program, budget)?;
        stage = "provider evaluation";
        let replay = program.evaluate_selected([], None, budget)?;
        if !replay.is_complete() {
            return Err(CheckError::Internal(
                "validated input domain did not settle",
            ));
        }
        stage = "eligible input enumeration";
        let mut out = BTreeMap::new();
        let mut input_atoms = 0;
        for relation in corpus.relations() {
            budget.tick("input domains")?;
            let Some(provider) = relation.input_domain else {
                continue;
            };
            let mut tuples = BTreeSet::new();
            for atom in &program.atoms {
                budget.tick("input domains")?;
                if atom.relation == provider && replay.fact(atom)? == FactState::Settled(true) {
                    budget.charge(atom.arguments.len() + 1, "input domains")?;
                    budget.room(
                        input_atoms,
                        budget.limits.max_atoms,
                        "input domains",
                        "atoms",
                    )?;
                    input_atoms += 1;
                    tuples.insert(GroundAtom::new(relation.id, atom.arguments.clone()));
                }
            }
            out.insert(relation.id, tuples);
        }
        Ok(out)
    })();
    result.map_err(|e| e.in_phase("input domains", Some(stage)))
}
