// Test-only snapshot of the original Cartesian grounder.
use super::*;

impl GroundProgram {
    pub fn prepare_cartesian(corpus: &Corpus, domains: &Domains, limits: &Limits) -> Result<Self> {
        let mut budget = Budget::new(limits);
        let domains = validate_domains(corpus, domains, &mut budget)?;
        let restricted = input_domains::evaluate(corpus, &domains, &mut budget)?;
        let mut p = Self::empty(corpus, domains);
        p.input_domains = restricted;
        let domains = &p.domains;
        let preparation = p.preparation;
        for relation in corpus.relations() {
            budget.tick("grounding")?;
            let columns: Vec<_> = relation
                .parameters
                .iter()
                .map(|p| domains[&p.sort].as_slice())
                .collect();
            each_tuple(&columns, &mut budget, |args, budget| {
                budget.room(p.atoms.len(), limits.max_atoms, "grounding", "atoms")?;
                let atom = GroundAtom::new(relation.id, args.iter().copied());
                if relation.role == RelationRole::Input {
                    if p.input_domains
                        .get(&relation.id)
                        .is_some_and(|allowed| !allowed.contains(&atom))
                    {
                        return Ok(());
                    }
                    p.inputs.insert(atom.clone());
                }
                p.atom_index.insert(atom.clone(), p.atoms.len());
                p.atoms.push(atom);
                Ok(())
            })?;
        }
        let mut dependencies = 0usize;
        for rule in corpus.rules() {
            let mut variables = BTreeMap::new();
            for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
                for term in atom.arguments() {
                    budget.tick("grounding")?;
                    if let Term::Variable { name, sort } = term.value() {
                        variables.insert(name.as_str(), *sort);
                    }
                }
            }
            let columns: Vec<_> = variables
                .values()
                .map(|sort| domains[sort].as_slice())
                .collect();
            each_tuple(&columns, &mut budget, |args, budget| {
                budget.room(p.rules.len(), limits.max_rules, "grounding", "rules")?;
                let binding: BTreeMap<_, _> = variables
                    .keys()
                    .copied()
                    .zip(args.iter().copied())
                    .collect();
                let head = ground_atom(&rule.head, &binding, budget)?;
                let mut body = Vec::new();
                for literal in &rule.body {
                    budget.room(
                        dependencies,
                        limits.max_dependencies,
                        "grounding",
                        "dependencies",
                    )?;
                    dependencies += 1;
                    body.push(GroundLiteral {
                        polarity: match literal {
                            Literal::Positive(_) => Polarity::Positive,
                            Literal::Negative(_) => Polarity::Negative,
                        },
                        term: ground_atom(literal.atom(), &binding, budget)?,
                    });
                }
                p.rules.push(GroundRule {
                    id: GroundRuleId {
                        preparation,
                        index: p.rules.len(),
                    },
                    source: rule.id,
                    head,
                    body,
                });
                Ok(())
            })?;
        }
        graph::analyze(&mut p, &mut budget)?;
        Ok(p)
    }
}
