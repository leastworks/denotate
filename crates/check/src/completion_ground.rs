//! Completion cannot use the least-model possible-tuple closure. Enumerate finite
//! substitutions, retaining every defining instance, including unseeded recursion.
//! Only input tuples and atoms occurring in instances need storage: every other
//! legal derived tuple has an empty definition and is false.
use super::*;

impl GroundProgram {
    pub(crate) fn prepare_completion(
        corpus: &Corpus,
        domains: &Domains,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let domains = validate_domains(corpus, domains, budget)?;
        let mut p = Self::empty(corpus, domains.clone());
        p.obligations.clear();
        let mut dependencies = 0;
        for rule in corpus.rules() {
            budget.tick("completion grounding")?;
            let mut variables = BTreeMap::new();
            for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
                for term in atom.arguments() {
                    budget.tick("completion grounding")?;
                    if let Term::Variable { name, sort } = term.value() {
                        variables.insert(name.as_str(), *sort);
                    }
                }
            }
            let columns: Vec<_> = variables.values().map(|s| domains[s].as_slice()).collect();
            each_tuple(&columns, budget, |values, b| {
                b.room(
                    p.rules.len(),
                    b.limits.max_rules,
                    "completion grounding",
                    "rules",
                )?;
                let binding = variables
                    .keys()
                    .copied()
                    .zip(values.iter().copied())
                    .collect();
                let head = ground_atom(&rule.head, &binding, b)?;
                p.completion_atom(head.atom.clone(), b)?;
                let mut body = Vec::new();
                for literal in &rule.body {
                    b.room(
                        dependencies,
                        b.limits.max_dependencies,
                        "completion grounding",
                        "dependencies",
                    )?;
                    dependencies += 1;
                    let term = ground_atom(literal.atom(), &binding, b)?;
                    p.completion_atom(term.atom.clone(), b)?;
                    body.push(GroundLiteral {
                        polarity: if matches!(literal, Literal::Positive(_)) {
                            Polarity::Positive
                        } else {
                            Polarity::Negative
                        },
                        term,
                    });
                }
                let id = GroundRuleId {
                    preparation: p.preparation,
                    index: p.rules.len(),
                };
                p.rules.push(GroundRule {
                    id,
                    source: rule.id,
                    head,
                    body,
                    replacements: vec![],
                });
                Ok(())
            })?;
        }
        // Eligibility is deliberately not evaluated yet. First inspect provider
        // cones in this unpruned instance graph for completion compatibility.
        graph::analyze(&mut p, budget)?;
        Ok(p)
    }

    pub(crate) fn completion_inputs(
        &mut self,
        corpus: &Corpus,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        self.input_domains = input_domains::evaluate(corpus, &self.domains, budget)?;
        let domains = self.domains.clone();
        for r in corpus.relations().filter(|r| r.role == RelationRole::Input) {
            if let Some(allowed) = self.input_domains.get(&r.id).cloned() {
                for a in allowed {
                    self.completion_atom(a.clone(), budget)?;
                    self.inputs.insert(a);
                }
            } else {
                let columns: Vec<_> = r
                    .parameters
                    .iter()
                    .map(|p| domains[&p.sort].as_slice())
                    .collect();
                each_tuple(&columns, budget, |values, b| {
                    let a = GroundAtom::new(r.id, values.iter().copied());
                    self.completion_atom(a.clone(), b)?;
                    self.inputs.insert(a);
                    Ok(())
                })?;
            }
        }
        // Ineligible input atoms occurring in rules remain in the inventory, but
        // are not free inputs: their empty definition makes them false.
        self.build_input_groups(corpus, &[], budget)?;
        graph::analyze(self, budget)
    }

    fn completion_atom(&mut self, atom: GroundAtom, b: &mut Budget<'_>) -> Result<()> {
        b.charge(atom.arguments.len() + 1, "completion grounding")?;
        if !self.atom_index.contains_key(&atom) {
            b.room(
                self.atoms.len(),
                b.limits.max_atoms,
                "completion grounding",
                "atoms",
            )?;
            let i = self.atoms.len();
            self.atom_index.insert(atom.clone(), i);
            self.atoms.push(atom);
        }
        Ok(())
    }
}
