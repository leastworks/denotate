use super::*;
impl GroundProgram {
    pub(crate) fn prepare_completion_enumerated(
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
}
