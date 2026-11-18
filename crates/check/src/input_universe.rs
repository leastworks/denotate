//! Input declarations define U before selected assumptions and admission.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{Cardinality, Corpus};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub(crate) struct UniverseGroup {
    pub relation: denotate_ir::RelationId,
    pub kind: Cardinality,
    pub atoms: Vec<GroundAtom>,
}
impl GroundProgram {
    pub(crate) fn build_input_universe(
        &mut self,
        corpus: &Corpus,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        self.universe_groups.clear();
        self.input_constraints_inconsistent = false;
        self.input_cardinalities = corpus
            .relations()
            .filter_map(|r| r.input_cardinality.clone().map(|c| (r.id, c)))
            .collect();
        let mut result = Vec::new();
        for (relation, declaration) in &self.input_cardinalities {
            let mut groups = BTreeMap::new();
            if declaration.kind == Cardinality::ExactlyOne {
                let domains = declaration
                    .group_by
                    .iter()
                    .map(|i| &self.domains[&self.signatures[relation][*i]])
                    .collect::<Vec<_>>();
                if !domains.iter().any(|d| d.is_empty()) {
                    let mut positions = vec![0; domains.len()];
                    loop {
                        budget.tick("input universe groups")?;
                        budget.room(
                            result.len() + groups.len(),
                            budget.limits.max_atoms,
                            "input universe groups",
                            "groups",
                        )?;
                        let key: Vec<_> = positions
                            .iter()
                            .enumerate()
                            .map(|(i, p)| domains[i][*p])
                            .collect();
                        groups.insert(key, Vec::new());
                        let mut i = positions.len();
                        while i > 0 {
                            i -= 1;
                            positions[i] += 1;
                            if positions[i] < domains[i].len() {
                                break;
                            }
                            positions[i] = 0;
                        }
                        if positions.iter().all(|p| *p == 0) {
                            break;
                        }
                    }
                }
            }
            for atom in &self.inputs {
                budget.tick("input universe groups")?;
                if atom.relation == *relation {
                    let key = declaration
                        .group_by
                        .iter()
                        .map(|i| atom.arguments[*i])
                        .collect::<Vec<_>>();
                    groups.entry(key).or_default().push(atom.clone());
                }
            }
            result.extend(
                groups
                    .into_values()
                    .filter(|g| declaration.kind == Cardinality::ExactlyOne || g.len() > 1)
                    .map(|atoms| UniverseGroup {
                        relation: *relation,
                        kind: declaration.kind,
                        atoms,
                    }),
            );
        }
        self.universe_groups = result;
        Ok(())
    }
    /// Input-only selected AMO groups can conflict with declared exactly-one
    /// groups. Compute this after choosing the input order; retain only the truth
    /// of consistency, so a later fresh variable map cannot misbind a condition.
    pub(crate) fn check_input_consistency(&mut self, budget: &mut Budget<'_>) -> Result<()> {
        self.input_constraints_inconsistent = false;
        if !self.input_groups.is_empty()
            && self
                .universe_groups
                .iter()
                .any(|g| g.kind == Cardinality::ExactlyOne)
        {
            self.input_constraints_inconsistent = ConditionContext::build(self, budget)?
                .permitted_worlds()
                .is_false();
        }
        Ok(())
    }
    /// Exactly-one groups enumerate resolved grouping domains, including empty candidate sets.
    pub fn input_universe_is_empty(&self) -> bool {
        self.universe_groups
            .iter()
            .any(|g| g.kind == Cardinality::ExactlyOne && g.atoms.is_empty())
    }
    /// Closed structural support, represented by the declared group indices it touches.
    /// Includes blocked components; selected assumptions never prune these dependencies.
    pub(crate) fn universe_supports(
        &self,
        cone: Option<&DependencyCone>,
        budget: &mut Budget<'_>,
    ) -> Result<Vec<BTreeSet<usize>>> {
        let mut retained = crate::symbolic::retain(0, 0, self.components.len(), budget)?;
        let mut input_groups = BTreeMap::new();
        for (index, group) in self.universe_groups.iter().enumerate() {
            for atom in &group.atoms {
                budget.tick("input universe support")?;
                input_groups.insert(atom, index);
                retained = crate::symbolic::retain(retained, 0, 1, budget)?;
            }
        }
        let mut supports: Vec<BTreeSet<usize>> = Vec::with_capacity(self.components.len());
        for component in &self.components {
            if cone.is_some_and(|c| !c.components.contains(&component.id)) {
                supports.push(BTreeSet::new());
                continue;
            }
            let mut support = BTreeSet::new();
            for atom in &component.atoms {
                budget.tick("input universe support")?;
                if let Some(group) = input_groups.get(atom) {
                    if support.insert(*group) {
                        retained = crate::symbolic::retain(retained, 0, 1, budget)?;
                    }
                }
            }
            for dependency in &component.dependencies {
                for group in &supports[dependency.index] {
                    budget.tick("input universe support")?;
                    if support.insert(*group) {
                        retained = crate::symbolic::retain(retained, 0, 1, budget)?;
                    }
                }
            }
            supports.push(support);
        }
        Ok(supports)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule};
    use std::sync::Arc;

    #[test]
    fn declared_truth_keeps_logical_short_circuits_with_an_exhausted_operand() {
        let mut c = Corpus::new();
        let input = rel(&mut c, "input", true);
        let unknown = rel(&mut c, "unknown", false);
        let consumer = rel(&mut c, "consumer", false);
        rule(&mut c, consumer, &[(input, false)]);
        c.constrain_input(input, Cardinality::ExactlyOne, [])
            .unwrap();
        let limits = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let mut m = p.symbolic(&limits).unwrap();
        m.unknown.insert(
            atom(unknown),
            EvaluationUnknown {
                atom: atom(unknown),
                reason: Inconclusive {
                    phase: "test",
                    resource: "work",
                    details: Default::default(),
                },
            },
        );
        let yes = Arc::new(SettledExpression::Atom(atom(input)));
        let unknown = Arc::new(SettledExpression::Atom(atom(unknown)));
        for (expression, expected) in [
            (
                SettledExpression::Any(vec![unknown.clone(), yes.clone()]),
                true,
            ),
            (
                SettledExpression::All(vec![unknown, Arc::new(SettledExpression::Not(yes))]),
                false,
            ),
        ] {
            let crate::symbolic::PartialCondition::Known(value) = m
                .partial_expression(&expression, &mut Budget::new(&limits))
                .unwrap()
            else {
                panic!("logical shortcut became inconclusive")
            };
            assert_eq!(
                m.context()
                    .evaluate(&value, [atom(input)], &limits)
                    .unwrap(),
                expected
            );
        }
    }
}
