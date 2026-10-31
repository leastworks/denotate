//! Build W before admission, using independent stratified meaning.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function;
use denotate_ir::{Cardinality, ConstantId, Restriction};
use std::collections::{BTreeMap, BTreeSet};

impl GroundProgram {
    pub fn assumptions_consistent(&self) -> bool {
        self.assumption_condition
            .as_ref()
            .is_none_or(|w| !w.is_false())
    }
    pub(crate) fn install_assumptions(
        &mut self,
        restrictions: &[Restriction],
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let result = (|| {
            // No rewrites and no selected restrictions may establish a constraint's
            // own meaning. Unrelated negative cycles may remain blocked.
            let mut raw = self.clone();
            raw.input_groups.clear();
            raw.assumption_condition = None;
            let meaning = raw.symbolic_with_budget(budget)?;
            let ctx = meaning.context();
            let mut permitted = ConditionContext::build(self, budget)?.permitted_worlds();
            for r in restrictions {
                budget.tick("assumptions")?;
                let relation = r.relation();
                let signature = self
                    .signatures
                    .get(&relation)
                    .ok_or(CheckError::InvalidRequest("unknown assumption relation"))?;
                let columns = r.group_by();
                let mut unique = BTreeSet::new();
                for c in columns {
                    budget.tick("assumptions")?;
                    if *c >= signature.len() || !unique.insert(*c) {
                        return Err(CheckError::InvalidRequest("invalid assumption grouping"));
                    }
                }
                let mut groups = BTreeMap::<Vec<ConstantId>, Vec<&GroundAtom>>::new();
                if r.kind().has_coverage() {
                    let domains = columns
                        .iter()
                        .map(|c| &self.domains[&signature[*c]])
                        .collect::<Vec<_>>();
                    if !domains.iter().any(|d| d.is_empty()) {
                        let mut positions = vec![0; domains.len()];
                        loop {
                            budget.tick("assumption groups")?;
                            budget.room(
                                groups.len(),
                                budget.limits.max_atoms,
                                "assumption groups",
                                "groups",
                            )?;
                            let key = positions
                                .iter()
                                .enumerate()
                                .map(|(i, p)| domains[i][*p])
                                .collect();
                            groups.insert(key, vec![]);
                            let mut i = positions.len();
                            loop {
                                if i == 0 {
                                    break;
                                }
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
                for atom in &self.atoms {
                    budget.tick("assumptions")?;
                    if atom.relation != relation {
                        continue;
                    }
                    let key = columns.iter().map(|i| atom.arguments[*i]).collect();
                    groups.entry(key).or_default().push(atom);
                }
                for atoms in groups.values() {
                    let mut seen = ctx.false_condition();
                    for atom in atoms {
                        budget.tick("assumptions")?;
                        let value = match meaning.fact(atom)? {
                            SymbolicFact::Settled(c) => c,
                            SymbolicFact::Inconclusive(c) => {
                                return Err(CheckError::LimitExceeded {
                                    phase: c.phase,
                                    resource: c.resource,
                                });
                            }
                            SymbolicFact::Blocked(_) => {
                                return Err(CheckError::InvalidRequest(
                                    "assumption cone is not independently stratified",
                                ));
                            }
                        };
                        if r.kind() == Cardinality::Empty {
                            permitted =
                                ctx.apply(&permitted, &value, op_function::and_not, budget)?;
                        } else {
                            if r.kind().has_uniqueness() {
                                let conflict =
                                    ctx.apply(&seen, &value, op_function::and, budget)?;
                                permitted =
                                    ctx.apply(&permitted, &conflict, op_function::and_not, budget)?;
                            }
                            seen = ctx.apply(&seen, &value, op_function::or, budget)?;
                        }
                        crate::symbolic::retain(
                            meaning.metrics().retained_condition_nodes,
                            0,
                            permitted.node_count() + seen.node_count(),
                            budget,
                        )?;
                    }
                    if r.kind().has_coverage() {
                        permitted = ctx.apply(&permitted, &seen, op_function::and, budget)?;
                    }
                }
            }
            // Even false is retained: it is an inconsistent context, not a proof.
            self.assumption_condition = Some(permitted);
            Ok(())
        })();
        result.map_err(|e| match e {
            CheckError::LimitExceeded { resource, .. } => CheckError::LimitExceeded {
                phase: "assumptions",
                resource,
            },
            CheckError::Deadline { .. } => CheckError::Deadline {
                phase: "assumptions",
            },
            e => e,
        })
    }
}
