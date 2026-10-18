use crate::{
    limits::{Budget, Result},
    symbolic::retain,
    *,
};
use biodivine_lib_bdd::op_function;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};

/// Dependency-closed ground scope, not just a Boolean function's input support.
/// Includes every possible defining instance and structural-absence premise.
#[derive(Debug, Clone)]
pub struct DependencyCone {
    pub roots: BTreeSet<GroundAtom>,
    pub facts: BTreeSet<GroundAtom>,
    pub rules: BTreeSet<GroundRuleId>,
    pub components: BTreeSet<ComponentId>,
    pub blocked_by: BTreeSet<ComponentId>,
}

pub(crate) struct ConeIndex<'p> {
    program: &'p GroundProgram,
    producers: BTreeMap<&'p GroundAtom, Vec<&'p GroundRule>>,
}
impl<'p> ConeIndex<'p> {
    pub(crate) fn new(program: &'p GroundProgram, budget: &mut Budget<'_>) -> Result<Self> {
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        for rule in program.rules() {
            budget.tick("dependency cones")?;
            producers.entry(&rule.head.atom).or_default().push(rule);
        }
        Ok(Self { program, producers })
    }
    pub(crate) fn build(
        &self,
        roots: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<DependencyCone> {
        let mut cone = DependencyCone {
            roots: BTreeSet::new(),
            facts: BTreeSet::new(),
            rules: BTreeSet::new(),
            components: BTreeSet::new(),
            blocked_by: BTreeSet::new(),
        };
        for root in roots {
            budget.tick("dependency cones")?;
            self.program.validate_atom(&root)?;
            cone.roots.insert(root);
        }
        let mut pending: Vec<_> = cone.roots.iter().cloned().collect();
        while let Some(fact) = pending.pop() {
            budget.tick("dependency cones")?;
            if !cone.facts.insert(fact.clone()) {
                continue;
            }
            if let Some(index) = self.program.atom_index.get(&fact) {
                let id = self.program.atom_components[*index];
                cone.components.insert(id);
                for root in &self.program.components[id.index].blocked_by {
                    budget.tick("dependency cones")?;
                    cone.blocked_by.insert(*root);
                }
            }
            if let Some(rules) = self.producers.get(&fact) {
                for rule in rules {
                    budget.tick("dependency cones")?;
                    cone.rules.insert(rule.id);
                    for literal in &rule.body {
                        budget.tick("dependency cones")?;
                        pending.push(literal.term.atom.clone());
                    }
                }
            }
        }
        Ok(cone)
    }
}
impl GroundProgram {
    pub fn dependency_cone(
        &self,
        roots: impl IntoIterator<Item = GroundAtom>,
        limits: &Limits,
    ) -> Result<DependencyCone> {
        limits.cancellation.check()?;
        let mut budget = Budget::new(limits);
        self.dependency_cone_with_budget(roots, &mut budget)
    }
    pub(crate) fn dependency_cone_with_budget(
        &self,
        roots: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<DependencyCone> {
        ConeIndex::new(self, budget)?.build(roots, budget)
    }
}

#[derive(Debug, Clone)]
pub enum GroupOutcome {
    /// Proved only for this dependency-closed group, over every input observation.
    Proved,
    /// Raw nonempty violation condition; use verify_at_most_one for a replayed finding.
    Overlap(Condition),
    Unsupported,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Clone)]
pub struct GroupCheck {
    pub group: AtMostOneGroup,
    pub cone: DependencyCone,
    pub outcome: GroupOutcome,
}
#[derive(Debug)]
pub struct PropertyReport {
    /// Independent of group outcomes; never implies obligations passed.
    pub whole_program_admitted: bool,
    pub unresolved_components: BTreeSet<ComponentId>,
    /// Nontrivial groups only; zero/one possible tuple needs no Boolean query.
    pub groups: Vec<GroupCheck>,
    pub metrics: SymbolicMetrics,
}

impl SymbolicMeaning<'_> {
    /// Check all represented at_most_one obligations over every input assignment.
    /// Assumptions are not supported yet; rules never restrict the input worlds.
    /// Budget exhaustion is explicit per group once indexing succeeds. Earlier
    /// completed groups are retained; internal failures still return an error.
    pub fn check_at_most_one(&self, limits: &Limits) -> Result<PropertyReport> {
        self.check_queries(limits, None)
    }
    pub(crate) fn check_queries(
        &self,
        limits: &Limits,
        mut queries: Option<&mut QueryRun<'_>>,
    ) -> Result<PropertyReport> {
        limits.cancellation.check()?;
        let start = Instant::now();
        let mut budget = if queries.is_some() {
            Budget::tracked(limits)
        } else {
            Budget::new(limits)
        };
        let index = ConeIndex::new(self.program, &mut budget);
        if let Err(error) = &index {
            budget.failure(error);
        }
        if let Some(q) = queries.as_mut() {
            // Operational errors cannot commit a receipt.
            if let Err(error) = &index {
                Inconclusive::from_error(error.clone())?;
            }
            let dependency = if q.receipts.get(&QueryKey::Admission).is_some() {
                QueryKey::Admission
            } else {
                QueryKey::Preparation
            };
            budget.record(q.receipts, QueryKey::ConeIndex, [dependency])?;
        }
        let index = index?;
        let mut work = budget.used();
        let mut groups = Vec::new();
        let mut retained = 0;
        let mut retained_nodes = 0;
        let mut ordered: Vec<_> = self.program.at_most_one_groups().collect();
        if let Some(q) = queries.as_ref() {
            let keyed = ordered
                .into_iter()
                .map(|g| Ok((q.group(g)?, g)))
                .collect::<Result<BTreeMap<_, _>>>()?;
            ordered = keyed.into_values().collect();
        }
        #[cfg(any(test, feature = "test-support"))]
        if queries.is_some() {
            crate::accounting::test_schedule(&mut ordered);
        }
        for group in ordered {
            let mut tuples: Vec<_> = group.tuples.iter().collect();
            if let Some(q) = queries.as_ref() {
                let keyed = tuples
                    .into_iter()
                    .map(|a| Ok((AtomKey::from_atom(q.keys, a).map_err(CheckError::Keys)?, a)))
                    .collect::<Result<BTreeMap<_, _>>>()?;
                tuples = keyed.into_values().collect();
            }
            if queries.is_some() {
                budget = Budget::tracked(limits);
                retained = 0;
            }
            let mut cone = DependencyCone {
                roots: group.tuples.iter().cloned().collect(),
                facts: BTreeSet::new(),
                rules: BTreeSet::new(),
                components: BTreeSet::new(),
                blocked_by: BTreeSet::new(),
            };
            let result = (|| -> Result<GroupOutcome> {
                budget.tick("property checks")?;
                cone = index.build(group.tuples.iter().cloned(), &mut budget)?;
                let outcome = if let Some(cause) = cone
                    .components
                    .iter()
                    .find_map(|id| self.inconclusive.get(id))
                {
                    GroupOutcome::Inconclusive(*cause)
                } else if !cone.blocked_by.is_empty() {
                    self.program
                        .admission_limit()
                        .map_or(GroupOutcome::Unsupported, GroupOutcome::Inconclusive)
                } else {
                    let mut violation = self.context.false_condition();
                    for (i, left) in tuples.iter().enumerate() {
                        for right in &tuples[i + 1..] {
                            budget.tick("property checks")?;
                            let pair = self.context.apply(
                                &self.known(left),
                                &self.known(right),
                                op_function::and,
                                &mut budget,
                            )?;
                            violation = self.context.apply(
                                &violation,
                                &pair,
                                op_function::or,
                                &mut budget,
                            )?;
                        }
                    }
                    let violation = self.context.restrict(&violation, &mut budget)?;
                    if violation.is_false() {
                        GroupOutcome::Proved
                    } else {
                        retained = retain(retained, 0, violation.node_count(), &mut budget)?;
                        GroupOutcome::Overlap(violation)
                    }
                };
                Ok(outcome)
            })();
            let outcome = match result {
                Ok(value) => value,
                Err(error) => {
                    budget.failure(&error);
                    GroupOutcome::Inconclusive(Inconclusive::from_error(error)?)
                }
            };
            if let Some(q) = queries.as_mut() {
                work += budget.used();
                retained_nodes += retained;
                budget.record(
                    q.receipts,
                    QueryKey::Property(q.group(group)?),
                    [QueryKey::Symbolic, QueryKey::ConeIndex],
                )?;
            }
            groups.push(GroupCheck {
                group: group.clone(),
                cone,
                outcome,
            });
        }
        let mut unresolved_components = BTreeSet::new();
        for component in self.program.components() {
            if component.cycle.is_some() {
                unresolved_components.insert(component.id);
            }
        }
        Ok(PropertyReport {
            whole_program_admitted: self.is_complete(),
            unresolved_components,
            groups,
            metrics: SymbolicMetrics {
                elapsed: start.elapsed(),
                work: if queries.is_some() {
                    work
                } else {
                    budget.used()
                },
                retained_condition_nodes: if queries.is_some() {
                    retained_nodes
                } else {
                    retained
                },
            },
        })
    }
}
