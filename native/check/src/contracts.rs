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

struct ConeIndex<'p> {
    program: &'p GroundProgram,
    producers: BTreeMap<&'p GroundAtom, Vec<&'p GroundRule>>,
}
impl<'p> ConeIndex<'p> {
    fn new(program: &'p GroundProgram, budget: &mut Budget<'_>) -> Result<Self> {
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        for rule in &program.rules {
            budget.tick("dependency cones")?;
            producers.entry(&rule.head.atom).or_default().push(rule);
        }
        Ok(Self { program, producers })
    }
    fn build(
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
        let mut budget = Budget::new(limits);
        ConeIndex::new(self, &mut budget)?.build(roots, &mut budget)
    }
}

#[derive(Debug, Clone)]
pub enum GroupOutcome {
    /// Proved only for this dependency-closed group, over every input observation.
    Proved,
    /// Nonempty violation condition. Not yet a replayed counterexample (3d).
    Overlap(Condition),
    Unsupported,
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
    /// An error yields no partial successful report.
    pub fn check_at_most_one(&self, limits: &Limits) -> Result<PropertyReport> {
        let start = Instant::now();
        let mut budget = Budget::new(limits);
        let index = ConeIndex::new(self.program, &mut budget)?;
        let mut groups = Vec::new();
        let mut retained = 0;
        for group in self.program.at_most_one_groups() {
            budget.tick("property checks")?;
            let cone = index.build(group.tuples.iter().cloned(), &mut budget)?;
            let outcome = if !cone.blocked_by.is_empty() {
                GroupOutcome::Unsupported
            } else {
                let mut violation = self.context.false_condition();
                for (i, left) in group.tuples.iter().enumerate() {
                    for right in &group.tuples[i + 1..] {
                        budget.tick("property checks")?;
                        let pair = self.context.apply(
                            &self.known(left),
                            &self.known(right),
                            op_function::and,
                            &mut budget,
                        )?;
                        violation =
                            self.context
                                .apply(&violation, &pair, op_function::or, &mut budget)?;
                    }
                }
                if violation.is_false() {
                    GroupOutcome::Proved
                } else {
                    retained = retain(retained, 0, violation.node_count(), limits)?;
                    GroupOutcome::Overlap(violation)
                }
            };
            groups.push(GroupCheck {
                group: group.clone(),
                cone,
                outcome,
            });
        }
        let mut unresolved_components = BTreeSet::new();
        for component in self.program.components() {
            budget.tick("property checks")?;
            if component.cycle.is_some() {
                unresolved_components.insert(component.id);
            }
        }
        budget.charge(0, "property checks")?;
        Ok(PropertyReport {
            whole_program_admitted: self.is_complete(),
            unresolved_components,
            groups,
            metrics: SymbolicMetrics {
                elapsed: start.elapsed(),
                work: budget.used(),
                retained_condition_nodes: retained,
            },
        })
    }
}
