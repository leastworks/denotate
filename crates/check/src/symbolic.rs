use crate::{
    boolean::limit,
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone)]
pub enum SymbolicFact {
    Settled(Condition),
    Blocked(BTreeSet<ComponentId>),
    Inconclusive(Inconclusive),
}

#[derive(Debug, Clone)]
pub struct SymbolicMetrics {
    pub elapsed: Duration,
    pub work: usize,
    pub retained_condition_nodes: usize,
}

/// Settled fact conditions for admitted components over ALL input observations.
/// A blocked component is not a restriction on the input universe.
#[derive(Debug)]
pub struct SymbolicMeaning<'p> {
    pub(crate) program: &'p GroundProgram,
    pub(crate) context: ConditionContext,
    pub(crate) conditions: BTreeMap<GroundAtom, Condition>,
    pub(crate) inconclusive: BTreeMap<ComponentId, Inconclusive>,
    pub(crate) metrics: SymbolicMetrics,
}
impl SymbolicMeaning<'_> {
    pub fn program(&self) -> &GroundProgram {
        self.program
    }
    pub fn context(&self) -> &ConditionContext {
        &self.context
    }
    pub fn is_complete(&self) -> bool {
        self.program.is_admitted() && self.inconclusive.is_empty()
    }
    pub fn metrics(&self) -> &SymbolicMetrics {
        &self.metrics
    }
    pub fn fact(&self, atom: &GroundAtom) -> Result<SymbolicFact> {
        if self.program.fixed_value(atom).is_some() {
            return Ok(SymbolicFact::Settled(self.known(atom)));
        }
        if self.program.is_possible(atom)? {
            let component = self.program.component_for(atom)?;
            if let Some(cause) = self.inconclusive.get(&component.id) {
                return Ok(SymbolicFact::Inconclusive(*cause));
            }
            if !component.blocked_by.is_empty() {
                if let Some(cause) = self.program.admission_limit() {
                    return Ok(SymbolicFact::Inconclusive(cause));
                }
                return Ok(SymbolicFact::Blocked(component.blocked_by.clone()));
            }
        }
        Ok(SymbolicFact::Settled(self.known(atom)))
    }
    pub(crate) fn known(&self, atom: &GroundAtom) -> Condition {
        if let Some(value) = self.program.fixed_value(atom) {
            return if value {
                self.context.true_condition()
            } else {
                self.context.false_condition()
            };
        }
        self.conditions
            .get(atom)
            .cloned()
            .unwrap_or_else(|| self.context.false_condition())
    }
}

impl GroundProgram {
    pub fn symbolic(&self, limits: &Limits) -> Result<SymbolicMeaning<'_>> {
        let mut budget = Budget::new(limits);
        self.symbolic_with_budget(&mut budget)
    }

    pub(crate) fn symbolic_with_budget(
        &self,
        budget: &mut Budget<'_>,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_impl(budget, false)
    }

    pub(crate) fn symbolic_for_admission(
        &self,
        budget: &mut Budget<'_>,
        observe: Option<&dyn Fn(ComponentId)>,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(
            budget,
            false,
            None,
            observe,
            #[cfg(any(test, feature = "test-support"))]
            None,
        )
    }

    /// Reporting evaluation retains only completed components after exhaustion.
    /// No intermediate recursive approximation becomes a settled fact.
    pub fn symbolic_checked(
        &self,
        limits: &Limits,
    ) -> Result<AnalysisOutcome<SymbolicMeaning<'_>>> {
        AnalysisOutcome::from_result(self.symbolic_impl(&mut Budget::new(limits), true))
    }

    pub(crate) fn symbolic_impl(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected(budget, partial, None)
    }
    pub(crate) fn symbolic_selected(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
        cone: Option<&DependencyCone>,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(
            budget,
            partial,
            cone,
            None,
            #[cfg(any(test, feature = "test-support"))]
            None,
        )
    }
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn symbolic_selected_measured(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
        cone: Option<&DependencyCone>,
        measured: &mut dyn FnMut(ComponentId, Duration),
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(budget, partial, cone, None, Some(measured))
    }
    fn symbolic_selected_impl(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
        cone: Option<&DependencyCone>,
        observe: Option<&dyn Fn(ComponentId)>,
        #[cfg(any(test, feature = "test-support"))] mut measured: Option<
            &mut dyn FnMut(ComponentId, Duration),
        >,
    ) -> Result<SymbolicMeaning<'_>> {
        let _stage = budget.limits.progress.nested("symbolic-evaluation");
        let start = Instant::now();
        let context = ConditionContext::build_selected(self, cone.map(|c| &c.facts), budget)?;
        let mut meaning = SymbolicMeaning {
            program: self,
            context,
            conditions: BTreeMap::new(),
            inconclusive: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: 0,
                retained_condition_nodes: 0,
            },
        };
        let mut retained = meaning.context.permitted_worlds().node_count();
        for input in meaning.context.inputs().cloned().collect::<Vec<_>>() {
            let input = &input;
            let condition = meaning.context.input_with_budget(input, budget)?;
            retained = retain(retained, 0, condition.node_count(), budget)?;
            meaning.conditions.insert(input.clone(), condition);
        }
        for (index, component) in self.components.iter().enumerate() {
            if cone.is_some_and(|c| !c.components.contains(&component.id)) {
                continue;
            }
            // Validate before short-circuiting or skipping blocked components:
            // completion also reads their premises through `fact`/`known`.
            // Missing conditions may mean false only inside the selected cone.
            if let Some(cone) = cone {
                for rule in &self.component_rules[index] {
                    for literal in &self.rules[*rule].body {
                        if !cone.facts.contains(&literal.term.atom) {
                            return Err(CheckError::Internal(
                                "local premise outside dependency cone",
                            ));
                        }
                    }
                }
            }
            if !component.blocked_by.is_empty() {
                continue;
            }
            if let Some(cause) = component
                .dependencies
                .iter()
                .find_map(|id| meaning.inconclusive.get(id))
                .copied()
            {
                meaning.inconclusive.insert(component.id, cause);
                continue;
            }
            let _component_stage =
                budget
                    .limits
                    .progress
                    .sampled("symbolic-evaluation", partial, || {
                        CheckingTarget::Component(
                            self.progress_component(component.id)
                                .expect("current component"),
                        )
                    });
            let previous_retained = retained;
            if let Some(observe) = observe {
                observe(component.id);
            }
            #[cfg(any(test, feature = "test-support"))]
            let component_start = measured.as_ref().map(|_| Instant::now());
            let result = (|| -> Result<()> {
                budget.tick("symbolic evaluation")?;
                loop {
                    let mut changed = false;
                    for rule in &self.component_rules[index] {
                        budget.tick("symbolic evaluation")?;
                        let rule = &self.rules[*rule];
                        let old = meaning.known(&rule.head.atom);
                        if old.is_true() {
                            continue;
                        }
                        let mut body = meaning.context.true_condition();
                        for literal in &rule.body {
                            budget.tick("symbolic evaluation")?;
                            let mut premise = meaning.known(&literal.term.atom);
                            if literal.polarity == Polarity::Negative {
                                if let Some(atom_index) = self.atom_index.get(&literal.term.atom) {
                                    let provider = self.atom_components[*atom_index];
                                    if provider.index >= index
                                        || !self.components[provider.index].blocked_by.is_empty()
                                    {
                                        return Err(CheckError::Internal(
                                            "symbolic negated premise is not settled",
                                        ));
                                    }
                                }
                                premise = meaning.context.complement(&premise, budget)?;
                            }
                            body =
                                meaning
                                    .context
                                    .apply(&body, &premise, op_function::and, budget)?;
                            if body.is_false() {
                                break;
                            }
                        }
                        // Only extend the head if this body adds input worlds.
                        // Node-vector equality is not Boolean equivalence.
                        let delta =
                            meaning
                                .context
                                .apply(&body, &old, op_function::and_not, budget)?;
                        if delta.is_false() {
                            continue;
                        }
                        let next = meaning
                            .context
                            .apply(&old, &body, op_function::or, budget)?;
                        let old_size = meaning
                            .conditions
                            .get(&rule.head.atom)
                            .map_or(0, Condition::node_count);
                        retained = retain(retained, old_size, next.node_count(), budget)?;
                        meaning.conditions.insert(rule.head.atom.clone(), next);
                        changed = true;
                    }
                    if !component.recursive || !changed {
                        break;
                    }
                }
                Ok(())
            })();
            #[cfg(any(test, feature = "test-support"))]
            if let (Some(measured), Some(start)) = (&mut measured, component_start) {
                measured(component.id, start.elapsed());
            }
            if let Err(error) = result {
                if !partial {
                    return Err(error);
                }
                budget.failure(&error);
                let cause = Inconclusive::from_error(error)?;
                for atom in &component.atoms {
                    if !self.inputs.contains(atom) {
                        meaning.conditions.remove(atom);
                    }
                }
                retained = previous_retained;
                meaning.inconclusive.insert(component.id, cause);
            }
        }
        if !partial {
            budget.charge(0, "symbolic evaluation")?;
        }
        meaning.metrics = SymbolicMetrics {
            elapsed: start.elapsed(),
            work: budget.used(),
            retained_condition_nodes: retained,
        };
        Ok(meaning)
    }
}

pub(crate) fn retain(
    total: usize,
    old: usize,
    new: usize,
    budget: &mut Budget<'_>,
) -> Result<usize> {
    let next = total
        .checked_sub(old)
        .and_then(|n| n.checked_add(new))
        .ok_or_else(|| {
            limit(
                "symbolic storage",
                "condition nodes",
                budget.limits.max_condition_nodes,
                None,
            )
        })?;
    budget.observe("symbolic storage", "condition nodes", next);
    if next > budget.limits.max_condition_nodes {
        budget.failure(&limit(
            "symbolic storage",
            "condition nodes",
            budget.limits.max_condition_nodes,
            Some(next),
        ));
        return Err(limit(
            "symbolic storage",
            "condition nodes",
            budget.limits.max_condition_nodes,
            Some(next),
        ));
    }
    Ok(next)
}
