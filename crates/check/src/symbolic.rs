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

/// An exact symbolic condition could not be evaluated. `atom` is the original
/// exhausted head, not a downstream reader. Reused values carry semantic keys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvaluationUnknown<A> {
    pub atom: A,
    pub reason: Inconclusive,
}

pub(crate) fn local_exhaustion(error: &CheckError) -> bool {
    crate::guarded_settlement::cases::recoverable(error)
}

pub(crate) enum PartialCondition {
    Known(Condition),
    Unknown(EvaluationUnknown<GroundAtom>),
}
impl PartialCondition {
    fn is_true(&self) -> bool {
        matches!(self, Self::Known(c) if c.is_true())
    }
    fn is_false(&self) -> bool {
        matches!(self, Self::Known(c) if c.is_false())
    }
    fn not(self, ctx: &ConditionContext, budget: &mut Budget<'_>) -> Result<Self> {
        Ok(match self {
            Self::Known(c) => Self::Known(ctx.complement(&c, budget)?),
            unknown => unknown,
        })
    }
    fn combine(
        self,
        other: Self,
        all: bool,
        ctx: &ConditionContext,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        // A false conjunct or true alternative decides the expression even if
        // another premise is unknown. Otherwise conservatively propagate unknown.
        if (all && (self.is_false() || other.is_false()))
            || (!all && (self.is_true() || other.is_true()))
        {
            return Ok(Self::Known(if all {
                ctx.false_condition()
            } else {
                ctx.true_condition()
            }));
        }
        Ok(match (self, other) {
            (Self::Known(a), Self::Known(b)) => Self::Known(ctx.apply(
                &a,
                &b,
                if all {
                    op_function::and
                } else {
                    op_function::or
                },
                budget,
            )?),
            (Self::Unknown(u), _) | (_, Self::Unknown(u)) => Self::Unknown(u),
        })
    }
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
    pub(crate) unknown: BTreeMap<GroundAtom, EvaluationUnknown<GroundAtom>>,
    pub(crate) metrics: SymbolicMetrics,
}
impl SymbolicMeaning<'_> {
    fn partial_condition(&self, atom: &GroundAtom) -> PartialCondition {
        self.unknown.get(atom).cloned().map_or_else(
            || PartialCondition::Known(self.known(atom)),
            PartialCondition::Unknown,
        )
    }
    pub(crate) fn partial_expression(
        &self,
        expression: &SettledExpression<GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<PartialCondition> {
        budget.tick("settled expression")?;
        Ok(match expression {
            SettledExpression::Constant(v) => PartialCondition::Known(if *v {
                self.context.true_condition()
            } else {
                self.context.false_condition()
            }),
            SettledExpression::Atom(a) => match self.fact(a)? {
                SymbolicFact::Settled(c) => PartialCondition::Known(c),
                SymbolicFact::Inconclusive(reason) => PartialCondition::Unknown(
                    self.unknown.get(a).cloned().unwrap_or(EvaluationUnknown {
                        atom: a.clone(),
                        reason,
                    }),
                ),
                SymbolicFact::Blocked(_) => {
                    return Err(CheckError::Internal("replacement reads unresolved atom"));
                }
            },
            SettledExpression::Not(c) => self
                .partial_expression(c, budget)?
                .not(&self.context, budget)?,
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                let all = matches!(expression, SettledExpression::All(_));
                let mut result = PartialCondition::Known(if all {
                    self.context.true_condition()
                } else {
                    self.context.false_condition()
                });
                for c in cs {
                    let next = self.partial_expression(c, budget)?;
                    result = result.combine(next, all, &self.context, budget)?;
                    if (all && result.is_false()) || (!all && result.is_true()) {
                        break;
                    }
                }
                result
            }
        })
    }
    pub fn program(&self) -> &GroundProgram {
        self.program
    }
    pub fn context(&self) -> &ConditionContext {
        &self.context
    }
    pub fn is_complete(&self) -> bool {
        self.program.is_admitted() && self.inconclusive.is_empty() && self.unknown.is_empty()
    }
    pub fn metrics(&self) -> &SymbolicMetrics {
        &self.metrics
    }
    pub fn unknown_atoms(&self) -> &BTreeMap<GroundAtom, EvaluationUnknown<GroundAtom>> {
        &self.unknown
    }
    pub fn fact(&self, atom: &GroundAtom) -> Result<SymbolicFact> {
        if self.program.fixed_value(atom).is_some() {
            return Ok(SymbolicFact::Settled(self.known(atom)));
        }
        if let Some(unknown) = self.unknown.get(atom) {
            return Ok(SymbolicFact::Inconclusive(unknown.reason));
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
        observe: Option<&dyn Fn(ComponentId, Option<&EvaluationUnknown<GroundAtom>>)>,
        cone: &DependencyCone,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(
            budget,
            false,
            Some(cone),
            true,
            observe,
            #[cfg(any(test, feature = "test-support"))]
            None,
        )
    }

    /// Atom-local BDD/storage exhaustion preserves independent exact conditions.
    /// Other logical exhaustion retains only previously completed components.
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
            false,
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
        self.symbolic_selected_impl(budget, partial, cone, false, None, Some(measured))
    }
    fn symbolic_selected_impl(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
        cone: Option<&DependencyCone>,
        admission: bool,
        observe: Option<&dyn Fn(ComponentId, Option<&EvaluationUnknown<GroundAtom>>)>,
        #[cfg(any(test, feature = "test-support"))] mut measured: Option<
            &mut dyn FnMut(ComponentId, Duration),
        >,
    ) -> Result<SymbolicMeaning<'_>> {
        let _stage = budget.limits.progress.nested("symbolic-evaluation");
        let start = Instant::now();
        let context = ConditionContext::build_selected(
            self,
            if admission {
                None
            } else {
                cone.map(|c| &c.facts)
            },
            budget,
        )?;
        let mut meaning = SymbolicMeaning {
            program: self,
            context,
            conditions: BTreeMap::new(),
            inconclusive: BTreeMap::new(),
            unknown: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: 0,
                retained_condition_nodes: 0,
            },
        };
        let mut retained = meaning.context.permitted_worlds().node_count();
        for input in meaning.context.inputs().cloned().collect::<Vec<_>>() {
            if admission && cone.is_some_and(|c| !c.facts.contains(&input)) {
                continue;
            }
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
                    for literal in self.rules[*rule].dependency_literals() {
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
                observe(component.id, None);
            }
            #[cfg(any(test, feature = "test-support"))]
            let component_start = measured.as_ref().map(|_| Instant::now());
            // A failed head is opaque for this snapshot. Restart the positive
            // component from bottom: earlier approximations may have read that
            // head before its condition grew beyond the allowance.
            let mut failed = BTreeMap::new();
            let result = 'restart: loop {
                let failures_before = failed.len();
                let pass = (|| -> Result<()> {
                    budget.tick("symbolic evaluation")?;
                    loop {
                        let mut changed = false;
                        for rule_index in &self.component_rules[index] {
                            budget.tick("symbolic evaluation")?;
                            let rule = &self.rules[*rule_index];
                            let head = &rule.head.atom;
                            if failed.contains_key(head) {
                                continue;
                            }
                            let old = meaning.partial_condition(head);
                            if old.is_true() {
                                continue;
                            }
                            let next =
                                meaning.evaluate_producer(rule, index, old, &mut retained, budget);
                            match next {
                                Ok(Some(PartialCondition::Known(c))) => {
                                    meaning.unknown.remove(head);
                                    meaning.conditions.insert(head.clone(), c);
                                    changed = true;
                                }
                                Ok(Some(PartialCondition::Unknown(u))) => {
                                    meaning.conditions.remove(head);
                                    changed |= !meaning.unknown.contains_key(head);
                                    meaning.unknown.insert(head.clone(), u);
                                }
                                Ok(None) => {}
                                Err(error) if local_exhaustion(&error) => {
                                    // No partial condition or producer contribution
                                    // escapes this restart. Consumed work stays charged.
                                    let _atom = budget.limits.progress.sampled(
                                        "symbolic-evaluation",
                                        true,
                                        || CheckingTarget::Atom(head.clone()),
                                    );
                                    budget.failure(&error);
                                    let unknown = EvaluationUnknown {
                                        atom: head.clone(),
                                        reason: Inconclusive::from_error(error)?,
                                    };
                                    if let Some(observe) = observe {
                                        observe(component.id, Some(&unknown));
                                    }
                                    failed.insert(head.clone(), unknown);
                                    return Ok(());
                                }
                                Err(error) => return Err(error),
                            }
                        }
                        if !component.recursive || !changed {
                            break;
                        }
                    }
                    Ok(())
                })();
                if pass.is_err() {
                    break pass;
                }
                // Install each new failure only after discarding the whole
                // component's intermediate approximations.
                if failed.len() != failures_before {
                    if let Err(error) = budget.charge(component.atoms.len(), "symbolic restart") {
                        break Err(error);
                    }
                    for atom in &component.atoms {
                        if !self.inputs.contains(atom) {
                            meaning.conditions.remove(atom);
                        }
                        meaning.unknown.remove(atom);
                    }
                    retained = previous_retained;
                    meaning.unknown.extend(failed.clone());
                    continue 'restart;
                }
                break Ok(());
            };
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
                    meaning.unknown.remove(atom);
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
    budget.limits.profile.retained_conditions(next);
    Ok(next)
}

impl SymbolicMeaning<'_> {
    fn evaluate_producer(
        &self,
        rule: &GroundRule,
        index: usize,
        old: PartialCondition,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<Option<PartialCondition>> {
        let head = &rule.head.atom;
        let mut body = PartialCondition::Known(self.context.true_condition());
        for literal in &rule.body {
            budget.tick("symbolic evaluation")?;
            let mut premise = self.partial_condition(&literal.term.atom);
            if literal.polarity == Polarity::Negative {
                if let Some(atom_index) = self.program.atom_index.get(&literal.term.atom) {
                    let provider = self.program.atom_components[*atom_index];
                    if provider.index >= index
                        || !self.program.components[provider.index]
                            .blocked_by
                            .is_empty()
                    {
                        return Err(CheckError::Internal(
                            "symbolic negated premise is not settled",
                        ));
                    }
                }
                premise = premise.not(&self.context, budget)?;
            }
            body = body.combine(premise, true, &self.context, budget)?;
            if body.is_false() {
                break;
            }
        }
        if !body.is_false() {
            for replacement in &rule.replacements {
                let value = self.partial_expression(&replacement.expression, budget)?;
                body = body.combine(value, true, &self.context, budget)?;
                if body.is_false() {
                    break;
                }
            }
        }
        // Preserve the unrestricted convergence check on
        // exact conditions; equality under W is insufficient.
        if let (PartialCondition::Known(a), PartialCondition::Known(b)) = (&old, &body) {
            if self
                .context
                .apply(b, a, op_function::and_not, budget)?
                .is_false()
            {
                return Ok(None);
            }
        }
        let next = old.combine(body, false, &self.context, budget)?;
        let old_size = self.conditions.get(head).map_or(0, Condition::node_count);
        match &next {
            PartialCondition::Known(c) => {
                *retained = retain(*retained, old_size, c.node_count(), budget)?;
            }
            PartialCondition::Unknown(_) => *retained -= old_size,
        }
        Ok(Some(next))
    }

    pub(crate) fn settled_expression(
        &self,
        expression: &SettledExpression<GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        expression.symbolic(
            &self.context,
            &mut |atom| match self.fact(atom)? {
                SymbolicFact::Settled(value) => Ok(value),
                SymbolicFact::Inconclusive(cause) => Err(cause.into()),
                SymbolicFact::Blocked(_) => {
                    Err(CheckError::Internal("replacement reads unresolved atom"))
                }
            },
            budget,
        )
    }
}
