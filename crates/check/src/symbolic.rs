mod retention;
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
    fn masked<const W: bool>(
        self,
        meaning: &SymbolicMeaning<'_, W>,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        Ok(match self {
            Self::Known(c) => {
                Self::Known(meaning.context.apply(mask, &c, op_function::and, budget)?)
            }
            unknown => unknown,
        })
    }

    fn is_true<const W: bool>(
        &self,
        meaning: &SymbolicMeaning<'_, W>,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        match self {
            Self::Known(c) => meaning.condition_is_true(c, mask, budget),
            Self::Unknown(_) => Ok(false),
        }
    }
    fn is_false(&self) -> bool {
        matches!(self, Self::Known(c) if c.is_false())
    }
    fn not<const W: bool>(
        self,
        meaning: &SymbolicMeaning<'_, W>,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        Ok(match self {
            Self::Known(c) => Self::Known(meaning.context.apply(
                mask,
                &c,
                op_function::and_not,
                budget,
            )?),
            unknown => unknown,
        })
    }
    fn combine<const W: bool>(
        self,
        other: Self,
        all: bool,
        meaning: &SymbolicMeaning<'_, W>,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        // A false conjunct or true alternative decides the expression even if
        // another premise is unknown. Otherwise conservatively propagate unknown.
        if (all && (self.is_false() || other.is_false()))
            || (!all
                && (self.is_true(meaning, mask, budget)?
                    || other.is_true(meaning, mask, budget)?))
        {
            return Ok(Self::Known(if all {
                meaning.context.false_condition()
            } else {
                mask.clone()
            }));
        }
        // Masked truth is the current mask, not raw true. Avoid conjoining it
        // again with operands that already imply it. Unknowns remain unknown.
        if all {
            if self.is_true(meaning, mask, budget)? {
                return Ok(other);
            }
            if other.is_true(meaning, mask, budget)? {
                return Ok(self);
            }
        }
        Ok(match (self, other) {
            (Self::Known(a), Self::Known(b)) => Self::Known(meaning.context.apply(
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

/// Settled fact conditions for admitted components, exact on the declared input universe U.
/// A blocked component is not a restriction on the input universe.
/// Per-component masks contain U; values outside U are not a semantic contract.
/// Internal verification uses `SymbolicMeaning<true>`, exact only within W;
/// admission/proof APIs accept the U-exact default type only.
#[derive(Debug)]
pub struct SymbolicMeaning<'p, const WITHIN_W: bool = false> {
    pub(crate) program: &'p GroundProgram,
    pub(crate) context: ConditionContext,
    pub(crate) conditions: BTreeMap<GroundAtom, Condition>,
    pub(crate) released: BTreeSet<GroundAtom>,
    pub(crate) universe_masks: Vec<Condition>,
    pub(crate) inconclusive: BTreeMap<ComponentId, Inconclusive>,
    pub(crate) unknown: BTreeMap<GroundAtom, EvaluationUnknown<GroundAtom>>,
    pub(crate) metrics: SymbolicMetrics,
}
impl<const WITHIN_W: bool> SymbolicMeaning<'_, WITHIN_W> {
    pub(crate) fn stored_conditions(&self) -> impl Iterator<Item = &Condition> {
        self.conditions
            .values()
            .chain(self.universe_masks.iter())
            .chain(self.context.stored_conditions())
    }

    fn component_mask(&self, index: usize) -> Condition {
        self.universe_masks
            .get(index)
            .cloned()
            .unwrap_or_else(|| self.truth())
    }
    fn truth(&self) -> Condition {
        if WITHIN_W {
            self.context.permitted_worlds()
        } else {
            self.context.true_condition()
        }
    }
    fn condition_is_true(
        &self,
        condition: &Condition,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        let truth = mask;
        if truth.is_true() {
            return Ok(condition.is_true());
        }
        if condition.node_count() != truth.node_count() {
            return Ok(false);
        }
        budget.charge(condition.node_count(), "symbolic truth within W")?;
        Ok(condition.same_representation(truth))
    }
    fn partial_condition(&self, atom: &GroundAtom) -> Result<PartialCondition> {
        self.unknown.get(atom).cloned().map_or_else(
            || self.known(atom).map(PartialCondition::Known),
            |u| Ok(PartialCondition::Unknown(u)),
        )
    }
    pub(crate) fn partial_expression(
        &self,
        expression: &SettledExpression<GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<PartialCondition> {
        // Proof consumers read under the full context. Per-component masks are
        // used only by the evaluation loop, whose support is structurally closed.
        let mask = if self.universe_masks.is_empty() {
            self.truth()
        } else {
            self.context.permitted_worlds()
        };
        self.partial_expression_masked(expression, &mask, budget)
    }
    fn partial_expression_masked(
        &self,
        expression: &SettledExpression<GroundAtom>,
        mask: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<PartialCondition> {
        budget.tick("settled expression")?;
        Ok(match expression {
            SettledExpression::Constant(v) => PartialCondition::Known(if *v {
                mask.clone()
            } else {
                self.context.false_condition()
            }),
            SettledExpression::Atom(a) => match self.fact(a)? {
                SymbolicFact::Settled(c) => PartialCondition::Known(self.context.apply(
                    mask,
                    &c,
                    op_function::and,
                    budget,
                )?),
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
                .partial_expression_masked(c, mask, budget)?
                .not(self, mask, budget)?,
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                let all = matches!(expression, SettledExpression::All(_));
                let mut result = PartialCondition::Known(if all {
                    mask.clone()
                } else {
                    self.context.false_condition()
                });
                for c in cs {
                    let next = self.partial_expression_masked(c, mask, budget)?;
                    result = result.combine(next, all, self, mask, budget)?;
                    if (all && result.is_false()) || (!all && result.is_true(self, mask, budget)?) {
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
            return Ok(SymbolicFact::Settled(self.known(atom)?));
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
        Ok(SymbolicFact::Settled(self.known(atom)?))
    }
    pub(crate) fn known(&self, atom: &GroundAtom) -> Result<Condition> {
        if self.released.contains(atom) {
            return Err(CheckError::Internal("read of released symbolic condition"));
        }
        if let Some(value) = self.program.fixed_value(atom) {
            return Ok(if value {
                self.truth()
            } else {
                self.context.false_condition()
            });
        }
        Ok(self
            .conditions
            .get(atom)
            .cloned()
            .unwrap_or_else(|| self.context.false_condition()))
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
        keep: &BTreeSet<GroundAtom>,
        reserved: usize,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(
            budget,
            false,
            Some(cone),
            None,
            Some((keep, reserved)),
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

    /// Verification-only meaning. The type prevents use by raw admission/proof APIs.
    pub(crate) fn symbolic_for_checking<const WITHIN_W: bool>(
        &self,
        budget: &mut Budget<'_>,
    ) -> Result<SymbolicMeaning<'_, WITHIN_W>> {
        self.symbolic_selected_impl(
            budget,
            true,
            None,
            None,
            None,
            None,
            #[cfg(any(test, feature = "test-support"))]
            None,
        )
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
            cone.map(|c| &c.facts),
            None,
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
        self.symbolic_selected_impl(
            budget,
            partial,
            cone,
            cone.map(|c| &c.facts),
            None,
            None,
            Some(measured),
        )
    }
    /// Evaluate selected dependencies without projecting the variable universe.
    /// Assumption conditions must combine with W in the whole program's order.
    pub(crate) fn symbolic_for_assumptions(
        &self,
        budget: &mut Budget<'_>,
        cone: &DependencyCone,
    ) -> Result<SymbolicMeaning<'_>> {
        self.symbolic_selected_impl(
            budget,
            false,
            Some(cone),
            None,
            None,
            None,
            #[cfg(any(test, feature = "test-support"))]
            None,
        )
    }
    fn symbolic_selected_impl<const WITHIN_W: bool>(
        &self,
        budget: &mut Budget<'_>,
        partial: bool,
        cone: Option<&DependencyCone>,
        input_facts: Option<&BTreeSet<GroundAtom>>,
        keep: Option<(&BTreeSet<GroundAtom>, usize)>,
        observe: Option<&dyn Fn(ComponentId, Option<&EvaluationUnknown<GroundAtom>>)>,
        #[cfg(any(test, feature = "test-support"))] mut measured: Option<
            &mut dyn FnMut(ComponentId, Duration),
        >,
    ) -> Result<SymbolicMeaning<'_, WITHIN_W>> {
        let reserved = keep.map_or(0, |(_, reserved)| reserved);
        let mut retention = keep
            .map(|(keep, _)| {
                retention::Retention::build(self, cone.expect("admission cone"), keep, budget)
            })
            .transpose()?;
        let _stage = budget.limits.progress.nested("symbolic-evaluation");
        let start = Instant::now();
        let context = ConditionContext::build_selected(self, input_facts, budget)?;
        let mut mask_nodes = 0;
        let universe_masks = if !WITHIN_W && !self.input_cardinalities.is_empty() {
            let supports = self.universe_supports(cone, budget)?;
            let support_storage =
                supports.len() + supports.iter().map(BTreeSet::len).sum::<usize>();
            let context_storage = context.permitted_worlds().node_count()
                + context
                    .universe_factors
                    .iter()
                    .map(Condition::node_count)
                    .sum::<usize>();
            let mut shared = BTreeMap::<BTreeSet<usize>, Condition>::new();
            let mut masks = Vec::with_capacity(supports.len());
            for support in supports {
                budget.tick("input universe masks")?;
                let mask = if let Some(mask) = shared.get(&support) {
                    mask.clone()
                } else {
                    let mut mask = context.true_condition();
                    for index in &support {
                        mask = context.apply(
                            &mask,
                            &context.universe_factors[*index],
                            op_function::and,
                            budget,
                        )?;
                    }
                    mask_nodes = retain(mask_nodes, 0, mask.node_count(), budget)?;
                    retain(
                        reserved + support_storage + context_storage,
                        0,
                        mask_nodes,
                        budget,
                    )?;
                    shared.insert(support, mask.clone());
                    mask
                };
                masks.push(mask);
            }
            masks
        } else {
            Vec::new()
        };
        let mut meaning: SymbolicMeaning<'_, WITHIN_W> = SymbolicMeaning {
            program: self,
            context,
            conditions: BTreeMap::new(),
            released: BTreeSet::new(),
            universe_masks,
            inconclusive: BTreeMap::new(),
            unknown: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: 0,
                retained_condition_nodes: 0,
            },
        };
        let mut retained = retain(
            reserved
                + mask_nodes
                + meaning.context.permitted_worlds().node_count()
                + meaning
                    .context
                    .universe_factors
                    .iter()
                    .map(Condition::node_count)
                    .sum::<usize>(),
            0,
            retention.as_ref().map_or(0, |r| r.nodes),
            budget,
        )?;
        for input in meaning.context.inputs().cloned().collect::<Vec<_>>() {
            if input_facts.is_none() && cone.is_some_and(|c| !c.facts.contains(&input)) {
                continue;
            }
            let input = &input;
            let condition = meaning.context.input_with_budget(input, budget)?;
            let mask = meaning.component_mask(self.component_for(input)?.id.index);
            let condition = meaning
                .context
                .apply(&condition, &mask, op_function::and, budget)?;
            retained = retain(retained, 0, condition.node_count(), budget)?;
            meaning.conditions.insert(input.clone(), condition);
        }
        for (index, component) in self.components.iter().enumerate() {
            if let Some(retention) = &mut retention {
                retention.before(index, &mut meaning, &mut retained, budget)?;
            }
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
                            let old = meaning.partial_condition(head)?;
                            if old.is_true(&meaning, &meaning.component_mask(index), budget)? {
                                continue;
                            }
                            let _profile_target = budget.limits.profile.target(head);
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
            if budget.limits.profile.conditions_enabled() {
                for atom in &component.atoms {
                    if let Some(c) = meaning.conditions.get(atom) {
                        if c.node_count() >= 64 {
                            budget.limits.profile.condition(|| {
                                crate::ConditionObservation::Retained {
                                    atom: atom.clone(),
                                    nodes: c.node_count(),
                                }
                            });
                        }
                    }
                }
            }
        }
        if let Some(retention) = &mut retention {
            retention.before(usize::MAX, &mut meaning, &mut retained, budget)?;
        }
        if !partial {
            budget.charge(0, "symbolic evaluation")?;
        }
        meaning.metrics = SymbolicMetrics {
            elapsed: start.elapsed(),
            work: budget.used(),
            retained_condition_nodes: retained - reserved,
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

impl<const WITHIN_W: bool> SymbolicMeaning<'_, WITHIN_W> {
    fn evaluate_producer(
        &self,
        rule: &GroundRule,
        index: usize,
        old: PartialCondition,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<Option<PartialCondition>> {
        let head = &rule.head.atom;
        let mask = self.component_mask(index);
        let mut body = PartialCondition::Known(mask.clone());
        for literal in &rule.body {
            budget.tick("symbolic evaluation")?;
            let mut premise = self
                .partial_condition(&literal.term.atom)?
                .masked(self, &mask, budget)?;
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
                premise = premise.not(self, &mask, budget)?;
            }
            body = body.combine(premise, true, self, &mask, budget)?;
            if body.is_false() {
                break;
            }
        }
        if !body.is_false() {
            for replacement in &rule.replacements {
                let value =
                    self.partial_expression_masked(&replacement.expression, &mask, budget)?;
                body = body.combine(value, true, self, &mask, budget)?;
                if body.is_false() {
                    break;
                }
            }
        }
        // Both operands use the same fixed component mask (or opt-in full W),
        // so their raw difference tests exact convergence within that mask.
        if let (PartialCondition::Known(a), PartialCondition::Known(b)) = (&old, &body) {
            if self
                .context
                .apply(b, a, op_function::and_not, budget)?
                .is_false()
            {
                return Ok(None);
            }
        }
        let next = old.combine(body, false, self, &mask, budget)?;
        let old_size = self.conditions.get(head).map_or(0, Condition::node_count);
        match &next {
            PartialCondition::Known(c) => {
                *retained = retain(*retained, old_size, c.node_count(), budget)?;
            }
            PartialCondition::Unknown(_) => *retained -= old_size,
        }
        Ok(Some(next))
    }
}

impl SymbolicMeaning<'_> {
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
