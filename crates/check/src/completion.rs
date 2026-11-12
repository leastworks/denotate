//! A sufficient failure check, never an admission mechanism. Completed equations
//! can have self-supported solutions even when there is no stable model.
use crate::{
    boolean::EquationContext,
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, iff, or};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub enum CompletionOutcome {
    /// All inputs have an equation solution. This does NOT establish meaning.
    NoContradiction,
    NoMeaning(Box<NoMeaning>),
    /// At least one external premise is unresolved. No free guesses were made.
    Deferred {
        blocked_by: BTreeSet<ComponentId>,
    },
    Inconclusive(Inconclusive),
}

#[derive(Debug)]
pub struct CompletionBoundary {
    pub condition: Condition,
    pub value_in_witness: bool,
    pub provider: CompletedProvider,
}

#[derive(Debug)]
pub struct NoMeaning {
    pub component: ComponentId,
    /// Input-only formula. No SCC variables escape the private equation arena.
    pub bad_input: Condition,
    pub observation: Observation,
    /// All retained defining instances, not just the displayed cycle's rules.
    pub rules: Vec<GroundRule>,
    /// Settled external premises, confirmed by concrete upstream replay.
    pub upstream: BTreeMap<GroundAtom, CompletionBoundary>,
    /// References preserve the connection to authored rules after rewriting.
    pub rewrites: Vec<RewriteProofId>,
}

impl SymbolicMeaning<'_> {
    pub(crate) fn complete_component(
        &self,
        component: &Component,
        retained: usize,
        budget: &mut Budget<'_>,
    ) -> Result<CompletionOutcome> {
        budget.tick("completion component")?;
        budget.charge(component.atoms.len(), "completion component")?;
        let internal: BTreeMap<_, _> = component
            .atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a.clone(), i))
            .collect();
        let mut rules = Vec::new();
        let mut upstream = BTreeMap::new();
        let mut blocked_by = BTreeSet::new();
        let mut incomplete = None;
        for index in &self.program.component_rules[component.id.index] {
            let rule = &self.program.rules[*index];
            budget.charge(1 + rule.body.len(), "completion rules")?;
            for literal in &rule.body {
                let atom = &literal.term.atom;
                if internal.contains_key(atom) || upstream.contains_key(atom) {
                    continue;
                }
                match self.fact(atom)? {
                    SymbolicFact::Settled(condition) => {
                        upstream.insert(atom.clone(), condition);
                    }
                    SymbolicFact::Blocked(roots) => blocked_by.extend(roots),
                    SymbolicFact::Inconclusive(cause) => incomplete = Some(cause),
                }
            }
            rules.push(rule.clone());
        }
        if let Some(cause) = incomplete {
            return Ok(CompletionOutcome::Inconclusive(cause));
        }
        if !blocked_by.is_empty() {
            return Ok(CompletionOutcome::Deferred { blocked_by });
        }
        let reserved = self
            .metrics()
            .retained_condition_nodes
            .checked_add(retained)
            .ok_or(CheckError::Internal("completion storage overflow"))?;
        let eq = EquationContext::new(self.context(), internal.len(), reserved, budget)?;
        let formula = equations(&eq, &internal, &rules, &upstream, None, budget)?;
        let answer = eq.eliminate(formula, budget)?;
        let bad = eq.not(&answer, budget)?;
        drop(answer);
        let bad_input = self.context().restrict(&eq.finish(bad, budget)?, budget)?;
        if bad_input.is_false() {
            return Ok(CompletionOutcome::NoContradiction);
        }
        let observation = self
            .context()
            .witness_with_budget(&bad_input, budget)?
            .ok_or(CheckError::Internal("no-meaning condition has no witness"))?;

        // Replay only settled prerequisites. Do not try evaluating the broken
        // component, and do not conjoin unrelated regions' equations.
        let cone = self
            .program
            .dependency_cone_with_budget(upstream.keys().cloned(), budget)?;
        let replay = self.program.evaluate_selected(
            observation.present.iter().cloned(),
            Some(&cone.components),
            budget,
        )?;
        let mut boundary = BTreeMap::new();
        let mut values = BTreeMap::new();
        for (atom, condition) in &upstream {
            budget.tick("completion witness replay")?;
            let FactState::Settled(value) = replay.fact(atom)? else {
                return Err(CheckError::Internal("completion boundary is not settled"));
            };
            if value
                != self.context().evaluate_with_budget(
                    condition,
                    observation.present.iter().cloned(),
                    budget,
                )?
            {
                return Err(CheckError::Internal("completion boundary did not replay"));
            }
            let provider = if !self.program.is_possible(atom)? {
                CompletedProvider::NoPossibleProducer
            } else if self.program.inputs.contains(atom) {
                CompletedProvider::InputSnapshot
            } else {
                CompletedProvider::Component(self.program.component_for(atom)?.id)
            };
            values.insert(atom.clone(), value);
            boundary.insert(
                atom.clone(),
                CompletionBoundary {
                    condition: condition.clone(),
                    value_in_witness: value,
                    provider,
                },
            );
        }
        // Rebuild from concrete boundary values, not by trusting bad_input.
        // There must be no assignment to the component's result variables.
        let replay_reserved = reserved + bad_input.node_count();
        let pinned = EquationContext::new(self.context(), internal.len(), replay_reserved, budget)?;
        let pinned_formula =
            equations(&pinned, &internal, &rules, &upstream, Some(&values), budget)?;
        if !pinned.eliminate(pinned_formula, budget)?.is_false() {
            return Err(CheckError::Internal(
                "no-meaning witness has an equation solution",
            ));
        }
        let mut rewrites = Vec::new();
        for proof in self.program.rewrite_proofs() {
            budget.tick("completion rewrite evidence")?;
            if internal.contains_key(&proof.candidate().head.atom) {
                rewrites.push(proof.id);
            }
        }
        Ok(CompletionOutcome::NoMeaning(Box::new(NoMeaning {
            component: component.id,
            bad_input,
            observation,
            rules,
            upstream: boundary,
            rewrites,
        })))
    }
}

fn equations(
    eq: &EquationContext<'_>,
    internal: &BTreeMap<GroundAtom, usize>,
    rules: &[GroundRule],
    upstream: &BTreeMap<GroundAtom, Condition>,
    pinned: Option<&BTreeMap<GroundAtom, bool>>,
    budget: &mut Budget<'_>,
) -> Result<crate::boolean::Formula> {
    // Index all producers; a fact is equivalent to their disjunction, not just
    // implied by them. Headless atoms have false on the right-hand side.
    let mut producers = BTreeMap::<_, Vec<_>>::new();
    for rule in rules {
        budget.tick("completion equations")?;
        producers.entry(&rule.head.atom).or_default().push(rule);
    }
    let mut result = eq.constant(true, budget)?;
    for (head, index) in internal {
        budget.tick("completion equations")?;
        let mut alternatives = eq.constant(false, budget)?;
        for rule in producers.get(head).into_iter().flatten() {
            let mut body = eq.constant(true, budget)?;
            for literal in &rule.body {
                budget.tick("completion equations")?;
                let atom = &literal.term.atom;
                let mut value = if let Some(index) = internal.get(atom) {
                    eq.variable(*index, budget)?
                } else if let Some(values) = pinned {
                    eq.constant(values[atom], budget)?
                } else {
                    eq.lift(&upstream[atom], budget)?
                };
                if literal.polarity == Polarity::Negative {
                    value = eq.not(&value, budget)?;
                }
                body = eq.apply(&body, &value, and, budget)?;
            }
            alternatives = eq.apply(&alternatives, &body, or, budget)?;
        }
        let variable = eq.variable(*index, budget)?;
        let equality = eq.apply(&variable, &alternatives, iff, budget)?;
        result = eq.apply(&result, &equality, and, budget)?;
    }
    Ok(result)
}
