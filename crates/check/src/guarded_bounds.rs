//! Candidate-relaxed dependency cones and bounds whose domain is explicitly G & W.
//! These certificates are deliberately not ComponentUpperBounds: no removal or
//! discharge query can accidentally consume them as an unrestricted bound.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::and;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Debug, Clone)]
pub struct GuardedCone {
    pub component: ComponentId,
    pub snapshot: u64,
    pub domain: Condition,
    pub relaxed_rule: Option<GroundRuleId>,
    pub atoms: Vec<GroundAtom>,
    /// Includes dead producers as evidence. Their masked condition is false;
    /// their premises do not extend the cone.
    pub producers: Vec<ProducerSummary>,
}
impl GuardedCone {
    pub(crate) fn nodes(&self) -> usize {
        // Charge cache/key metadata too, conservatively as condition-node slots.
        self.domain.node_count()
            + self.atoms.len()
            + self.producers.len()
            + 1
            + self
                .producers
                .iter()
                .map(ProducerSummary::nodes)
                .sum::<usize>()
    }
    pub(crate) fn same_computation(&self, other: &Self, budget: &mut Budget<'_>) -> Result<bool> {
        budget.charge(
            self.atoms.len() + self.producers.len() + self.domain.node_count(),
            "guarded cache lookup",
        )?;
        Ok(self.snapshot == other.snapshot
            && self.component == other.component
            && self.relaxed_rule == other.relaxed_rule
            && self.atoms == other.atoms
            && self.domain.same_representation(&other.domain)
            && self
                .producers
                .iter()
                .map(|p| p.rule.id)
                .eq(other.producers.iter().map(|p| p.rule.id)))
    }
}

#[derive(Debug, Clone)]
pub struct GuardedBounds {
    pub cone: Arc<GuardedCone>,
    pub conditions: BTreeMap<GroundAtom, Condition>,
    pub guarantees: BTreeMap<GroundAtom, Condition>,
}
impl GuardedBounds {
    pub(crate) fn nodes(&self) -> usize {
        self.cone.nodes()
            + self
                .conditions
                .values()
                .chain(self.guarantees.values())
                .map(Condition::node_count)
                .sum::<usize>()
    }
}

pub(crate) fn prepare(
    program: &GroundProgram,
    component: &Component,
    candidate: &ProducerSummary,
    root: &GroundAtom,
    summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<Arc<GuardedCone>> {
    let domain = ctx.restrict(&candidate.condition, budget)?;
    *retained = crate::symbolic::retain(*retained, 0, domain.node_count() + 1, budget)?;
    let mut pending = BTreeSet::from([root.clone()]);
    let mut atoms = BTreeSet::new();
    let mut selected = BTreeMap::new();
    while let Some(atom) = pending.pop_first() {
        budget.tick("guarded cone atom")?;
        if !atoms.insert(atom.clone()) {
            continue;
        }
        *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
        for id in producers.get(&atom).into_iter().flatten() {
            let summary = &summaries[id];
            budget.charge(
                1 + summary.rule.body.len() + summary.settled.len(),
                "guarded cone producer",
            )?;
            let condition = ctx.apply(&domain, &summary.condition, and, budget)?;
            // Relax the reading producer BEFORE traversing its premises. Its
            // retained settled guard stays unchanged by the proposed replacement.
            if !condition.is_false() && *id != candidate.rule.id {
                for premise in &summary.rule.body {
                    budget.tick("guarded cone premise")?;
                    if program
                        .atom_index
                        .get(&premise.term.atom)
                        .is_some_and(|i| program.atom_components[*i] == component.id)
                        && !atoms.contains(&premise.term.atom)
                    {
                        pending.insert(premise.term.atom.clone());
                    }
                }
            }
            let mut scoped = summary.clone();
            scoped.condition = condition;
            *retained = crate::symbolic::retain(*retained, 0, scoped.nodes() + 1, budget)?;
            selected.insert(*id, scoped);
        }
    }
    let relaxed_rule = atoms
        .contains(&candidate.rule.head.atom)
        .then_some(candidate.rule.id);
    Ok(Arc::new(GuardedCone {
        component: component.id,
        snapshot: program.graph_revision,
        domain,
        relaxed_rule,
        atoms: atoms.into_iter().collect(),
        producers: selected.into_values().collect(),
    }))
}

pub(crate) fn compute(
    cone: &Arc<GuardedCone>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    observe: Option<&dyn Fn(usize)>,
) -> Result<Arc<GuardedBounds>> {
    let (conditions, guarantees) = crate::upper_bounds::iterate(
        &cone.atoms,
        &cone.producers,
        &cone.domain,
        ctx,
        retained,
        budget,
        observe,
        true,
        cone.relaxed_rule,
    )?;
    Ok(Arc::new(GuardedBounds {
        cone: Arc::clone(cone),
        conditions,
        guarantees,
    }))
}

#[cfg(test)]
mod tests;
