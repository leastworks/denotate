//! Relax negative dependencies, then descend from true. A supported model is
//! contained in every iterate, including the greatest fixed point. Ascending
//! from false would lose that guarantee for self-supporting positive cycles.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not, or};
use std::{collections::BTreeMap, sync::Arc};

/// Shared certificate for discharge through positive forwarding. These are
/// upper bounds, NOT settled meanings or exact coverage for producer removal.
#[derive(Debug, Clone)]
pub struct ComponentUpperBounds {
    pub component: ComponentId,
    pub snapshot: u64,
    /// Every active producer in this component at the immutable snapshot.
    pub producers: Vec<ProducerSummary>,
    pub conditions: BTreeMap<GroundAtom, Condition>,
}
impl ComponentUpperBounds {
    pub(crate) fn nodes(&self) -> usize {
        self.conditions
            .values()
            .map(Condition::node_count)
            .sum::<usize>()
            + self
                .producers
                .iter()
                .map(ProducerSummary::nodes)
                .sum::<usize>()
    }
}

pub(crate) fn compute(
    program: &GroundProgram,
    component: &Component,
    summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<Arc<ComponentUpperBounds>> {
    let mut producers = Vec::new();
    for index in &program.component_rules[component.id.index] {
        let summary = &summaries[&program.rules[*index].id];
        budget.charge(
            1 + summary.rule.body.len() + summary.settled.len(),
            "upper-bound certificate",
        )?;
        *retained = crate::symbolic::retain(*retained, 0, summary.nodes(), budget.limits)?;
        producers.push(summary.clone());
    }
    let mut previous = BTreeMap::new();
    let mut previous_nodes = 0;
    for atom in &component.atoms {
        budget.tick("upper-bound initialization")?;
        let top = ctx.true_condition();
        previous_nodes += top.node_count();
        *retained = crate::symbolic::retain(*retained, 0, top.node_count(), budget.limits)?;
        previous.insert(atom.clone(), top);
    }
    loop {
        budget.tick("upper-bound iteration")?;
        let mut next = BTreeMap::new();
        let mut next_nodes = 0;
        // Account for both maps while the synchronous round is in progress.
        for atom in &component.atoms {
            budget.tick("upper-bound iteration")?;
            let bottom = ctx.false_condition();
            next_nodes += bottom.node_count();
            *retained = crate::symbolic::retain(*retained, 0, bottom.node_count(), budget.limits)?;
            next.insert(atom.clone(), bottom);
        }
        for producer in &producers {
            budget.tick("upper-bound iteration")?;
            let mut body = producer.condition.clone(); // all settled signed premises
            for literal in &producer.rule.body {
                budget.tick("upper-bound iteration")?;
                if literal.polarity == Polarity::Positive {
                    if let Some(bound) = previous.get(&literal.term.atom) {
                        body = ctx.apply(&body, bound, and, budget)?;
                    }
                }
                // Unresolved external positives and all internal negatives are
                // omitted. Neither is assumed false or used as exact knowledge.
            }
            let head = next
                .get_mut(&producer.rule.head.atom)
                .ok_or(CheckError::Internal(
                    "upper-bound producer outside component",
                ))?;
            let joined = ctx.apply(head, &body, or, budget)?;
            *retained = crate::symbolic::retain(
                *retained,
                head.node_count(),
                joined.node_count(),
                budget.limits,
            )?;
            next_nodes = next_nodes - head.node_count() + joined.node_count();
            *head = joined;
        }
        let mut changed = false;
        for (atom, old) in &previous {
            budget.tick("upper-bound convergence")?;
            // Descending by construction; compare meanings, not BDD layouts.
            changed |= !ctx.apply(old, &next[atom], and_not, budget)?.is_false();
        }
        if !changed {
            *retained -= next_nodes;
            return Ok(Arc::new(ComponentUpperBounds {
                component: component.id,
                snapshot: program.graph_revision,
                producers,
                conditions: previous,
            }));
        }
        *retained -= previous_nodes;
        previous = next;
        previous_nodes = next_nodes;
    }
}
