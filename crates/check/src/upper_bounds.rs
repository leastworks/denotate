//! Relax unresolved dependencies, then descend from true. Exact guarantees may
//! constrain negative premises. A supported model is
//! contained in every iterate, including the greatest fixed point. Ascending
//! from false would lose that guarantee for self-supporting positive cycles.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not, or};
use std::{collections::BTreeMap, sync::Arc};

/// Shared certificate for discharge or bound-based producer removal. Upper
/// bounds are NOT settled meanings or exact coverage. Only `guarantees`, from
/// producers with entirely settled premises, may supply lower coverage.
#[derive(Debug, Clone)]
pub struct ComponentUpperBounds {
    pub component: ComponentId,
    pub snapshot: u64,
    /// Every active producer in this component at the immutable snapshot.
    pub producers: Vec<ProducerSummary>,
    pub conditions: BTreeMap<GroundAtom, Condition>,
    /// Optional lower guarantees from exact producers only. Empty for legacy
    /// discharge bounds. Never propagated through unresolved premises.
    pub guarantees: BTreeMap<GroundAtom, Condition>,
}
impl ComponentUpperBounds {
    pub(crate) fn nodes(&self) -> usize {
        self.conditions
            .values()
            .chain(self.guarantees.values())
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
    observe: Option<&dyn Fn(usize)>,
) -> Result<Arc<ComponentUpperBounds>> {
    compute_with_guarantees(
        program, component, summaries, ctx, retained, budget, observe, false,
    )
}

pub(crate) fn compute_with_guarantees(
    program: &GroundProgram,
    component: &Component,
    summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    observe: Option<&dyn Fn(usize)>,
    strengthen: bool,
) -> Result<Arc<ComponentUpperBounds>> {
    let mut producers = Vec::new();
    for index in &program.component_rules[component.id.index] {
        let summary = &summaries[&program.rules[*index].id];
        budget.charge(
            1 + summary.rule.body.len() + summary.settled.len(),
            "upper-bound certificate",
        )?;
        *retained = crate::symbolic::retain(*retained, 0, summary.nodes(), budget)?;
        producers.push(summary.clone());
    }
    let mut guarantees = BTreeMap::new();
    if strengthen {
        for producer in &producers {
            budget.tick("bound guarantees")?;
            if !producer.exact {
                continue;
            }
            let head = &producer.rule.head.atom;
            let old = guarantees.get(head);
            let next = if let Some(old) = old {
                ctx.apply(old, &producer.condition, or, budget)?
            } else {
                producer.condition.clone()
            };
            *retained = crate::symbolic::retain(
                *retained,
                old.map_or(0, Condition::node_count),
                next.node_count(),
                budget,
            )?;
            guarantees.insert(head.clone(), next);
        }
    }
    let mut previous = BTreeMap::new();
    let mut previous_nodes = 0;
    for atom in &component.atoms {
        budget.tick("upper-bound initialization")?;
        let top = ctx.true_condition();
        previous_nodes += top.node_count();
        *retained = crate::symbolic::retain(*retained, 0, top.node_count(), budget)?;
        previous.insert(atom.clone(), top);
    }
    let mut iteration = 0;
    loop {
        iteration += 1;
        if let Some(observe) = observe {
            observe(iteration);
        }
        budget.tick("upper-bound iteration")?;
        let mut next = BTreeMap::new();
        let mut next_nodes = 0;
        // Account for both maps while the synchronous round is in progress.
        for atom in &component.atoms {
            budget.tick("upper-bound iteration")?;
            let bottom = ctx.false_condition();
            next_nodes += bottom.node_count();
            *retained = crate::symbolic::retain(*retained, 0, bottom.node_count(), budget)?;
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
                } else if let Some(guarantee) = guarantees.get(&literal.term.atom) {
                    body = ctx.apply(&body, guarantee, and_not, budget)?;
                }
                // Unresolved external premises and unguaranteed internal
                // negatives are omitted. Exact guarantees remain true after
                // deleting any batch of non-exact producers, so the descending
                // bounds contain supported models before AND after deletion.
            }
            let head = next
                .get_mut(&producer.rule.head.atom)
                .ok_or(CheckError::Internal(
                    "upper-bound producer outside component",
                ))?;
            let joined = ctx.apply(head, &body, or, budget)?;
            *retained =
                crate::symbolic::retain(*retained, head.node_count(), joined.node_count(), budget)?;
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
                guarantees,
            }));
        }
        *retained -= previous_nodes;
        previous = next;
        previous_nodes = next_nodes;
    }
}
