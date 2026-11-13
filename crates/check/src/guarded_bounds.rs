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
    ops::Deref,
    sync::Arc,
};

#[derive(Debug, Clone)]
pub struct GuardedProducer<S = Arc<ProducerSummary>> {
    /// Unmasked, immutable summary at the certificate's snapshot.
    pub summary: S,
    /// Whether its settled guard intersects this cone's domain.
    pub live: bool,
}
impl<S: Deref<Target = ProducerSummary>> Deref for GuardedProducer<S> {
    type Target = ProducerSummary;
    fn deref(&self) -> &Self::Target {
        &self.summary
    }
}

#[derive(Debug, Clone)]
pub struct GuardedCone<S = Arc<ProducerSummary>> {
    pub component: ComponentId,
    pub snapshot: u64,
    pub domain: Condition,
    pub relaxed_rule: Option<GroundRuleId>,
    pub atoms: Vec<GroundAtom>,
    /// Dead producers remain evidence, but their premises do not extend the cone.
    pub producers: Vec<GuardedProducer<S>>,
}
impl<S: Deref<Target = ProducerSummary>> GuardedCone<S> {
    pub(crate) fn temporary_nodes(&self) -> usize {
        // Charge cache/key metadata too, conservatively as condition-node slots.
        // Summaries are borrowed from the already-accounted round.
        self.domain.node_count() + self.atoms.len() + 2 * self.producers.len() + 1
    }
    pub(crate) fn nodes(&self) -> usize {
        // A committed certificate outlives the round. Keep conservative ownership
        // charges, including individually shared summaries, on that proof.
        self.temporary_nodes() + self.producers.iter().map(|p| p.nodes()).sum::<usize>()
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
                .map(|p| (p.rule.id, p.live))
                .eq(other.producers.iter().map(|p| (p.rule.id, p.live))))
    }
}

#[derive(Debug, Clone)]
pub struct GuardedBounds<S = Arc<ProducerSummary>> {
    pub cone: Arc<GuardedCone<S>>,
    pub conditions: BTreeMap<GroundAtom, Condition>,
    pub guarantees: BTreeMap<GroundAtom, Condition>,
}
impl<S: Deref<Target = ProducerSummary>> GuardedBounds<S> {
    fn value_nodes(&self) -> usize {
        self.conditions
            .values()
            .chain(self.guarantees.values())
            .map(Condition::node_count)
            .sum::<usize>()
    }
    pub(crate) fn temporary_nodes(&self) -> usize {
        self.cone.temporary_nodes() + self.value_nodes()
    }
    pub(crate) fn nodes(&self) -> usize {
        self.cone.nodes() + self.value_nodes()
    }
}

pub(crate) type BorrowedCone<'a> = GuardedCone<&'a ProducerSummary>;
pub(crate) type BorrowedBounds<'a> = GuardedBounds<&'a ProducerSummary>;

impl BorrowedBounds<'_> {
    pub(crate) fn owned(&self, budget: &mut Budget<'_>) -> Result<Arc<GuardedBounds>> {
        budget.charge(
            self.cone.atoms.len() + self.conditions.len() + self.guarantees.len(),
            "guarded certificate snapshot",
        )?;
        let mut producers = Vec::new();
        for p in &self.cone.producers {
            budget.charge(
                1 + p.rule.body.len() + p.settled.len(),
                "guarded certificate snapshot",
            )?;
            producers.push(GuardedProducer {
                summary: Arc::new(p.summary.clone()),
                live: p.live,
            });
        }
        Ok(Arc::new(GuardedBounds {
            cone: Arc::new(GuardedCone {
                component: self.cone.component,
                snapshot: self.cone.snapshot,
                domain: self.cone.domain.clone(),
                relaxed_rule: self.cone.relaxed_rule,
                atoms: self.cone.atoms.clone(),
                producers,
            }),
            conditions: self.conditions.clone(),
            guarantees: self.guarantees.clone(),
        }))
    }
}

/// Measurements survive a failed preparation after its partial cone is dropped.
#[derive(Debug, Default)]
pub(crate) struct Preparation {
    pub domain_nodes: Option<usize>,
    pub visited_atoms: usize,
    pub live_atoms: usize,
    pub visited_producers: usize,
    pub live_producers: usize,
    pub existing_nodes: usize,
    pub added_nodes: usize,
}

pub(crate) fn prepare<'a>(
    program: &GroundProgram,
    component: &Component,
    candidate: &ProducerSummary,
    root: &GroundAtom,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    stats: &mut Preparation,
) -> Result<Arc<BorrowedCone<'a>>> {
    *stats = Preparation {
        existing_nodes: *retained,
        ..Preparation::default()
    };
    let result = prepare_inner(
        program, component, candidate, root, summaries, producers, ctx, retained, budget, stats,
    );
    stats.added_nodes = retained.saturating_sub(stats.existing_nodes);
    result
}

fn prepare_inner<'a>(
    program: &GroundProgram,
    component: &Component,
    candidate: &ProducerSummary,
    root: &GroundAtom,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    stats: &mut Preparation,
) -> Result<Arc<BorrowedCone<'a>>> {
    let domain = ctx.restrict(&candidate.condition, budget)?;
    stats.domain_nodes = Some(domain.node_count());
    *retained = crate::symbolic::retain(*retained, 0, domain.node_count() + 1, budget)?;
    let mut pending = BTreeSet::from([root.clone()]);
    let mut atoms = BTreeSet::new();
    let mut selected = BTreeMap::new();
    while let Some(atom) = pending.pop_first() {
        budget.tick("guarded cone atom")?;
        if !atoms.insert(atom.clone()) {
            continue;
        }
        stats.visited_atoms += 1;
        *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
        let mut live_atom = false;
        for id in producers.get(&atom).into_iter().flatten() {
            stats.visited_producers += 1;
            let summary = &summaries[id];
            budget.charge(
                1 + summary.rule.body.len() + summary.settled.len(),
                "guarded cone producer",
            )?;
            // Restrict transiently for deadness; do not retain one copy of the
            // (potentially large) domain per producer.
            let live = !ctx
                .apply(&domain, &summary.condition, and, budget)?
                .is_false();
            if live {
                stats.live_producers += 1;
                if !live_atom {
                    stats.live_atoms += 1;
                    live_atom = true;
                }
            }
            // Relax the reading producer BEFORE traversing its premises. Its
            // retained settled guard stays unchanged by the proposed replacement.
            if live && *id != candidate.rule.id {
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
            *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
            selected.insert(*id, GuardedProducer { summary, live });
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

pub(crate) fn compute<'a>(
    cone: &Arc<BorrowedCone<'a>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    observe: Option<&dyn Fn(usize)>,
) -> Result<Arc<BorrowedBounds<'a>>> {
    let (conditions, guarantees) = crate::upper_bounds::iterate(
        &cone.atoms,
        cone.producers.iter().map(|p| (p.summary, p.live)),
        Some(&cone.domain),
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
