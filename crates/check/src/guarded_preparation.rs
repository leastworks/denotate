//! Admission-local prepared cones. Only IDs, pruning metadata and the domain
//! survive a round; current summaries are rebound on use. No bounds are retained.
use crate::{
    guarded_bounds::{BorrowedCone, GuardedProducer, Preparation, Pruning},
    limits::{Budget, Result},
    *,
};
use std::{collections::BTreeMap, sync::Arc};

pub(crate) struct PreparedCone {
    pub head: GroundAtom,
    domain: Condition,
    guard: Condition,
    permitted: Condition,
    relaxed_rule: Option<GroundRuleId>,
    atoms: Vec<GroundAtom>,
    producers: Vec<(GroundRuleId, bool)>,
    reasons: BTreeMap<GroundRuleId, crate::guarded_bounds::DeadReason>,
    sources: Vec<GroundRuleId>,
    pub stats: Preparation,
}
impl PreparedCone {
    pub(crate) fn profile_conditions(&self) -> impl Iterator<Item = &Condition> {
        [&self.domain, &self.guard, &self.permitted].into_iter()
    }
    pub fn capture(
        head: &GroundAtom,
        cone: &BorrowedCone<'_>,
        guard: &Condition,
        permitted: Condition,
        stats: &Preparation,
    ) -> Self {
        Self {
            head: head.clone(),
            domain: cone.domain.clone(),
            guard: guard.clone(),
            permitted,
            relaxed_rule: cone.relaxed_rule,
            atoms: cone.atoms.clone(),
            producers: cone.producers.iter().map(|p| (p.rule.id, p.live)).collect(),
            reasons: cone.pruning.reasons.clone(),
            sources: cone.pruning.sources.iter().map(|p| p.rule.id).collect(),
            stats: stats.clone(),
        }
    }
    pub fn nodes(&self) -> usize {
        self.domain.node_count()
            + self.guard.node_count()
            + self.permitted.node_count()
            + self.atoms.len()
            + self.producers.len() * 2
            + self.sources.len()
            + self
                .reasons
                .values()
                .map(|r| {
                    3 + match r {
                        crate::guarded_bounds::DeadReason::Negative {
                            exact_producers, ..
                        } => exact_producers.len(),
                        _ => 0,
                    }
                })
                .sum::<usize>()
            + 16
    }
    pub fn bind<'a>(
        &self,
        program: &GroundProgram,
        guard: &Condition,
        permitted: &Condition,
        summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Arc<BorrowedCone<'a>>>> {
        budget.charge(
            self.atoms.len()
                + self.producers.len()
                + self.sources.len()
                + guard.node_count()
                + permitted.node_count(),
            "guarded preparation reuse",
        )?;
        if !self.guard.same_representation(guard) || !self.permitted.same_representation(permitted)
        {
            return Ok(None);
        }
        let Some(producers) = self
            .producers
            .iter()
            .map(|(id, live)| {
                summaries.get(id).map(|summary| GuardedProducer {
                    summary,
                    live: *live,
                })
            })
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        let Some(sources) = self
            .sources
            .iter()
            .map(|id| summaries.get(id))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        let cone = Arc::new(GuardedCone {
            component: program.component_for(&self.head)?.id,
            snapshot: program.graph_revision,
            domain: self.domain.clone(),
            relaxed_rule: self.relaxed_rule,
            atoms: self.atoms.clone(),
            producers,
            pruning: Pruning {
                reasons: self.reasons.clone(),
                sources,
            },
        });
        *retained = crate::symbolic::retain(*retained, 0, cone.temporary_nodes(), budget)?;
        Ok(Some(cone))
    }
}
