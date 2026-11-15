//! Component-owned pending proofs. Shared summaries and committed proofs are borrowed.
use crate::{
    admission_skips::{Attempt, Attempts},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not, or};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

impl GroundProgram {
    pub(crate) fn producer_removals(
        &self,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        targets: &BTreeSet<GroundRuleId>,
        producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
        ctx: &ConditionContext,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
        attempts: &mut Attempts,
    ) -> Result<Vec<RewriteProof>> {
        let mut batch = Vec::new();
        let mut last_candidates = BTreeMap::new();
        for id in targets {
            budget.tick("removal coverage lifetime")?;
            let s = &summaries[id];
            if !s.exact {
                last_candidates.insert(&s.rule.head.atom, *id);
            }
        }
        // References borrow the already-accounted summaries. Only the union
        // adds retained condition storage; proofs keep their own existing
        // conservative charges, including shared coverage per proof.
        let mut exact_coverage: BTreeMap<_, Option<(Vec<&ProducerSummary>, Condition)>> =
            BTreeMap::new();
        for (position, rule) in targets
            .iter()
            .map(|id| self.rule(*id).expect("live target"))
            .enumerate()
        {
            progress.rule(self, "producer-removals", rule.id, position + 1);
            budget.tick("rewrite candidates")?;
            let candidate = &summaries[&rule.id];
            if candidate.exact {
                continue;
            }
            if attempts.reuse_negative(&Attempt::Removal(rule.id), budget, progress)? {
                if last_candidates[&rule.head.atom] == rule.id {
                    if let Some((_, coverage)) = exact_coverage.remove(&rule.head.atom).flatten() {
                        *retained -= coverage.node_count();
                    }
                }
                continue;
            }
            if let std::collections::btree_map::Entry::Vacant(entry) =
                exact_coverage.entry(&rule.head.atom)
            {
                let covering: Vec<_> = producers[&rule.head.atom]
                    .iter()
                    .filter_map(|id| summaries.get(id).filter(|s| s.exact))
                    .collect();
                let value = if covering.is_empty() {
                    // Remember the empty set without retaining a condition.
                    None
                } else {
                    attempts
                        .run(
                            Attempt::Coverage(rule.head.atom.clone()),
                            &rule.head.atom,
                            self,
                            retained,
                            budget,
                            progress,
                            |retained, budget| {
                                let mut coverage = ctx.false_condition();
                                *retained = crate::symbolic::retain(
                                    *retained,
                                    0,
                                    coverage.node_count(),
                                    budget,
                                )?;
                                for p in &covering {
                                    let next = ctx.apply(&coverage, &p.condition, or, budget)?;
                                    *retained = crate::symbolic::retain(
                                        *retained,
                                        coverage.node_count(),
                                        next.node_count(),
                                        budget,
                                    )?;
                                    coverage = next;
                                }
                                Ok(coverage)
                            },
                        )?
                        .map(|coverage| (covering, coverage))
                };
                entry.insert(value);
            }
            if let Some((covering, coverage)) = &exact_coverage[&rule.head.atom]
                && attempts.proof(
                    Attempt::Removal(rule.id),
                    &rule.head.atom,
                    self,
                    retained,
                    budget,
                    progress,
                    |proved| !proved,
                    |_, budget| {
                        Ok(ctx
                            .restrict(
                                &ctx.apply(&candidate.condition, coverage, and_not, budget)?,
                                budget,
                            )?
                            .is_false())
                    },
                )? == Some(true)
            {
                self.propose(
                    &mut batch,
                    candidate,
                    covering.clone(),
                    coverage.clone(),
                    RewriteKind::RedundantProducer,
                    None,
                    retained,
                    budget,
                )?;
            }
            if last_candidates[&rule.head.atom] == rule.id {
                if let Some((_, coverage)) = exact_coverage.remove(&rule.head.atom).flatten() {
                    *retained -= coverage.node_count();
                }
            }
        }
        debug_assert!(exact_coverage.is_empty());
        Ok(batch)
    }
    pub(crate) fn discharges(
        &self,
        meaning: &SymbolicMeaning<'_>,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        targets: &BTreeSet<GroundRuleId>,
        producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
        phase: AdmissionPhase,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
        attempts: &mut Attempts,
    ) -> Result<Vec<RewriteProof>> {
        let ctx = meaning.context();
        let mut batch = Vec::new();
        let mut upper_bounds = BTreeMap::new();
        for (position, rule) in targets
            .iter()
            .map(|id| self.rule(*id).expect("live target"))
            .enumerate()
        {
            progress.rule(self, "candidates", rule.id, position + 1);
            budget.tick("rewrite candidates")?;
            let candidate = &summaries[&rule.id];
            if candidate.exact {
                // Narrow value guard rule: only input negations whose
                // redundancy depends on W, proved from the OTHER premises.
                for excluded in candidate.settled.iter().filter(|p| {
                    p.literal.polarity == Polarity::Negative
                        && self.inputs.contains(&p.literal.term.atom)
                }) {
                    if attempts.reuse_negative(
                        &Attempt::Discharge(rule.id, excluded.literal.term.occurrence),
                        budget,
                        progress,
                    )? {
                        continue;
                    }
                    let proof = attempts
                        .proof(
                            Attempt::Discharge(rule.id, excluded.literal.term.occurrence),
                            &rule.head.atom,
                            self,
                            retained,
                            budget,
                            progress,
                            Option::is_none,
                            |_, budget| {
                                let mut guard = candidate.clone();
                                guard.settled.retain(|p| {
                                    p.literal.term.occurrence != excluded.literal.term.occurrence
                                });
                                guard.condition = ctx.true_condition();
                                for replacement in &rule.replacements {
                                    let value = meaning
                                        .settled_expression(&replacement.expression, budget)?;
                                    guard.condition =
                                        ctx.apply(&guard.condition, &value, and, budget)?;
                                }
                                for premise in &guard.settled {
                                    guard.condition = ctx.apply(
                                        &guard.condition,
                                        &premise.condition,
                                        and,
                                        budget,
                                    )?;
                                }
                                let coverage =
                                    ctx.input_with_budget(&excluded.literal.term.atom, budget)?;
                                let conflict =
                                    ctx.apply(&guard.condition, &coverage, and, budget)?;
                                Ok((!conflict.is_false()
                                    && !ctx.restrict(&guard.condition, budget)?.is_false()
                                    && ctx.restrict(&conflict, budget)?.is_false())
                                .then_some((guard, coverage)))
                            },
                        )?
                        .flatten();
                    if let Some((guard, coverage)) = proof {
                        self.propose(
                            &mut batch,
                            &guard,
                            vec![],
                            coverage,
                            RewriteKind::Discharge {
                                literal_occurrence: excluded.literal.term.occurrence,
                            },
                            None,
                            retained,
                            budget,
                        )?;
                        // Another negation may rely on this one. Rebuild
                        // its guard next round before proposing its removal.
                        break;
                    }
                }
                continue;
            }
            if phase == AdmissionPhase::Downstream {
                continue;
            }
            let component = self.component_for(&rule.head.atom)?;
            for literal in &rule.body {
                budget.tick("rewrite candidates")?;
                if literal.polarity != Polarity::Negative
                    || self.inputs.contains(&literal.term.atom)
                    || !self.is_possible(&literal.term.atom)?
                    || self.component_for(&literal.term.atom)?.id != component.id
                {
                    continue;
                }
                if attempts.reuse_negative(
                    &Attempt::Discharge(rule.id, literal.term.occurrence),
                    budget,
                    progress,
                )? {
                    continue;
                }
                let covering: Vec<_> = producers
                    .get(&literal.term.atom)
                    .into_iter()
                    .flatten()
                    .map(|id| &summaries[id])
                    .collect();
                if let std::collections::btree_map::Entry::Vacant(entry) =
                    upper_bounds.entry(component.id)
                {
                    progress.work(self, "upper-bounds", Some(component.id), position + 1, true);
                    let observe = |iteration| progress.iteration(self, iteration);
                    let head = component.atoms.first().unwrap();
                    entry.insert(attempts.run(
                        Attempt::UpperBounds(head.clone()),
                        head,
                        self,
                        retained,
                        budget,
                        progress,
                        |retained, budget| {
                            crate::upper_bounds::compute(
                                self,
                                component,
                                summaries,
                                ctx,
                                retained,
                                budget,
                                progress.enabled().then_some(&observe),
                            )
                        },
                    )?);
                    progress.work(self, "candidates", Some(component.id), position + 1, true);
                }
                let Some(bounds) = &upper_bounds[&component.id] else {
                    continue;
                };
                let coverage = bounds.conditions[&literal.term.atom].clone();
                if attempts.proof(
                    Attempt::Discharge(rule.id, literal.term.occurrence),
                    &rule.head.atom,
                    self,
                    retained,
                    budget,
                    progress,
                    |proved| !proved,
                    |_, budget| {
                        Ok(ctx
                            .restrict(
                                &ctx.apply(&candidate.condition, &coverage, and, budget)?,
                                budget,
                            )?
                            .is_false())
                    },
                )? == Some(true)
                {
                    self.propose(
                        &mut batch,
                        candidate,
                        covering,
                        coverage,
                        RewriteKind::Discharge {
                            literal_occurrence: literal.term.occurrence,
                        },
                        Some(Arc::clone(bounds)),
                        retained,
                        budget,
                    )?;
                }
            }
        }
        let nodes = upper_bounds
            .values()
            .flatten()
            .map(|b| b.nodes())
            .sum::<usize>();
        drop(upper_bounds);
        *retained -= nodes;
        Ok(batch)
    }
}
