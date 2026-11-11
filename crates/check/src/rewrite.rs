//! Conservative rewrites, proved against immutable settled snapshots. Proof
//! references are metadata, never evaluation/dependency edges.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not, or};
use denotate_ir::OccurrenceId;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Inconclusive {
    pub phase: &'static str,
    pub resource: &'static str,
    pub details: LimitDetails,
}
impl Inconclusive {
    pub(crate) fn from_error(error: CheckError) -> Result<Self> {
        match error {
            CheckError::LimitExceeded {
                phase,
                resource,
                details,
            } => Ok(Self {
                phase,
                resource,
                details,
            }),
            error => Err(error),
        }
    }
}
impl From<Inconclusive> for CheckError {
    fn from(c: Inconclusive) -> Self {
        Self::LimitExceeded {
            phase: c.phase,
            resource: c.resource,
            details: c.details,
        }
    }
}

/// Reporting boundary for work that can fail before any groups exist.
#[derive(Debug)]
pub enum AnalysisOutcome<T> {
    Complete(T),
    Inconclusive(Inconclusive),
}
impl<T> AnalysisOutcome<T> {
    pub fn from_result(result: Result<T>) -> Result<Self> {
        match result {
            Ok(value) => Ok(Self::Complete(value)),
            Err(error) => Ok(Self::Inconclusive(Inconclusive::from_error(error)?)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RewriteProofId {
    snapshot: u64,
    index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RewriteKind {
    Discharge { literal_occurrence: OccurrenceId },
    RedundantProducer,
}

#[derive(Debug, Clone)]
pub struct SettledPremise {
    pub literal: GroundLiteral,
    /// Signed condition: already complemented for a negative premise.
    pub condition: Condition,
}
#[derive(Debug, Clone)]
pub struct ProducerSummary {
    /// Executable shape at this proof's snapshot, not a later rewritten shape.
    pub rule: GroundRule,
    pub settled: Vec<SettledPremise>,
    /// Conjunction of settled signed premises only; unresolved ones omitted.
    pub condition: Condition,
    pub exact: bool,
}
impl ProducerSummary {
    fn profile_conditions(&self) -> impl Iterator<Item = &Condition> {
        std::iter::once(&self.condition).chain(self.settled.iter().map(|p| &p.condition))
    }
    pub(crate) fn nodes(&self) -> usize {
        self.condition.node_count()
            + self
                .settled
                .iter()
                .map(|p| p.condition.node_count())
                .sum::<usize>()
    }
}
#[derive(Debug, Clone)]
pub struct RewriteProof {
    pub id: RewriteProofId,
    pub snapshot: u64,
    pub kind: RewriteKind,
    pub candidate: ProducerSummary,
    pub producers: Vec<ProducerSummary>,
    /// Upper bound for discharge; exact coverage for producer removal.
    pub coverage: Condition,
    /// Complete forwarding certificate for discharge, shared within an SCC.
    /// Producer removal instead uses exact coverage and has no such certificate.
    pub upper_bounds: Option<Arc<ComponentUpperBounds>>,
}
impl RewriteProof {
    fn profile_conditions(&self) -> impl Iterator<Item = &Condition> {
        std::iter::once(&self.coverage)
            .chain(self.candidate.profile_conditions())
            .chain(
                self.producers
                    .iter()
                    .flat_map(ProducerSummary::profile_conditions),
            )
            .chain(self.upper_bounds.iter().flat_map(|b| {
                b.conditions.values().chain(
                    b.producers
                        .iter()
                        .flat_map(ProducerSummary::profile_conditions),
                )
            }))
    }
    fn nodes(&self) -> usize {
        std::iter::once(&self.candidate)
            .chain(&self.producers)
            .map(ProducerSummary::nodes)
            .sum::<usize>()
            + self.coverage.node_count()
            + self.upper_bounds.as_ref().map_or(0, |b| b.nodes())
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Rewrites {
    pub dropped: BTreeSet<GroundRuleId>,
    originals: BTreeMap<GroundRuleId, GroundRule>,
    proofs: Vec<RewriteProof>,
    pub inconclusive: Option<Inconclusive>,
    nodes: usize,
}

impl GroundProgram {
    /// Private reconstructed query runtime: explicit owned discharge certificates.
    pub(crate) fn install_local_discharge(
        &mut self,
        original: GroundRule,
        occurrence: OccurrenceId,
        condition: Condition,
        coverage: Condition,
    ) {
        let id = RewriteProofId {
            snapshot: self.preparation,
            index: self.rewrites.proofs.len(),
        };
        self.rewrites
            .originals
            .insert(original.id, original.clone());
        let snapshot = self.preparation;
        self.rewrites.proofs.push(RewriteProof {
            id,
            snapshot,
            kind: RewriteKind::Discharge {
                literal_occurrence: occurrence,
            },
            candidate: ProducerSummary {
                rule: original,
                settled: vec![],
                condition,
                exact: false,
            },
            producers: vec![],
            coverage,
            upper_bounds: None,
        });
    }

    pub fn prepare_checked(
        corpus: &denotate_ir::Corpus,
        domains: &Domains,
        limits: &Limits,
    ) -> Result<AnalysisOutcome<Self>> {
        AnalysisOutcome::from_result(Self::prepare(corpus, domains, limits))
    }

    pub fn rewrite_proofs(&self) -> impl Iterator<Item = &RewriteProof> {
        self.rewrites.proofs.iter()
    }
    pub fn rewrite_proof(&self, id: RewriteProofId) -> Option<&RewriteProof> {
        self.rewrites.proofs.get(id.index).filter(|p| p.id == id)
    }
    pub fn original_rule(&self, id: GroundRuleId) -> Option<&GroundRule> {
        self.rewrites.originals.get(&id).or_else(|| self.rule(id))
    }
    pub fn original_rules(&self) -> impl Iterator<Item = &GroundRule> {
        self.fixed
            .iter()
            .flat_map(|f| f.program.rules.iter())
            .chain(
                self.rules
                    .iter()
                    .map(|r| self.rewrites.originals.get(&r.id).unwrap_or(r)),
            )
    }
    pub fn admission_limit(&self) -> Option<Inconclusive> {
        self.rewrites.inconclusive
    }
    pub(crate) fn discharge(
        &self,
        rule: GroundRuleId,
        occurrence: OccurrenceId,
    ) -> Option<&RewriteProof> {
        self.rewrite_proofs().find(|p| {
            p.candidate.rule.id == rule
                && p.kind
                    == RewriteKind::Discharge {
                        literal_occurrence: occurrence,
                    }
        })
    }

    /// Consume one preparation, retaining source and ground-instance identities.
    /// A limit leaves the last fully committed rewrite batch intact, with an
    /// explicit inconclusive cause for remaining unresolved regions.
    pub fn admit(self, limits: &Limits) -> Result<Self> {
        self.admit_with_budget(&mut Budget::new(limits))
    }
    pub(crate) fn admit_with_budget(self, budget: &mut Budget<'_>) -> Result<Self> {
        self.admit_observed(budget, None)
    }
    pub(crate) fn admit_observed(
        mut self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
    ) -> Result<Self> {
        let progress = crate::admission_progress::AdmissionReporter::new(observer);
        progress.snapshot(&self, 0, "starting");
        let limits = budget.limits;
        limits.cancellation.check()?;
        self.rewrites.inconclusive = None;
        if !self.assumptions_consistent() {
            progress.finish(&self, "inconsistent-assumptions");
            return Ok(self);
        }
        let result = self.rewrite_loop(budget, &progress);
        if let Err(error) = result {
            progress.failed(&self, &error);
            budget.failure(&error);
            self.rewrites.inconclusive = Some(Inconclusive::from_error(error)?);
        } else {
            progress.finish(&self, "complete");
        }
        limits.cancellation.check()?;
        Ok(self)
    }

    fn rewrite_loop(
        &mut self,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<()> {
        let profile = budget.limits.profile.clone();
        let mut round = 0;
        loop {
            if self.is_admitted()
                && self.input_groups.is_empty()
                && self.assumption_condition.is_none()
            {
                return Ok(());
            }
            round += 1;
            progress.snapshot(self, round, "symbolic");
            let _round_profile = profile.span("admission-round", Some(round));
            budget.tick("rewrite snapshot")?;
            let meaning = {
                let mut stage = profile.span("admission-symbolic", Some(round));
                let observe = |id| progress.work(self, "symbolic", Some(id), 0, false);
                let meaning =
                    self.symbolic_for_admission(budget, progress.enabled().then_some(&observe))?;
                if profile.enabled() {
                    stage.retained(crate::boolean::condition_storage(
                        meaning
                            .conditions
                            .values()
                            .chain(meaning.context.stored_conditions()),
                    ));
                }
                meaning
            };
            let ctx = meaning.context();
            let mut summaries_profile = profile.span("admission-summaries", Some(round));
            progress.work(self, "summaries", None, 0, true);
            let mut summaries = BTreeMap::new();
            let mut producers = BTreeMap::<_, Vec<_>>::new();
            let mut retained = self.rewrites.nodes + meaning.metrics().retained_condition_nodes;
            for (position, rule) in self
                .rules
                .iter()
                .filter(|r| !self.rewrites.dropped.contains(&r.id))
                .enumerate()
            {
                progress.rule(self, "summaries", rule.id, position + 1);
                budget.tick("rewrite summaries")?;
                let mut condition = ctx.true_condition();
                let mut settled = Vec::new();
                let mut exact = true;
                for literal in &rule.body {
                    budget.tick("rewrite summaries")?;
                    match meaning.fact(&literal.term.atom)? {
                        SymbolicFact::Blocked(_) => exact = false,
                        SymbolicFact::Inconclusive(cause) => {
                            return Err(CheckError::from(cause));
                        }
                        SymbolicFact::Settled(mut value) => {
                            if literal.polarity == Polarity::Negative {
                                value = ctx.complement(&value, budget)?;
                            }
                            condition = ctx.apply(&condition, &value, and, budget)?;
                            retained =
                                crate::symbolic::retain(retained, 0, value.node_count(), budget)?;
                            settled.push(SettledPremise {
                                literal: literal.clone(),
                                condition: value,
                            });
                        }
                    }
                }
                retained = crate::symbolic::retain(retained, 0, condition.node_count(), budget)?;
                summaries.insert(
                    rule.id,
                    ProducerSummary {
                        rule: rule.clone(),
                        settled,
                        condition,
                        exact,
                    },
                );
                producers.entry(&rule.head.atom).or_default().push(rule.id);
            }
            if profile.enabled() {
                summaries_profile.retained(crate::boolean::condition_storage(
                    meaning
                        .conditions
                        .values()
                        .chain(ctx.stored_conditions())
                        .chain(summaries.values().flat_map(|s| {
                            std::iter::once(&s.condition)
                                .chain(s.settled.iter().map(|p| &p.condition))
                        })),
                ));
            }
            drop(summaries_profile);
            let mut candidates_profile = profile.span("admission-candidates", Some(round));
            progress.work(self, "candidates", None, 0, true);
            let mut batch = Vec::new();
            let mut upper_bounds = BTreeMap::new();
            for (position, rule) in self
                .rules
                .iter()
                .filter(|r| !self.rewrites.dropped.contains(&r.id))
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
                        let mut guard = candidate.clone();
                        guard.settled.retain(|p| {
                            p.literal.term.occurrence != excluded.literal.term.occurrence
                        });
                        guard.condition = ctx.true_condition();
                        for premise in &guard.settled {
                            guard.condition =
                                ctx.apply(&guard.condition, &premise.condition, and, budget)?;
                        }
                        let coverage =
                            ctx.input_with_budget(&excluded.literal.term.atom, budget)?;
                        let conflict = ctx.apply(&guard.condition, &coverage, and, budget)?;
                        if !conflict.is_false()
                            && !ctx.restrict(&guard.condition, budget)?.is_false()
                            && ctx.restrict(&conflict, budget)?.is_false()
                        {
                            self.propose(
                                &mut batch,
                                &guard,
                                vec![],
                                coverage,
                                RewriteKind::Discharge {
                                    literal_occurrence: excluded.literal.term.occurrence,
                                },
                                None,
                                &mut retained,
                                budget,
                            )?;
                            // Another negation may rely on this one. Rebuild
                            // its guard next round before proposing its removal.
                            break;
                        }
                    }
                    continue;
                }
                let covering: Vec<_> = producers[&rule.head.atom]
                    .iter()
                    .filter_map(|id| summaries.get(id).filter(|s| s.exact))
                    .collect();
                let mut coverage = ctx.false_condition();
                for p in &covering {
                    coverage = ctx.apply(&coverage, &p.condition, or, budget)?;
                }
                if !covering.is_empty()
                    && ctx
                        .restrict(
                            &ctx.apply(&candidate.condition, &coverage, and_not, budget)?,
                            budget,
                        )?
                        .is_false()
                {
                    self.propose(
                        &mut batch,
                        candidate,
                        covering,
                        coverage,
                        RewriteKind::RedundantProducer,
                        None,
                        &mut retained,
                        budget,
                    )?;
                    continue; // A whole-rule removal takes precedence over literal warnings.
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
                        entry.insert(crate::upper_bounds::compute(
                            self,
                            component,
                            &summaries,
                            ctx,
                            &mut retained,
                            budget,
                            progress.enabled().then_some(&observe),
                        )?);
                        progress.work(self, "candidates", Some(component.id), position + 1, true);
                    }
                    let bounds = &upper_bounds[&component.id];
                    let coverage = bounds.conditions[&literal.term.atom].clone();
                    if ctx
                        .restrict(
                            &ctx.apply(&candidate.condition, &coverage, and, budget)?,
                            budget,
                        )?
                        .is_false()
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
                            &mut retained,
                            budget,
                        )?;
                    }
                }
            }
            if profile.enabled() {
                candidates_profile.retained(crate::boolean::condition_storage(
                    meaning
                        .conditions
                        .values()
                        .chain(ctx.stored_conditions())
                        .chain(
                            summaries
                                .values()
                                .flat_map(ProducerSummary::profile_conditions),
                        )
                        .chain(upper_bounds.values().flat_map(|b| {
                            b.conditions.values().chain(
                                b.producers
                                    .iter()
                                    .flat_map(ProducerSummary::profile_conditions),
                            )
                        }))
                        .chain(
                            batch
                                .iter()
                                .chain(self.rewrites.proofs.iter())
                                .flat_map(RewriteProof::profile_conditions),
                        ),
                ));
            }
            drop(candidates_profile);
            if batch.is_empty() {
                return Ok(());
            }
            let _commit_profile = profile.span("admission-commit", Some(round));
            progress.work(self, "commit", None, 0, true);
            // Transactional graph rebuild: an interrupted batch cannot leave a
            // half-rewritten graph or publish warnings for uncommitted changes.
            budget.charge(
                self.atoms.len() + self.rules.iter().map(|r| 1 + r.body.len()).sum::<usize>(),
                "rewrite commit",
            )?;
            let mut next = self.clone();
            for proof in batch {
                let id = proof.candidate.rule.id;
                next.rewrites
                    .originals
                    .entry(id)
                    .or_insert_with(|| self.rules[id.index].clone());
                match proof.kind {
                    RewriteKind::RedundantProducer => {
                        next.rewrites.dropped.insert(id);
                    }
                    RewriteKind::Discharge { literal_occurrence } => next.rules[id.index]
                        .body
                        .retain(|l| l.term.occurrence != literal_occurrence),
                }
                next.rewrites.nodes += proof.nodes();
                next.rewrites.proofs.push(proof);
            }
            crate::graph::analyze(&mut next, budget)?;
            *self = next;
            progress.snapshot(self, round, "committed");
        }
    }

    fn propose(
        &self,
        batch: &mut Vec<RewriteProof>,
        candidate: &ProducerSummary,
        producers: Vec<&ProducerSummary>,
        coverage: Condition,
        kind: RewriteKind,
        upper_bounds: Option<Arc<ComponentUpperBounds>>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        budget.tick("rewrite proof")?;
        // Conservative accounting also counts shared certificates per proof.
        let mut nodes = coverage.node_count() + upper_bounds.as_ref().map_or(0, |b| b.nodes());
        for summary in std::iter::once(candidate).chain(producers.iter().copied()) {
            budget.charge(
                1 + summary.rule.body.len() + summary.settled.len(),
                "rewrite proof storage",
            )?;
            nodes += summary.nodes();
        }
        *retained = crate::symbolic::retain(*retained, 0, nodes, budget)?;
        let proof = RewriteProof {
            id: RewriteProofId {
                snapshot: self.graph_revision,
                index: self.rewrites.proofs.len() + batch.len(),
            },
            snapshot: self.graph_revision,
            kind,
            candidate: candidate.clone(),
            producers: producers.into_iter().cloned().collect(),
            coverage,
            upper_bounds,
        };
        batch.push(proof);
        Ok(())
    }
}
