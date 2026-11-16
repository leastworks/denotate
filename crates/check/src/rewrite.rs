//! Conservative rewrites, proved against immutable settled snapshots. Proof
//! references are metadata, never evaluation/dependency edges.
use crate::{
    admission_skips::{Attempt, Attempts},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not};
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
    GuardedSettlement { literal_occurrence: OccurrenceId },
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
pub struct SymbolicRewriteProof {
    pub candidate: ProducerSummary,
    pub producers: Vec<ProducerSummary>,
    pub coverage: Condition,
    pub upper_bounds: Option<Arc<ComponentUpperBounds>>,
}
#[derive(Debug, Clone)]
pub struct BoundRemovalProof {
    pub proof: SymbolicRewriteProof,
    /// Strengthened upper bound of this producer's complete signed body.
    pub body_upper: Condition,
}
#[derive(Debug, Clone)]
pub enum RewriteJustification {
    Symbolic(SymbolicRewriteProof),
    Structural(crate::structural::StructuralProof),
    BoundRemoval(BoundRemovalProof),
    GuardedSettlement(GuardedSettlementProof),
}
#[derive(Debug, Clone)]
pub struct RewriteProof {
    pub id: RewriteProofId,
    pub snapshot: u64,
    pub kind: RewriteKind,
    pub justification: RewriteJustification,
}
impl RewriteProof {
    pub fn candidate(&self) -> &GroundRule {
        match &self.justification {
            RewriteJustification::Symbolic(p) => &p.candidate.rule,
            RewriteJustification::Structural(p) => &p.candidate,
            RewriteJustification::BoundRemoval(p) => &p.proof.candidate.rule,
            RewriteJustification::GuardedSettlement(p) => &p.proof.candidate.rule,
        }
    }
    pub fn symbolic(&self) -> Option<&SymbolicRewriteProof> {
        match &self.justification {
            RewriteJustification::Symbolic(p) => Some(p),
            _ => None,
        }
    }
    pub fn structural(&self) -> Option<&crate::structural::StructuralProof> {
        match &self.justification {
            RewriteJustification::Structural(p) => Some(p),
            _ => None,
        }
    }
    pub fn bound_removal(&self) -> Option<&BoundRemovalProof> {
        match &self.justification {
            RewriteJustification::BoundRemoval(p) => Some(p),
            _ => None,
        }
    }
    pub fn guarded_settlement(&self) -> Option<&GuardedSettlementProof> {
        match &self.justification {
            RewriteJustification::GuardedSettlement(p) => Some(p),
            _ => None,
        }
    }
    pub(crate) fn conditional(&self) -> Option<&SymbolicRewriteProof> {
        self.symbolic()
            .or_else(|| self.bound_removal().map(|p| &p.proof))
            .or_else(|| self.guarded_settlement().map(|p| &p.proof))
    }
    pub fn supporting_rules(&self) -> Vec<&GroundRule> {
        match &self.justification {
            RewriteJustification::Symbolic(p) => p.producers.iter().map(|p| &p.rule).collect(),
            RewriteJustification::Structural(p) => p.supporting_rules(),
            RewriteJustification::GuardedSettlement(p) => p
                .certificate
                .summaries()
                .map(|p| &p.rule)
                .chain(
                    p.implied_guard
                        .iter()
                        .flat_map(|g| g.summaries().map(|s| &s.rule)),
                )
                .collect(),
            RewriteJustification::BoundRemoval(p) => p
                .proof
                .upper_bounds
                .as_ref()
                .expect("bound certificate")
                .producers
                .iter()
                .map(|p| &p.rule)
                .collect(),
        }
    }
    /// Direct evidence for keys and ordinary presentation. Full structural
    /// support is expanded only by an explicit detailed-evidence request.
    pub fn direct_rules(&self) -> Vec<&GroundRule> {
        match &self.justification {
            RewriteJustification::Symbolic(p) => p.producers.iter().map(|p| &p.rule).collect(),
            RewriteJustification::Structural(p) => p.direct_rules(),
            RewriteJustification::GuardedSettlement(p) => p
                .proof
                .producers
                .iter()
                .map(|p| &p.rule)
                .chain(
                    p.implied_guard
                        .iter()
                        .flat_map(|g| g.summaries().map(|s| &s.rule)),
                )
                .collect(),
            RewriteJustification::BoundRemoval(p) => {
                p.proof.producers.iter().map(|p| &p.rule).collect()
            }
        }
    }
    pub(crate) fn summaries(&self) -> impl Iterator<Item = &ProducerSummary> {
        self.conditional()
            .into_iter()
            .flat_map(|p| {
                std::iter::once(&p.candidate)
                    .chain(&p.producers)
                    .chain(p.upper_bounds.iter().flat_map(|b| b.producers.iter()))
            })
            .chain(self.guarded_settlement().into_iter().flat_map(|p| {
                p.certificate
                    .summaries()
                    .chain(p.implied_guard.iter().flat_map(|g| g.summaries()))
            }))
    }
    fn profile_conditions(&self) -> impl Iterator<Item = &Condition> {
        self.conditional()
            .into_iter()
            .flat_map(|p| {
                std::iter::once(&p.coverage)
                    .chain(p.candidate.profile_conditions())
                    .chain(
                        p.producers
                            .iter()
                            .flat_map(ProducerSummary::profile_conditions),
                    )
                    .chain(p.upper_bounds.iter().flat_map(|b| {
                        b.conditions.values().chain(b.guarantees.values()).chain(
                            b.producers
                                .iter()
                                .flat_map(ProducerSummary::profile_conditions),
                        )
                    }))
            })
            .chain(self.bound_removal().map(|p| &p.body_upper))
            .chain(self.guarded_settlement().into_iter().flat_map(|p| {
                p.implied_guard
                    .iter()
                    .flat_map(|g| g.summaries().flat_map(|s| s.profile_conditions()))
                    .chain(p.certificate.domains())
                    .chain(
                        p.certificate
                            .bounds()
                            .flat_map(|b| b.conditions.values().chain(b.guarantees.values())),
                    )
                    .chain(
                        p.certificate
                            .summaries()
                            .flat_map(ProducerSummary::profile_conditions),
                    )
            }))
    }
    fn nodes(&self) -> usize {
        self.conditional().map_or(0, |p| {
            std::iter::once(&p.candidate)
                .chain(&p.producers)
                .map(ProducerSummary::nodes)
                .sum::<usize>()
                + p.coverage.node_count()
                + p.upper_bounds.as_ref().map_or(0, |b| b.nodes())
        }) + self
            .bound_removal()
            .map_or(0, |p| p.body_upper.node_count())
            + self.guarded_settlement().map_or(0, |p| {
                p.certificate.nodes() + p.implied_guard.as_ref().map_or(0, ImpliedGuardProof::nodes)
            })
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Rewrites {
    pub dropped: BTreeSet<GroundRuleId>,
    originals: BTreeMap<GroundRuleId, GroundRule>,
    proofs: Vec<RewriteProof>,
    // Snapshot-local lookup metadata, never semantic keys or cached query input.
    // Removal proofs occupy no entries; a replay with no discharges misses cheaply.
    discharges: BTreeMap<(GroundRuleId, OccurrenceId), RewriteProofId>,
    replacements: BTreeMap<(GroundRuleId, OccurrenceId), RewriteProofId>,
    pub(crate) skips: BTreeMap<GroundAtom, Vec<AdmissionSkip>>,
    pub(crate) skipped_attempts: usize,
    pub inconclusive: Option<Inconclusive>,
    pub downstream_incomplete: Option<Inconclusive>,
    nodes: usize,
}

impl Rewrites {
    fn push_proof(&mut self, proof: RewriteProof) {
        if let RewriteKind::Discharge { literal_occurrence } = proof.kind {
            // Preserve the linear lookup's first-match behavior.
            self.discharges
                .entry((proof.candidate().id, literal_occurrence))
                .or_insert(proof.id);
        }
        if let RewriteKind::GuardedSettlement { literal_occurrence } = proof.kind {
            self.replacements
                .insert((proof.candidate().id, literal_occurrence), proof.id);
        }
        self.proofs.push(proof);
    }
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
        self.rewrites.push_proof(RewriteProof {
            id,
            snapshot,
            kind: RewriteKind::Discharge {
                literal_occurrence: occurrence,
            },
            justification: RewriteJustification::Symbolic(SymbolicRewriteProof {
                candidate: ProducerSummary {
                    rule: original,
                    settled: vec![],
                    condition,
                    exact: false,
                },
                producers: vec![],
                coverage,
                upper_bounds: None,
            }),
        });
    }

    pub fn prepare_checked(
        corpus: &denotate_ir::Corpus,
        domains: &Domains,
        limits: &Limits,
    ) -> Result<AnalysisOutcome<Self>> {
        AnalysisOutcome::from_result(Self::prepare(corpus, domains, limits))
    }

    pub(crate) fn replacement_proof(
        &self,
        rule: GroundRuleId,
        occurrence: OccurrenceId,
    ) -> Option<&RewriteProof> {
        self.rewrites
            .replacements
            .get(&(rule, occurrence))
            .and_then(|id| self.rewrite_proof(*id))
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
    /// Optional downstream rewrite work exhausted; admission verdicts are intact.
    pub fn downstream_incomplete(&self) -> Option<Inconclusive> {
        self.rewrites.downstream_incomplete
    }
    pub(crate) fn discharge(
        &self,
        rule: GroundRuleId,
        occurrence: OccurrenceId,
    ) -> Option<&RewriteProof> {
        self.rewrites
            .discharges
            .get(&(rule, occurrence))
            .and_then(|id| self.rewrite_proof(*id))
    }

    #[cfg(test)]
    pub(crate) fn discharge_scanning_reference(
        &self,
        rule: GroundRuleId,
        occurrence: OccurrenceId,
    ) -> Option<&RewriteProof> {
        self.rewrite_proofs().find(|p| {
            p.candidate().id == rule
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
        self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
    ) -> Result<Self> {
        self.admit_attempts(budget, observer, Attempts::default(), None, None, None)
    }
    #[cfg(test)]
    pub(crate) fn admit_without_negative_reuse(
        self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
    ) -> Result<Self> {
        self.admit_attempts(
            budget,
            observer,
            Attempts::without_negative_reuse(),
            None,
            None,
            None,
        )
    }
    pub(crate) fn admit_diagnosed(
        self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
        config: Option<CandidateProbeLimits>,
        components: Option<(SatProbeLimits, &SatProbeObserver<'_>)>,
        dump: Option<&AdmissionDumpObserver<'_>>,
    ) -> Result<Self> {
        self.admit_attempts(
            budget,
            observer,
            Attempts::default(),
            config,
            components,
            dump,
        )
    }
    #[cfg(test)]
    pub(crate) fn admit_guarded_for_test(
        self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
        batch: bool,
        reuse: bool,
    ) -> Result<Self> {
        let mut attempts = Attempts::default();
        attempts.batch_guarded = batch;
        attempts.reuse_prepared = reuse;
        self.admit_attempts(budget, observer, attempts, None, None, None)
    }

    fn admit_attempts(
        mut self,
        budget: &mut Budget<'_>,
        observer: Option<&AdmissionObserver<'_>>,
        mut attempts: Attempts,
        probe: Option<CandidateProbeLimits>,
        components: Option<(SatProbeLimits, &SatProbeObserver<'_>)>,
        dump: Option<&AdmissionDumpObserver<'_>>,
    ) -> Result<Self> {
        self.rewrites.skips.clear();
        self.rewrites.skipped_attempts = 0;
        let mut progress = crate::admission_progress::AdmissionReporter::new(observer);
        progress.dump = dump;
        progress.component_probe = components.map(|(config, observer)| {
            crate::sat_probe::admission::Diagnosis::new(config, budget.limits.clone(), observer)
        });
        if let Some(config) = probe {
            progress.enable_candidate_probe(config, budget.limits);
        }
        progress.snapshot(&self, 0, "starting");
        let limits = budget.limits;
        if let Err(error) = limits.cancellation.check() {
            budget.excluding_time(|| {
                self.dump(
                    dump,
                    AdmissionDumpEvent::Graph {
                        state: "interrupted",
                        error: Some(&error),
                    },
                )
            });
            return Err(error);
        }
        self.rewrites.inconclusive = None;
        self.rewrites.downstream_incomplete = None;
        if !self.assumptions_consistent() {
            budget.excluding_time(|| progress.candidate_probe_summary(&self));
            progress.finish(&self, "inconsistent-assumptions");
            budget.excluding_time(|| {
                self.dump(
                    dump,
                    AdmissionDumpEvent::Graph {
                        state: "inconsistent-assumptions",
                        error: None,
                    },
                )
            });
            return Ok(self);
        }
        let mut round = 0;
        let mut phase = AdmissionPhase::Relevant;
        let result = self
            .rewrite_loop(budget, &progress, &mut attempts, phase, &mut round)
            .and_then(|()| {
                progress.round_end(&self);
                // Downstream never attempts guarded replacements. Release the
                // optional preparation pool before its evaluation and proofs.
                attempts.clear_prepared();
                phase = AdmissionPhase::Downstream;
                progress.phase(phase);
                self.rewrite_loop(budget, &progress, &mut attempts, phase, &mut round)
            });
        budget.excluding_time(|| progress.candidate_probe_summary(&self));
        progress.round_end(&self);
        self.rewrites.skipped_attempts = attempts.count;
        self.rewrites.skips = attempts.records();
        budget.excluding_time(|| {
            self.dump(
                dump,
                AdmissionDumpEvent::Graph {
                    state: if result.is_ok() {
                        "complete"
                    } else {
                        "interrupted"
                    },
                    error: result.as_ref().err(),
                },
            )
        });
        if let Err(error) = result {
            progress.failed(&self, &error);
            budget.failure(&error);
            let cause = Inconclusive::from_error(error)?;
            match phase {
                AdmissionPhase::Relevant => self.rewrites.inconclusive = Some(cause),
                AdmissionPhase::Downstream => self.rewrites.downstream_incomplete = Some(cause),
            }
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
        attempts: &mut Attempts,
        phase: AdmissionPhase,
        round: &mut usize,
    ) -> Result<()> {
        let profile = budget.limits.profile.clone();
        loop {
            if self.is_admitted()
                && (phase == AdmissionPhase::Relevant
                    || (self.input_groups.is_empty() && self.assumption_condition.is_none()))
            {
                return Ok(());
            }
            let mut scope = crate::admission_scope::AdmissionScope::build(self, phase, budget)?;
            if scope.targets.is_empty() {
                return Ok(());
            }
            *round += 1;
            let _round_profile = profile.span("admission-round", Some(*round));
            progress.snapshot(self, *round, "structural");
            {
                let _stage = profile.span("admission-structural", Some(*round));
                let structural = crate::structural::reduce_selected(self, Some(&scope), budget)?;
                if !structural.is_empty() {
                    self.commit_structural(structural, attempts, budget)?;
                    progress.snapshot(self, *round, "structural-committed");
                    if self.is_admitted()
                        && (phase == AdmissionPhase::Relevant
                            || (self.input_groups.is_empty()
                                && self.assumption_condition.is_none()))
                    {
                        return Ok(());
                    }
                    scope = crate::admission_scope::AdmissionScope::build(self, phase, budget)?;
                }
            }
            if scope.targets.is_empty() {
                return Ok(());
            }
            progress.snapshot(self, *round, "symbolic");
            budget.tick("rewrite snapshot")?;
            let meaning = {
                let _timer = progress.time("symbolic");
                let mut stage = profile.span("admission-symbolic", Some(*round));
                let observe = |id| progress.work(self, "symbolic", Some(id), 0, false);
                let meaning = self.symbolic_for_admission(
                    budget,
                    progress.enabled().then_some(&observe),
                    &scope.cone,
                )?;
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
            let summaries_timer = progress.time("summaries");
            let mut summaries_profile = profile.span("admission-summaries", Some(*round));
            progress.work(self, "summaries", None, 0, true);
            let mut summaries = BTreeMap::new();
            let mut producers = BTreeMap::<_, Vec<_>>::new();
            let mut has_candidates = false;
            let mut exact_heads = BTreeSet::new();
            let mut retained =
                self.rewrites.nodes + meaning.metrics().retained_condition_nodes + attempts.nodes();
            for (position, rule) in self
                .rules
                .iter()
                .filter(|r| scope.cone.rules.contains(&r.id))
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
                for replacement in &rule.replacements {
                    let value = meaning.settled_expression(&replacement.expression, budget)?;
                    condition = ctx.apply(&condition, &value, and, budget)?;
                }
                retained = crate::symbolic::retain(retained, 0, condition.node_count(), budget)?;
                if !exact && scope.targets.contains(&rule.id) {
                    has_candidates = true;
                }
                if exact {
                    exact_heads.insert(&rule.head.atom);
                }
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
            drop(summaries_timer);
            let mut candidates_profile = profile.span("admission-candidates", Some(*round));
            // A successful component batch commits before any later pass can
            // exhaust. Rebuild the schedule from the next immutable snapshot.
            let components = scope.ordered_targets(self, budget)?;
            let mut batch = Vec::new();
            for pass in ["producer-removals", "bound-removals", "candidates"] {
                if pass == "bound-removals" && phase == AdmissionPhase::Relevant {
                    if let Some(diagnosis) = &progress.component_probe {
                        budget.excluding_time(|| {
                            diagnosis.run(self, *round, &components, &summaries, ctx)
                        })?;
                    }
                }
                for (component, targets) in &components {
                    progress.work(self, pass, Some(*component), 0, true);
                    let head = self
                        .component(*component)
                        .expect("scheduled component")
                        .atoms
                        .first()
                        .expect("component atom");
                    let result = attempts.component_pass(
                        head,
                        self,
                        &mut retained,
                        budget,
                        progress,
                        |attempts, retained, budget| match pass {
                            "producer-removals" => self.producer_removals(
                                &summaries, targets, &producers, ctx, retained, budget, progress,
                                attempts,
                            ),
                            "bound-removals" => self.bound_removals(
                                &summaries,
                                targets,
                                &exact_heads,
                                ctx,
                                retained,
                                budget,
                                progress,
                                attempts,
                            ),
                            _ => self.discharges(
                                &meaning, &summaries, targets, &producers, phase, retained, budget,
                                progress, attempts,
                            ),
                        },
                    )?;
                    if let Some(proofs) = result {
                        batch = proofs;
                    }
                    if !batch.is_empty() {
                        break;
                    }
                }
                if !batch.is_empty() {
                    break;
                }
            }
            // Preserve established discharge proofs before trying the more general
            // guarded replacement. Each successful batch reads a fresh snapshot.
            if batch.is_empty() && phase == AdmissionPhase::Relevant && has_candidates {
                let mut guarded_targets = BTreeSet::new();
                for (component, targets) in &components {
                    let head = self
                        .component(*component)
                        .expect("scheduled component")
                        .atoms
                        .first()
                        .expect("component atom");
                    if !attempts.component_skipped(head) {
                        guarded_targets.extend(targets);
                    }
                }
                let guarded = self.guarded_settlements(
                    &meaning,
                    &summaries,
                    &guarded_targets,
                    &mut retained,
                    budget,
                    progress,
                    attempts,
                )?;
                for proof in guarded {
                    batch.push(RewriteProof {
                        id: RewriteProofId {
                            snapshot: self.graph_revision,
                            index: self.rewrites.proofs.len() + batch.len(),
                        },
                        snapshot: self.graph_revision,
                        kind: RewriteKind::GuardedSettlement {
                            literal_occurrence: proof.occurrence,
                        },
                        justification: RewriteJustification::GuardedSettlement(proof),
                    });
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
            let _commit_profile = profile.span("admission-commit", Some(*round));
            progress.work(self, "commit", None, 0, true);
            self.commit_rewrites(batch, attempts, budget)?;
            progress.snapshot(self, *round, "committed");
        }
    }

    fn commit_structural(
        &mut self,
        structural: Vec<crate::structural::StructuralProof>,
        attempts: &mut Attempts,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let batch = structural
            .into_iter()
            .enumerate()
            .map(|(index, proof)| RewriteProof {
                id: RewriteProofId {
                    snapshot: self.graph_revision,
                    index: self.rewrites.proofs.len() + index,
                },
                snapshot: self.graph_revision,
                kind: RewriteKind::RedundantProducer,
                justification: RewriteJustification::Structural(proof),
            })
            .collect();
        self.commit_rewrites(batch, attempts, budget)
    }

    /// Exercise the structural algorithm independently of admission scheduling.
    #[cfg(test)]
    pub(crate) fn structural_for_test(mut self, limits: &Limits) -> Result<Self> {
        let mut budget = Budget::new(limits);
        let result = crate::structural::reduce(&self, &mut budget).and_then(|proofs| {
            if proofs.is_empty() {
                Ok(())
            } else {
                self.commit_structural(proofs, &mut Attempts::default(), &mut budget)
            }
        });
        if let Err(error) = result {
            self.rewrites.inconclusive = Some(Inconclusive::from_error(error)?);
        }
        Ok(self)
    }

    /// Strengthen bounds only after cheap removals reach a fixed point. Covers
    /// and guarantees are exact and remain in the graph: no proposed deletion
    /// can justify itself, directly or through another deletion in this batch.
    fn bound_removals(
        &self,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        targets: &BTreeSet<GroundRuleId>,
        exact_heads: &BTreeSet<&GroundAtom>,
        ctx: &ConditionContext,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
        attempts: &mut Attempts,
    ) -> Result<Vec<RewriteProof>> {
        let mut candidates = Vec::new();
        let mut last = BTreeMap::new();
        for (position, id) in targets.iter().enumerate() {
            let p = &summaries[id];
            budget.tick("bound removal candidates")?;
            if !targets.contains(&p.rule.id) || p.exact || !exact_heads.contains(&p.rule.head.atom)
            {
                continue;
            }
            let component = self.component_for(&p.rule.head.atom)?;
            if !component.recursive {
                continue;
            }
            candidates.push((position + 1, p, component));
            last.insert(component.id, p.rule.id);
        }
        let mut cache: BTreeMap<_, Option<Arc<ComponentUpperBounds>>> = BTreeMap::new();
        let mut batch = Vec::new();
        for (position, candidate, component) in candidates {
            if attempts.reuse_negative(
                &Attempt::BoundRemoval(candidate.rule.id),
                budget,
                progress,
            )? {
                if last[&component.id] == candidate.rule.id {
                    if let Some(bounds) = cache.remove(&component.id).flatten() {
                        *retained -= bounds.nodes();
                    }
                }
                continue;
            }
            if let std::collections::btree_map::Entry::Vacant(entry) = cache.entry(component.id) {
                progress.work(
                    self,
                    "guaranteed-bounds",
                    Some(component.id),
                    position,
                    true,
                );
                let observe = |iteration| progress.iteration(self, iteration);
                let head = component.atoms.first().expect("component atom");
                entry.insert(attempts.run(
                    Attempt::GuaranteedBounds(head.clone()),
                    head,
                    self,
                    retained,
                    budget,
                    progress,
                    |retained, budget| {
                        crate::upper_bounds::compute_with_guarantees(
                            self,
                            component,
                            summaries,
                            ctx,
                            retained,
                            budget,
                            progress.enabled().then_some(&observe),
                            true,
                        )
                    },
                )?);
            }
            if let Some(bounds) = &cache[&component.id] {
                let coverage = &bounds.guarantees[&candidate.rule.head.atom];
                progress.rule(self, "bound-removals", candidate.rule.id, position);
                let upper = attempts
                    .proof(
                        Attempt::BoundRemoval(candidate.rule.id),
                        &candidate.rule.head.atom,
                        self,
                        retained,
                        budget,
                        progress,
                        Option::is_none,
                        |_, budget| {
                            let mut upper = candidate.condition.clone();
                            for literal in &candidate.rule.body {
                                budget.tick("bound removal body")?;
                                match literal.polarity {
                                    Polarity::Positive => {
                                        if let Some(bound) =
                                            bounds.conditions.get(&literal.term.atom)
                                        {
                                            upper = ctx.apply(&upper, bound, and, budget)?;
                                        }
                                    }
                                    Polarity::Negative => {
                                        if let Some(lower) =
                                            bounds.guarantees.get(&literal.term.atom)
                                        {
                                            upper = ctx.apply(&upper, lower, and_not, budget)?;
                                        }
                                    }
                                }
                            }
                            let uncovered = ctx.apply(&upper, coverage, and_not, budget)?;
                            Ok(ctx
                                .restrict(&uncovered, budget)?
                                .is_false()
                                .then_some(upper))
                        },
                    )?
                    .flatten();
                if let Some(body_upper) = upper {
                    let covering = bounds
                        .producers
                        .iter()
                        .filter(|p| p.exact && p.rule.head.atom == candidate.rule.head.atom)
                        .collect();
                    self.propose(
                        &mut batch,
                        candidate,
                        covering,
                        coverage.clone(),
                        RewriteKind::RedundantProducer,
                        Some(Arc::clone(bounds)),
                        retained,
                        budget,
                    )?;
                    *retained =
                        crate::symbolic::retain(*retained, 0, body_upper.node_count(), budget)?;
                    // Move the newly allocated proof without cloning its metadata.
                    let mut owned = batch.pop().unwrap();
                    let RewriteJustification::Symbolic(proof) = owned.justification else {
                        unreachable!()
                    };
                    owned.justification =
                        RewriteJustification::BoundRemoval(BoundRemovalProof { proof, body_upper });
                    batch.push(owned);
                }
            }
            if last[&component.id] == candidate.rule.id {
                if let Some(bounds) = cache.remove(&component.id).flatten() {
                    *retained -= bounds.nodes();
                }
            }
        }
        debug_assert!(cache.is_empty());
        Ok(batch)
    }

    fn commit_rewrites(
        &mut self,
        batch: Vec<RewriteProof>,
        attempts: &mut Attempts,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        // Transactional graph rebuild: an interrupted batch cannot leave a
        // half-rewritten graph or publish warnings for uncommitted changes.
        budget.charge(
            self.atoms.len()
                + self
                    .rules
                    .iter()
                    .map(|r| 1 + r.body.len() + r.replacements.len())
                    .sum::<usize>(),
            "rewrite commit",
        )?;
        let mut next = self.clone();
        let changed = attempts.changed_readers(self, &batch, budget)?;
        for proof in batch {
            let id = proof.candidate().id;
            next.rewrites
                .originals
                .entry(id)
                .or_insert_with(|| self.rules[id.index].clone());
            match proof.kind {
                RewriteKind::RedundantProducer => {
                    next.rewrites.dropped.insert(id);
                }
                RewriteKind::GuardedSettlement { literal_occurrence } => {
                    let p = proof.guarded_settlement().expect("guarded certificate");
                    next.rules[id.index]
                        .body
                        .retain(|l| l.term.occurrence != literal_occurrence);
                    next.rules[id.index].replacements.push(SettledReplacement {
                        occurrence: literal_occurrence,
                        expression: Arc::clone(&p.replacement),
                    });
                }
                RewriteKind::Discharge { literal_occurrence } => next.rules[id.index]
                    .body
                    .retain(|l| l.term.occurrence != literal_occurrence),
            }
            next.rewrites.nodes += proof.nodes();
            next.rewrites.push_proof(proof);
        }
        crate::graph::analyze(&mut next, budget)?;
        let invalidated = attempts.invalidated(self, &next, &changed, budget)?;
        *self = next;
        attempts.invalidate(&invalidated);
        Ok(())
    }

    pub(crate) fn propose(
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
            justification: RewriteJustification::Symbolic(SymbolicRewriteProof {
                candidate: candidate.clone(),
                producers: producers.into_iter().cloned().collect(),
                coverage,
                upper_bounds,
            }),
        };
        batch.push(proof);
        Ok(())
    }
}

#[cfg(test)]
mod batch_commit_tests {
    use super::*;
    use crate::test_support::rewrites::{atom, summaries};

    #[test]
    fn interrupted_multi_replacement_commit_leaves_graph_and_proofs_untouched() {
        let (c, first, second) = crate::tests::guarded_settlement::independent_readers_fixture();
        let l = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let m = raw.symbolic(&l).unwrap();
        let summaries = summaries(&raw, &m, &l);
        let targets = summaries
            .values()
            .filter(|s| [atom(first), atom(second)].contains(&s.rule.head.atom))
            .map(|s| s.rule.id)
            .collect();
        let proofs = raw
            .guarded_settlements(
                &m,
                &summaries,
                &targets,
                &mut 0,
                &mut Budget::new(&l),
                &crate::admission_progress::AdmissionReporter::new(None),
                &mut Attempts::default(),
            )
            .unwrap();
        assert_eq!(proofs.len(), 2);
        let batch: Vec<_> = proofs
            .into_iter()
            .enumerate()
            .map(|(index, proof)| RewriteProof {
                id: RewriteProofId {
                    snapshot: raw.graph_revision,
                    index,
                },
                snapshot: raw.graph_revision,
                kind: RewriteKind::GuardedSettlement {
                    literal_occurrence: proof.occurrence,
                },
                justification: RewriteJustification::GuardedSettlement(proof),
            })
            .collect();
        let mut rebuilt_failure = false;
        let mut completed = false;
        for allowance in (1..10000).step_by(31) {
            let limited = Limits {
                max_work: allowance,
                ..l.clone()
            };
            let mut p = raw.clone();
            match p.commit_rewrites(
                batch.clone(),
                &mut Attempts::default(),
                &mut Budget::new(&limited),
            ) {
                Ok(()) => {
                    assert_eq!(p.rewrite_proofs().count(), 2);
                    completed = true;
                    break;
                }
                Err(CheckError::LimitExceeded { phase, .. }) => {
                    rebuilt_failure |= phase != "rewrite commit";
                    assert_eq!(
                        p.rules().collect::<Vec<_>>(),
                        raw.rules().collect::<Vec<_>>()
                    );
                    assert_eq!(p.graph_revision, raw.graph_revision);
                    assert_eq!(p.rewrite_proofs().count(), 0);
                }
                Err(e) => panic!("{e:?}"),
            }
        }
        assert!(rebuilt_failure && completed);
    }
}
