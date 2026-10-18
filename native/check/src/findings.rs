use crate::{
    limits::{Budget, Result},
    *,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayScope {
    WholeProgram,
    ConeOnly,
}

/// A finite grounded proof DAG. Positive premises name earlier steps; negative
/// premises only reference a completed provider and its confirmed absence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GroundEvidence {
    Input,
    Derived {
        rule: GroundRule,
        premises: Vec<PremiseEvidence>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceStep {
    pub order: usize,
    pub evidence: GroundEvidence,
}
#[derive(Debug)]
pub struct Counterexample {
    pub observation: Observation,
    pub replay_scope: ReplayScope,
    /// Every distinct group tuple true in the selected observation, not duplicate
    /// derivations of one tuple. At least two, confirmed by concrete replay.
    pub tuples: BTreeSet<GroundAtom>,
    pub evidence: BTreeMap<GroundAtom, EvidenceStep>,
    /// None when the original globally admitted program already replayed fully.
    pub certification: Option<CertificationOutcome>,
    /// Proven implications from this group's full violation condition to a
    /// region's no-meaning condition, not inferences from failed certification.
    pub confined_to_no_meaning: Vec<ComponentId>,
}
#[derive(Debug)]
pub enum VerifiedOutcome {
    Proved,
    Counterexample(Counterexample),
    Unsupported,
    Inconclusive(Inconclusive),
}
#[derive(Debug)]
pub struct VerifiedGroup {
    pub group: AtMostOneGroup,
    pub cone: DependencyCone,
    pub outcome: VerifiedOutcome,
}

/// One reported closed cycle, with every ground rule and premise on that path.
/// This does not purport to enumerate every cycle in the component.
#[derive(Debug)]
pub struct UnresolvedRegion {
    pub component: ComponentId,
    pub cycle: Cycle,
    pub rules: Vec<GroundRule>,
    pub outcome: RegionOutcome,
    /// Separate from admission: a solution does not admit this region.
    pub completion: CompletionOutcome,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionOutcome {
    Unsupported,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Default)]
pub struct FindingMetrics {
    pub witness: Duration,
    pub replay: Duration,
    pub evidence: Duration,
    pub completion: Duration,
    pub certification: Duration,
}
#[derive(Debug)]
pub struct Verification<'p> {
    program: &'p GroundProgram,
    pub groups: Vec<VerifiedGroup>,
    pub unresolved: Vec<UnresolvedRegion>,
    pub property_metrics: SymbolicMetrics,
    pub finding_metrics: FindingMetrics,
    pub incomplete_evaluation: BTreeMap<ComponentId, Inconclusive>,
}
impl Verification<'_> {
    pub fn program(&self) -> &GroundProgram {
        self.program
    }
    pub fn whole_program_admitted(&self) -> bool {
        self.program.is_admitted()
    }
    /// Includes trivially discharged groups (zero/one possible tuple). A blocked
    /// program is never a global pass, even if its independent groups are proved.
    pub fn all_obligations_proved(&self) -> bool {
        self.whole_program_admitted()
            && self.incomplete_evaluation.is_empty()
            && self
                .groups
                .iter()
                .all(|g| matches!(g.outcome, VerifiedOutcome::Proved))
    }
}

impl<'p> SymbolicMeaning<'p> {
    /// Converts budget exhaustion before a report exists to a top-level outcome.
    pub fn verify_checked(&self, limits: &Limits) -> Result<AnalysisOutcome<Verification<'p>>> {
        AnalysisOutcome::from_result(self.verify_at_most_one(limits))
    }
    /// Synchronous findings. Limits become explicit inconclusive groups; a
    /// replay mismatch is an internal failure, never a reported counterexample.
    pub fn verify_at_most_one(&self, limits: &Limits) -> Result<Verification<'p>> {
        self.verify_with_completion_limits(limits, limits)
    }

    /// Completion has its own budget and runs after overlap checks/replay, so
    /// an expensive broken region cannot consume their allowance.
    pub fn verify_with_completion_limits(
        &self,
        limits: &Limits,
        completion_limits: &Limits,
    ) -> Result<Verification<'p>> {
        self.verify_with_phase_limits(limits, completion_limits, limits)
    }

    /// Independent allowances for required findings and the optional replay
    /// upgrade. Each phase shares its budget across groups/components in order.
    pub fn verify_with_phase_limits(
        &self,
        limits: &Limits,
        completion_limits: &Limits,
        certification_limits: &Limits,
    ) -> Result<Verification<'p>> {
        self.verify_queries(limits, completion_limits, certification_limits, None)
    }
    pub(crate) fn verify_queries(
        &self,
        limits: &Limits,
        completion_limits: &Limits,
        certification_limits: &Limits,
        mut queries: Option<&mut QueryRun<'_>>,
    ) -> Result<Verification<'p>> {
        limits.cancellation.check()?;
        let report = self.check_queries(limits, queries.as_deref_mut())?;
        self.verify_report(
            limits,
            completion_limits,
            certification_limits,
            queries,
            report,
            None,
        )
    }
    pub(crate) fn verify_report(
        &self,
        limits: &Limits,
        completion_limits: &Limits,
        certification_limits: &Limits,
        mut queries: Option<&mut QueryRun<'_>>,
        report: PropertyReport,
        mut local_completions: Option<BTreeMap<ComponentId, CompletionOutcome>>,
    ) -> Result<Verification<'p>> {
        let mut budget = Budget::new(limits);
        let mut metrics = FindingMetrics::default();
        let mut groups = Vec::new();
        let mut violations = Vec::new();
        for check in report.groups {
            if queries.is_some() {
                budget = Budget::tracked(limits);
            }
            violations.push(match &check.outcome {
                GroupOutcome::Overlap(c) => Some(c.clone()),
                _ => None,
            });
            let result = (|| -> Result<VerifiedOutcome> {
                let outcome = match check.outcome {
                    GroupOutcome::Proved => VerifiedOutcome::Proved,
                    GroupOutcome::Unsupported => VerifiedOutcome::Unsupported,
                    GroupOutcome::Inconclusive(cause) => VerifiedOutcome::Inconclusive(cause),
                    GroupOutcome::Overlap(condition) => {
                        let start = Instant::now();
                        let observation = self
                            .context
                            .witness_with_budget(&condition, &mut budget)?
                            .ok_or(CheckError::Internal("overlap has no witness"))?;
                        metrics.witness += start.elapsed();
                        let start = Instant::now();
                        let selected =
                            (!self.program.is_admitted()).then_some(&check.cone.components);
                        let replay = self.program.evaluate_selected(
                            observation.present.iter().cloned(),
                            selected,
                            &mut budget,
                        )?;
                        let replay_scope = if replay.is_complete() {
                            ReplayScope::WholeProgram
                        } else {
                            ReplayScope::ConeOnly
                        };
                        let mut tuples = BTreeSet::new();
                        for tuple in &check.group.tuples {
                            budget.tick("replay confirmation")?;
                            match replay.fact(tuple)? {
                                FactState::Settled(true) => {
                                    tuples.insert(tuple.clone());
                                }
                                FactState::Settled(false) => {}
                                FactState::Blocked(_) => {
                                    return Err(CheckError::Internal("overlap replay is blocked"));
                                }
                            }
                        }
                        if tuples.len() < 2 {
                            return Err(CheckError::Internal("symbolic overlap did not replay"));
                        }
                        metrics.replay += start.elapsed();
                        let start = Instant::now();
                        let evidence = collect_evidence(&replay, &tuples, &mut budget)?;
                        metrics.evidence += start.elapsed();
                        VerifiedOutcome::Counterexample(Counterexample {
                            observation,
                            replay_scope,
                            tuples,
                            evidence,
                            certification: None,
                            confined_to_no_meaning: vec![],
                        })
                    }
                };
                Ok(outcome)
            })();
            let outcome = match result {
                Ok(value) => value,
                Err(error) => {
                    budget.failure(&error);
                    VerifiedOutcome::Inconclusive(Inconclusive::from_error(error)?)
                }
            };
            if let Some(q) = queries.as_mut() {
                let key = q.group(&check.group)?;
                budget.record(
                    q.receipts,
                    QueryKey::Witness(key.clone()),
                    [if local_completions.is_some() {
                        QueryKey::FindingConversion(key)
                    } else {
                        QueryKey::Property(key)
                    }],
                )?;
            }
            groups.push(VerifiedGroup {
                group: check.group,
                cone: check.cone,
                outcome,
            });
        }
        let mut unresolved = Vec::new();
        let completion_start = Instant::now();
        completion_limits.cancellation.check()?;
        let mut completion_budget = Budget::new(completion_limits);
        let mut completion_nodes = 0;
        // Copy already bounded, prepared cycle metadata even if witness work
        // exhausted its budget. Otherwise a limit would hide the blocked regions.
        let mut ordered: Vec<_> = report.unresolved_components.into_iter().collect();
        if let Some(q) = queries.as_ref() {
            let keyed = ordered
                .into_iter()
                .map(|id| Ok((q.component(id)?, id)))
                .collect::<Result<BTreeMap<_, _>>>()?;
            ordered = keyed.into_values().collect();
        }
        #[cfg(any(test, feature = "test-support"))]
        if queries.is_some() {
            crate::accounting::test_schedule(&mut ordered);
        }
        for id in ordered {
            if queries.is_some() {
                completion_budget = Budget::tracked(completion_limits);
                completion_nodes = 0;
            }
            let component = self
                .program
                .component(id)
                .ok_or(CheckError::Internal("missing component"))?;
            let cycle = component
                .cycle
                .as_ref()
                .ok_or(CheckError::Internal("missing cycle"))?;
            let mut rules = Vec::new();
            let mut seen = BTreeSet::new();
            for edge in &cycle.edges {
                if seen.insert(edge.rule) {
                    let rule = self
                        .program
                        .rule(edge.rule)
                        .ok_or(CheckError::Internal("missing cycle rule"))?;
                    rules.push(rule.clone());
                }
            }
            let completion_result = if let Some(local) = local_completions.as_mut() {
                local
                    .remove(&id)
                    .ok_or(CheckError::Internal("missing local completion"))
            } else {
                self.complete_component(component, completion_nodes, &mut completion_budget)
            };
            let completion = match completion_result {
                Ok(outcome) => outcome,
                Err(error) => {
                    completion_budget.failure(&error);
                    CompletionOutcome::Inconclusive(Inconclusive::from_error(error)?)
                }
            };
            if let CompletionOutcome::NoMeaning(finding) = &completion {
                completion_nodes += finding.bad_input.node_count();
            }
            if let Some(q) = queries.as_mut().filter(|_| local_completions.is_none()) {
                completion_budget.record(
                    q.receipts,
                    QueryKey::Completion(q.component(id)?),
                    [QueryKey::Symbolic],
                )?;
            }
            unresolved.push(UnresolvedRegion {
                component: id,
                cycle: cycle.clone(),
                rules,
                completion,
                outcome: self
                    .program
                    .admission_limit()
                    .map_or(RegionOutcome::Unsupported, RegionOutcome::Inconclusive),
            });
        }
        if let Some(q) = queries.as_ref() {
            // Completion tasks may arrive in any order. A certification query's
            // dependency traversal remains canonical, including on exhaustion.
            let keyed = unresolved
                .into_iter()
                .map(|r| Ok((q.component(r.component)?, r)))
                .collect::<Result<BTreeMap<_, _>>>()?;
            unresolved = keyed.into_values().collect();
        }
        metrics.completion = completion_start.elapsed();
        let certification_start = Instant::now();
        certification_limits.cancellation.check()?;
        let mut certification_budget = Budget::new(certification_limits);
        for (group, condition) in groups.iter_mut().zip(violations) {
            if queries.is_some() {
                certification_budget = Budget::tracked(certification_limits);
            }
            let needs_completion = matches!(&group.outcome, VerifiedOutcome::Counterexample(c) if c.replay_scope == ReplayScope::ConeOnly);
            if let (VerifiedOutcome::Counterexample(example), Some(condition)) =
                (&mut group.outcome, condition)
            {
                if example.replay_scope == ReplayScope::ConeOnly {
                    self.certify_counterexample(
                        example,
                        &group.group,
                        &condition,
                        &mut certification_budget,
                    )?;
                    if example.replay_scope == ReplayScope::ConeOnly {
                        for region in &unresolved {
                            let CompletionOutcome::NoMeaning(finding) = &region.completion else {
                                continue;
                            };
                            // Require a permitted observation outside the failure
                            // region; otherwise every conflict implies it vacuously.
                            let outside = self.context.apply(
                                &self.context.permitted_worlds(),
                                &finding.bad_input,
                                biodivine_lib_bdd::op_function::and_not,
                                &mut certification_budget,
                            );
                            match outside {
                                Ok(outside) if outside.is_false() => continue,
                                Ok(_) => {}
                                Err(error @ CheckError::LimitExceeded { .. }) => {
                                    certification_budget.failure(&error);
                                    break;
                                }
                                Err(error) => return Err(error),
                            }
                            match self.context.apply(
                                &condition,
                                &finding.bad_input,
                                biodivine_lib_bdd::op_function::and_not,
                                &mut certification_budget,
                            ) {
                                Ok(outside) if outside.is_false() => {
                                    example.confined_to_no_meaning.push(region.component)
                                }
                                Ok(_) => {}
                                Err(error @ CheckError::LimitExceeded { .. }) => {
                                    certification_budget.failure(&error);
                                    break;
                                } // Optional wording only.
                                Err(error) => return Err(error),
                            }
                        }
                    }
                }
            }
            if let Some(q) = queries.as_mut() {
                let key = q.group(&group.group)?;
                let mut dependencies = BTreeSet::from([QueryKey::Witness(key.clone())]);
                if needs_completion {
                    for region in &unresolved {
                        dependencies.insert(QueryKey::Completion(q.component(region.component)?));
                    }
                }
                certification_budget.record(
                    q.receipts,
                    QueryKey::Certification(key),
                    dependencies,
                )?;
            }
        }
        metrics.certification = certification_start.elapsed();
        limits.cancellation.check()?;
        completion_limits.cancellation.check()?;
        certification_limits.cancellation.check()?;
        if queries.is_some() {
            let order: BTreeMap<_, _> = self
                .program
                .at_most_one_groups()
                .enumerate()
                .map(|(i, g)| ((g.obligation, g.key.clone()), i))
                .collect();
            groups.sort_by_key(|g| order[&(g.group.obligation, g.group.key.clone())]);
            unresolved.sort_by_key(|r| r.component);
        }
        Ok(Verification {
            program: self.program,
            groups,
            unresolved,
            property_metrics: report.metrics,
            finding_metrics: metrics,
            incomplete_evaluation: self.inconclusive.clone(),
        })
    }
}

pub(crate) fn collect_evidence(
    replay: &Replay<'_>,
    roots: &BTreeSet<GroundAtom>,
    budget: &mut Budget<'_>,
) -> Result<BTreeMap<GroundAtom, EvidenceStep>> {
    let mut result = BTreeMap::new();
    let mut pending: Vec<_> = roots.iter().cloned().collect();
    while let Some(fact) = pending.pop() {
        budget.tick("evidence")?;
        if result.contains_key(&fact) {
            continue;
        }
        let derivation = replay
            .derivation(&fact)
            .ok_or(CheckError::Internal("missing positive evidence"))?;
        let evidence = match &derivation.evidence {
            Evidence::Input => GroundEvidence::Input,
            Evidence::Derived { rule, premises } => {
                let rule = replay
                    .program()
                    .original_rule(*rule)
                    .ok_or(CheckError::Internal("missing evidence rule"))?;
                for premise in premises {
                    budget.tick("evidence")?;
                    match premise {
                        PremiseEvidence::Discharged {
                            literal_occurrence,
                            proof,
                        } => {
                            replay.validate_discharge(
                                rule.id,
                                *literal_occurrence,
                                *proof,
                                budget,
                            )?;
                        }
                        PremiseEvidence::Positive { fact, .. } => {
                            let support = replay
                                .derivation(fact)
                                .ok_or(CheckError::Internal("missing support"))?;
                            if support.order >= derivation.order {
                                return Err(CheckError::Internal("ungrounded evidence"));
                            }
                            pending.push(fact.clone());
                        }
                        PremiseEvidence::Absent { fact, provider, .. } => {
                            if replay.absence_provider(fact)?.as_ref() != Some(provider) {
                                return Err(CheckError::Internal("absence did not replay"));
                            }
                        }
                    }
                }
                GroundEvidence::Derived {
                    rule: rule.clone(),
                    premises: premises.clone(),
                }
            }
        };
        result.insert(
            fact,
            EvidenceStep {
                order: derivation.order,
                evidence,
            },
        );
    }
    Ok(result)
}
