//! Fresh dependency-closed queries. Snapshot IDs never escape in retained values.
use crate::{
    contracts::ConeIndex,
    limits::{Budget, Result},
    *,
};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

mod input;
mod memo;
mod owned;
pub use input::*;
pub use owned::{answer_owned_local, evaluate_owned_local};
#[cfg(test)]
mod tests;

impl PreparedCheck<'_> {
    pub fn verify_local(&self, operations: &OperationalLimits) -> Result<LocalCheckOutcome<'_>> {
        self.verify_local_with(operations, &mut NoLocalMemo)
    }
    pub fn verify_local_with(
        &self,
        operations: &OperationalLimits,
        cache: &mut dyn LocalMemoStore,
    ) -> Result<LocalCheckOutcome<'_>> {
        operations.cancellation.check()?;
        validate_local_constraints(&self.request.constraints)?;
        let limits = self.request.limits.with_operations(operations);
        let mut receipts = self.receipts.clone();
        let dependency = if receipts.get(&QueryKey::Admission).is_some() {
            QueryKey::Admission
        } else {
            QueryKey::Preparation
        };
        let mut budget = Budget::tracked(&limits);
        let index = ConeIndex::new(&self.program, &mut budget);
        if let Err(e) = &index {
            Inconclusive::from_error(e.clone())?;
            budget.failure(e);
        }
        budget.record(&mut receipts, QueryKey::ConeIndex, [dependency.clone()])?;
        let index = match index {
            Ok(i) => i,
            Err(e) => {
                return Ok(LocalCheckOutcome::Inconclusive {
                    reason: Inconclusive::from_error(e)?,
                    receipts,
                });
            }
        };
        // This fresh global context serves replay/certification and current presentation.
        // It never evaluates program rules, and is charged separately from local solving.
        let mut budget = Budget::tracked(&limits);
        let context_start = Instant::now();
        let context = ConditionContext::build(&self.program, &mut budget);
        let context_time = context_start.elapsed();
        if let Err(e) = &context {
            Inconclusive::from_error(e.clone())?;
            budget.failure(e);
        }
        budget.record(&mut receipts, QueryKey::FindingContext, [dependency])?;
        let context = match context {
            Ok(c) => c,
            Err(e) => {
                return Ok(LocalCheckOutcome::Inconclusive {
                    reason: Inconclusive::from_error(e)?,
                    receipts,
                });
            }
        };
        let mut presentation = SymbolicMeaning {
            program: &self.program,
            context,
            conditions: BTreeMap::new(),
            inconclusive: BTreeMap::new(),
            metrics: SymbolicMetrics {
                elapsed: Duration::ZERO,
                work: 0,
                retained_condition_nodes: 0,
            },
        };
        let atoms: BTreeMap<_, _> = self
            .keys
            .atoms
            .iter()
            .map(|(a, k)| (k.clone(), a.clone()))
            .collect();
        let mut artifacts = BTreeMap::new();
        let mut metrics = LocalMetrics {
            finding_context: context_time,
            ..LocalMetrics::default()
        };
        let mut unique = BTreeSet::new();
        let mut groups = Vec::new();
        let mut completions = BTreeMap::new();
        let ordered = self
            .program
            .at_most_one_groups()
            .map(|g| Ok((GroupKey::from_group(self.semantic_keys, g)?, g)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        for (key, group) in ordered {
            let scope = LocalScope::Group(key.clone());
            let mut budget = Budget::tracked(&limits);
            let cone = index.build(group.tuples.iter().cloned(), &mut budget);
            if let Err(e) = &cone {
                Inconclusive::from_error(e.clone())?;
                budget.failure(e);
            }
            // Cone discovery belongs to evaluation, whose allowance is query-local.
            let cone = match cone {
                Ok(c) => c,
                Err(e) => {
                    budget.record(
                        &mut receipts,
                        QueryKey::ConeEvaluation(key.clone()),
                        [QueryKey::ConeIndex],
                    )?;
                    let mut b = Budget::tracked(&limits);
                    let cause = Inconclusive::from_error(e)?;
                    b.failure(&CheckError::LimitExceeded {
                        phase: cause.phase,
                        resource: cause.resource,
                    });
                    b.record(
                        &mut receipts,
                        QueryKey::Property(key.clone()),
                        [QueryKey::ConeEvaluation(key.clone())],
                    )?;
                    Budget::tracked(&limits).record(
                        &mut receipts,
                        QueryKey::FindingConversion(key.clone()),
                        [QueryKey::Property(key), QueryKey::FindingContext],
                    )?;
                    groups.push(GroupCheck {
                        group: group.clone(),
                        cone: empty_cone(group.tuples.iter().cloned()),
                        outcome: GroupOutcome::Inconclusive(cause),
                    });
                    continue;
                }
            };
            let start = Instant::now();
            let input = self.local_input(scope.clone(), &cone, &presentation.context)?;
            metrics.keys += start.elapsed();
            metrics.cone_atoms += input.facts.len();
            metrics.cone_inputs += input.inputs.len();
            unique.extend(input.facts.iter().cloned());
            operations.cancellation.check()?;
            budget.record(
                &mut receipts,
                QueryKey::ConeDiscovery(key.clone()),
                [QueryKey::ConeIndex],
            )?;
            let memo = cache.execute(&input, operations, &mut metrics)?;
            receipts
                .record(
                    QueryKey::ConeEvaluation(key.clone()),
                    memo.evaluation_receipt.clone(),
                )
                .map_err(CheckError::Receipts)?;
            receipts
                .record(QueryKey::Property(key.clone()), memo.answer_receipt.clone())
                .map_err(CheckError::Receipts)?;
            let value = memo.evaluation.as_ref();
            let answer = memo.answer.as_ref();
            let condition = match answer {
                Some(LocalAnswer::Group(LocalVerdict::Overlap(c))) => Some(c),
                _ => None,
            };
            let mut outcome = match answer {
                Some(LocalAnswer::Group(LocalVerdict::Proved)) => GroupOutcome::Proved,
                Some(LocalAnswer::Group(LocalVerdict::Unsupported(_))) => GroupOutcome::Unsupported,
                Some(LocalAnswer::Group(LocalVerdict::Overlap(_))) => GroupOutcome::Proved, // replaced by current-context import below
                _ => GroupOutcome::Inconclusive(
                    memo.failure
                        .ok_or(CheckError::Internal("missing local failure"))?,
                ),
            };
            let start = Instant::now();
            let mut budget = Budget::tracked(&limits);
            let converted = (|| -> Result<()> {
                if let Some(c) = condition {
                    let mut retained = crate::symbolic::retain(0, 0, c.node_count(), &mut budget)?;
                    outcome = GroupOutcome::Overlap(presentation.context.import(
                        &c,
                        &atoms,
                        &mut budget,
                    )?);
                    for tuple in &group.tuples {
                        let atom = AtomKey::from_atom(self.semantic_keys, tuple)
                            .map_err(CheckError::Keys)?;
                        let c = value
                            .ok_or(CheckError::Internal("missing local evaluation"))?
                            .conditions
                            .get(&atom);
                        let c = match c {
                            Some(c) => presentation.context.import(c, &atoms, &mut budget)?,
                            None => presentation.context.false_condition(),
                        };
                        retained =
                            crate::symbolic::retain(retained, 0, c.node_count(), &mut budget)?;
                        presentation.conditions.insert(tuple.clone(), c);
                    }
                }
                Ok(())
            })();
            if let Err(e) = converted {
                budget.failure(&e);
                outcome = GroupOutcome::Inconclusive(Inconclusive::from_error(e)?);
            }
            budget.record(
                &mut receipts,
                QueryKey::FindingConversion(key.clone()),
                [QueryKey::Property(key), QueryKey::FindingContext],
            )?;
            metrics.conversion += start.elapsed();
            artifacts.insert(
                scope,
                LocalArtifact {
                    input,
                    evaluation: value.cloned(),
                    answer: answer.cloned(),
                },
            );
            groups.push(GroupCheck {
                group: group.clone(),
                cone,
                outcome,
            });
        }
        let regions = self
            .program
            .components()
            .filter(|c| c.cycle.is_some())
            .map(|c| (self.keys.components[&c.id].clone(), c))
            .collect::<BTreeMap<_, _>>();
        for (key, component) in regions {
            let scope = LocalScope::Region(key.clone());
            let mut budget = Budget::tracked(&limits);
            let cone = index.build(component.atoms.iter().cloned(), &mut budget);
            let memo = match cone {
                Ok(cone) => {
                    let start = Instant::now();
                    let input = self.local_input(scope.clone(), &cone, &presentation.context)?;
                    metrics.keys += start.elapsed();
                    metrics.cone_atoms += input.facts.len();
                    metrics.cone_inputs += input.inputs.len();
                    unique.extend(input.facts.iter().cloned());
                    budget.record(
                        &mut receipts,
                        QueryKey::RegionDiscovery(key.clone()),
                        [QueryKey::ConeIndex],
                    )?;
                    let memo = cache.execute(&input, operations, &mut metrics)?;
                    artifacts.insert(
                        scope,
                        LocalArtifact {
                            input,
                            evaluation: memo.evaluation.clone(),
                            answer: memo.answer.clone(),
                        },
                    );
                    memo
                }
                Err(e) => {
                    let failure = Inconclusive::from_error(e.clone())?;
                    budget.failure(&e);
                    let mut local_receipts = WorkReceipts::default();
                    budget.record(
                        &mut local_receipts,
                        QueryKey::RegionEvaluation(key.clone()),
                        [QueryKey::ConeIndex],
                    )?;
                    let mut b = Budget::tracked(&limits);
                    b.failure(&e);
                    b.record(
                        &mut local_receipts,
                        QueryKey::Completion(key.clone()),
                        [
                            QueryKey::RegionEvaluation(key.clone()),
                            QueryKey::FindingContext,
                        ],
                    )?;
                    std::sync::Arc::new(LocalMemo {
                        evaluation: None,
                        answer: None,
                        failure: Some(failure),
                        evaluation_receipt: local_receipts
                            .get(&QueryKey::RegionEvaluation(key.clone()))
                            .unwrap()
                            .clone(),
                        answer_receipt: local_receipts
                            .get(&QueryKey::Completion(key.clone()))
                            .unwrap()
                            .clone(),
                    })
                }
            };
            receipts
                .record(
                    QueryKey::RegionEvaluation(key.clone()),
                    memo.evaluation_receipt.clone(),
                )
                .map_err(CheckError::Receipts)?;
            let mut budget = Budget::resume(&limits, memo.answer_receipt.own.clone());
            let start = Instant::now();
            let completion = self.restore_completion(
                component,
                &memo,
                &presentation.context,
                &atoms,
                &mut budget,
            );
            metrics.conversion += start.elapsed();
            let completion = match completion {
                Ok(c) => c,
                Err(e) => {
                    budget.failure(&e);
                    CompletionOutcome::Inconclusive(Inconclusive::from_error(e)?)
                }
            };
            budget.record(
                &mut receipts,
                QueryKey::Completion(key.clone()),
                [QueryKey::RegionEvaluation(key), QueryKey::FindingContext],
            )?;
            completions.insert(component.id, completion);
        }
        metrics.unique_atoms = unique.len();
        let report = PropertyReport {
            whole_program_admitted: self.program.is_admitted(),
            unresolved_components: completions.keys().copied().collect(),
            groups,
            metrics: SymbolicMetrics {
                elapsed: metrics.property,
                work: receipts
                    .entries()
                    .filter(|(k, _)| matches!(k, QueryKey::Property(_)))
                    .try_fold(0usize, |n, (_, r)| {
                        n.checked_add(r.own.work)
                            .ok_or(CheckError::Receipts(ReceiptError::Overflow))
                    })?,
                retained_condition_nodes: 0,
            },
        };
        let mut query_run = QueryRun {
            keys: self.semantic_keys,
            ground: &self.keys,
            receipts: &mut receipts,
        };
        let mut verification = presentation.verify_report(
            &limits,
            &limits,
            &limits,
            Some(&mut query_run),
            report,
            Some(completions),
        )?;
        if !self.program.coverage.is_empty() {
            let mut coverage_budget = Budget::tracked(&limits);
            let meaning = self.program.symbolic_impl(&mut coverage_budget, true);
            if let Err(e) = &meaning {
                coverage_budget.failure(e);
            }
            coverage_budget.record(
                &mut receipts,
                QueryKey::CoverageMeaning,
                [QueryKey::FindingContext],
            )?;
            match meaning {
                Ok(meaning) => {
                    let mut queries = QueryRun {
                        keys: self.semantic_keys,
                        ground: &self.keys,
                        receipts: &mut receipts,
                    };
                    verification.coverage = meaning.check_coverage(&limits, Some(&mut queries))?;
                }
                Err(e) => {
                    let reason = Inconclusive::from_error(e)?;
                    for id in self.program.coverage.keys() {
                        verification.coverage.insert(
                            *id,
                            CoverageReport {
                                inconclusive: Some(reason),
                                ..CoverageReport::default()
                            },
                        );
                    }
                }
            }
        }
        let mut value = self.project(&verification, self.semantic_keys)?;
        for (scope, artifact) in &artifacts {
            if let (
                LocalScope::Group(key),
                Some(LocalAnswer::Group(LocalVerdict::Unsupported(reason))),
            ) = (scope, &artifact.answer)
            {
                if let Some(result) = value.groups.get_mut(key) {
                    *result = ScopedResult::Unsupported(reason.clone());
                }
            }
        }
        receipts.total().map_err(CheckError::Receipts)?;
        operations.cancellation.check()?;
        Ok(LocalCheckOutcome::Complete(LocalCheckedReport {
            checked: CheckedReport {
                verification,
                results: Accounted { value, receipts },
            },
            queries: artifacts,
            metrics,
        }))
    }
}
fn empty_cone(roots: impl IntoIterator<Item = GroundAtom>) -> DependencyCone {
    DependencyCone {
        roots: roots.into_iter().collect(),
        facts: BTreeSet::new(),
        rules: BTreeSet::new(),
        components: BTreeSet::new(),
        blocked_by: BTreeSet::new(),
    }
}
fn timed_export(
    context: &ConditionContext,
    condition: &Condition,
    keys: &SemanticKeys,
    budget: &mut Budget<'_>,
    elapsed: &mut Duration,
) -> Result<OwnedCondition> {
    let start = Instant::now();
    let value = context.export(condition, keys, budget);
    *elapsed += start.elapsed();
    value
}
