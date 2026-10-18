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
pub use input::*;
#[cfg(test)]
mod tests;

impl PreparedCheck<'_> {
    pub fn verify_local(&self, operations: &OperationalLimits) -> Result<LocalCheckOutcome<'_>> {
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
            let input = self.local_input(scope.clone(), &cone)?;
            metrics.keys += start.elapsed();
            metrics.cone_atoms += input.facts.len();
            metrics.cone_inputs += input.inputs.len();
            unique.extend(input.facts.iter().cloned());
            let start = Instant::now();
            let evaluation = self
                .program
                .symbolic_selected(&mut budget, true, Some(&cone));
            let evaluation = evaluation
                .and_then(|m| export_evaluation(m, self.semantic_keys, &self.keys, &mut budget));
            metrics.evaluation += start.elapsed();
            if let Err(e) = &evaluation {
                Inconclusive::from_error(e.clone())?;
                budget.failure(e);
            }
            budget.record(
                &mut receipts,
                QueryKey::ConeEvaluation(key.clone()),
                [QueryKey::ConeIndex],
            )?;
            let mut budget = Budget::tracked(&limits);
            let (meaning, value) = match evaluation {
                Ok(v) => v,
                Err(e) => {
                    let cause = Inconclusive::from_error(e)?;
                    artifacts.insert(
                        scope,
                        LocalArtifact {
                            input,
                            evaluation: None,
                            answer: None,
                        },
                    );
                    budget.record(
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
                        cone,
                        outcome: GroupOutcome::Inconclusive(cause),
                    });
                    continue;
                }
            };
            let property_start = Instant::now();
            let outcome = local_property(&meaning, &cone, group, self.semantic_keys, &mut budget);
            let owned = outcome.and_then(|o| match o {
                GroupOutcome::Overlap(c) => Ok((
                    Some(
                        meaning
                            .context
                            .export(&c, self.semantic_keys, &mut budget)?,
                    ),
                    GroupOutcome::Overlap(c),
                )),
                o => Ok((None, o)),
            });
            metrics.property += property_start.elapsed();
            if let Err(e) = &owned {
                Inconclusive::from_error(e.clone())?;
                budget.failure(e);
            }
            budget.record(
                &mut receipts,
                QueryKey::Property(key.clone()),
                [QueryKey::ConeEvaluation(key.clone())],
            )?;
            let (condition, mut outcome) = match owned {
                Ok(v) => v,
                Err(e) => (
                    None,
                    GroupOutcome::Inconclusive(Inconclusive::from_error(e)?),
                ),
            };
            let answer = LocalAnswer::Group(match &outcome {
                GroupOutcome::Proved => LocalVerdict::Proved,
                GroupOutcome::Overlap(_) => {
                    LocalVerdict::Overlap(condition.as_ref().unwrap().clone())
                }
                GroupOutcome::Unsupported => {
                    LocalVerdict::Unsupported(CapabilityReason::UnsettledDependencies(
                        cone.blocked_by
                            .iter()
                            .map(|id| self.keys.components[id].clone())
                            .collect(),
                    ))
                }
                GroupOutcome::Inconclusive(c) => LocalVerdict::Inconclusive((*c).into()),
            });
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
                        let c = value.conditions.get(&atom);
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
                    evaluation: Some(value),
                    answer: Some(answer),
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
            let start = Instant::now();
            let result = (|| -> Result<(SymbolicMeaning<'_>, LocalEvaluation)> {
                let cone = index.build(component.atoms.iter().cloned(), &mut budget)?;
                let start = Instant::now();
                let input = self.local_input(scope.clone(), &cone)?;
                metrics.keys += start.elapsed();
                metrics.cone_atoms += input.facts.len();
                metrics.cone_inputs += input.inputs.len();
                unique.extend(input.facts.iter().cloned());
                artifacts.insert(
                    scope.clone(),
                    LocalArtifact {
                        input,
                        evaluation: None,
                        answer: None,
                    },
                );
                let meaning = self
                    .program
                    .symbolic_selected(&mut budget, true, Some(&cone))?;
                export_evaluation(meaning, self.semantic_keys, &self.keys, &mut budget)
            })();
            metrics.evaluation += start.elapsed();
            if let Err(e) = &result {
                Inconclusive::from_error(e.clone())?;
                budget.failure(e);
            }
            budget.record(
                &mut receipts,
                QueryKey::RegionEvaluation(key.clone()),
                [QueryKey::ConeIndex],
            )?;
            let mut budget = Budget::tracked(&limits);
            let completion = match result {
                Ok((m, v)) => {
                    artifacts.get_mut(&scope).unwrap().evaluation = Some(v);
                    let start = Instant::now();
                    let completed = m
                        .complete_component(component, 0, &mut budget)
                        .and_then(|c| {
                            let answer = self.own_completion(&c, &m.context, &mut budget)?;
                            artifacts.get_mut(&scope).unwrap().answer = Some(answer);
                            Ok(c)
                        });
                    metrics.completion += start.elapsed();
                    let start = Instant::now();
                    let converted = completed.and_then(|c| {
                        convert_completion(
                            c,
                            &m.context,
                            &presentation.context,
                            self.semantic_keys,
                            &atoms,
                            &self.program,
                            &mut budget,
                        )
                    });
                    metrics.conversion += start.elapsed();
                    converted
                }
                Err(e) => Err(e),
            };
            let completion = match completion {
                Ok(c) => c,
                Err(e) => {
                    budget.failure(&e);
                    CompletionOutcome::Inconclusive(Inconclusive::from_error(e)?)
                }
            };
            budget.record(
                &mut receipts,
                QueryKey::Completion(key),
                [
                    QueryKey::RegionEvaluation(self.keys.components[&component.id].clone()),
                    QueryKey::FindingContext,
                ],
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
        let verification = presentation.verify_report(
            &limits,
            &limits,
            &limits,
            Some(&mut query_run),
            report,
            Some(completions),
        )?;
        let value = self.project(&verification, self.semantic_keys)?;
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
fn export_evaluation<'p>(
    meaning: SymbolicMeaning<'p>,
    keys: &SemanticKeys,
    index: &GroundKeyIndex,
    budget: &mut Budget<'_>,
) -> Result<(SymbolicMeaning<'p>, LocalEvaluation)> {
    let permitted = meaning
        .context
        .export(&meaning.context.permitted_worlds(), keys, budget)?;
    let mut retained = crate::symbolic::retain(
        meaning.metrics().retained_condition_nodes,
        0,
        permitted.node_count(),
        budget,
    )?;
    let conditions = meaning
        .conditions
        .iter()
        .map(|(a, c)| {
            let value = meaning.context.export(c, keys, budget)?;
            retained = crate::symbolic::retain(retained, 0, value.node_count(), budget)?;
            Ok((
                AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?,
                value,
            ))
        })
        .collect::<Result<_>>()?;
    let incomplete = meaning
        .inconclusive
        .iter()
        .map(|(id, c)| (index.components[id].clone(), (*c).into()))
        .collect();
    Ok((
        meaning,
        LocalEvaluation {
            permitted,
            conditions,
            incomplete,
        },
    ))
}
fn local_property(
    meaning: &SymbolicMeaning<'_>,
    cone: &DependencyCone,
    group: &AtMostOneGroup,
    keys: &SemanticKeys,
    budget: &mut Budget<'_>,
) -> Result<GroupOutcome> {
    budget.tick("property checks")?;
    if let Some(c) = cone
        .components
        .iter()
        .find_map(|id| meaning.inconclusive.get(id))
    {
        return Ok(GroupOutcome::Inconclusive(*c));
    }
    if !cone.blocked_by.is_empty() {
        return Ok(meaning
            .program
            .admission_limit()
            .map_or(GroupOutcome::Unsupported, GroupOutcome::Inconclusive));
    }
    let tuples = group
        .tuples
        .iter()
        .map(|a| Ok((AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?, a)))
        .collect::<Result<BTreeMap<_, _>>>()?;
    let tuples = tuples.into_values().collect::<Vec<_>>();
    let ctx = &meaning.context;
    let mut violation = ctx.false_condition();
    for (i, left) in tuples.iter().enumerate() {
        for right in &tuples[i + 1..] {
            budget.tick("property checks")?;
            let pair = ctx.apply(
                &meaning.known(left),
                &meaning.known(right),
                biodivine_lib_bdd::op_function::and,
                budget,
            )?;
            violation = ctx.apply(
                &violation,
                &pair,
                biodivine_lib_bdd::op_function::or,
                budget,
            )?;
        }
    }
    let violation = ctx.restrict(&violation, budget)?;
    if violation.is_false() {
        Ok(GroupOutcome::Proved)
    } else {
        crate::symbolic::retain(0, 0, violation.node_count(), budget)?;
        Ok(GroupOutcome::Overlap(violation))
    }
}
fn convert_completion(
    mut c: CompletionOutcome,
    from: &ConditionContext,
    to: &ConditionContext,
    keys: &SemanticKeys,
    atoms: &BTreeMap<AtomKey, GroundAtom>,
    program: &GroundProgram,
    budget: &mut Budget<'_>,
) -> Result<CompletionOutcome> {
    if let CompletionOutcome::NoMeaning(f) = &mut c {
        f.bad_input = to.import(&from.export(&f.bad_input, keys, budget)?, atoms, budget)?;
        for b in f.upstream.values_mut() {
            b.condition = to.import(&from.export(&b.condition, keys, budget)?, atoms, budget)?;
        }
        budget.charge(program.inputs.len(), "local witness extension")?;
        f.observation.absent = program
            .inputs
            .difference(&f.observation.present)
            .cloned()
            .collect();
        program.validate_input_world(&f.observation.present, budget)?;
    }
    Ok(c)
}
