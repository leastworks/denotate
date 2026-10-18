//! Owned completion rebinding and logical continuation of a memoized query.
use super::*;

impl PreparedCheck<'_> {
    pub(super) fn compute_local_region(
        &self,
        cone: &DependencyCone,
        component: &Component,
        key: &ComponentKey,
        mut budget: Budget<'_>,
        limits: &Limits,
        metrics: &mut LocalMetrics,
    ) -> Result<(LocalMemo, Option<(ConditionContext, CompletionOutcome)>)> {
        let mut receipts = WorkReceipts::default();
        let start = Instant::now();
        let evaluation = self
            .program
            .symbolic_selected(&mut budget, true, Some(cone));
        metrics.evaluation += start.elapsed();
        let start = Instant::now();
        let evaluation = evaluation
            .and_then(|m| export_evaluation(m, self.semantic_keys, &self.keys, &mut budget));
        metrics.export += start.elapsed();
        if let Err(e) = &evaluation {
            Inconclusive::from_error(e.clone())?;
            budget.failure(e);
        }
        budget.record(
            &mut receipts,
            QueryKey::RegionEvaluation(key.clone()),
            [QueryKey::ConeIndex],
        )?;
        let mut budget = Budget::tracked(limits);
        let mut value = None;
        let mut failure = None;
        let mut raw = None;
        let answer = match evaluation {
            Ok((meaning, v)) => {
                value = Some(v);
                let start = Instant::now();
                let completed = meaning.complete_component(component, 0, &mut budget);
                metrics.completion += start.elapsed();
                let start = Instant::now();
                let exports_before = metrics.export;
                let answer = completed.and_then(|c| {
                    if let CompletionOutcome::Inconclusive(c) = &c {
                        failure = Some(*c);
                    }
                    let owned = self.own_completion(
                        &c,
                        &meaning.context,
                        &mut budget,
                        &mut metrics.export,
                    )?;
                    raw = Some((meaning.context, c));
                    Ok(owned)
                });
                metrics.completion += start
                    .elapsed()
                    .saturating_sub(metrics.export - exports_before);
                answer
            }
            Err(e) => Err(e),
        };
        let answer = match answer {
            Ok(a) => Some(a),
            Err(e) => {
                budget.failure(&e);
                failure = Some(Inconclusive::from_error(e)?);
                None
            }
        };
        budget.record(
            &mut receipts,
            QueryKey::Completion(key.clone()),
            [
                QueryKey::RegionEvaluation(key.clone()),
                QueryKey::FindingContext,
            ],
        )?;
        Ok((
            LocalMemo {
                // Completion can exhaust during ordered upstream replay after
                // evaluation has finished. Keep its full work order in the key.
                reorder_safe: false,
                evaluation: value,
                answer,
                failure,
                evaluation_receipt: receipts
                    .get(&QueryKey::RegionEvaluation(key.clone()))
                    .unwrap()
                    .clone(),
                answer_receipt: receipts
                    .get(&QueryKey::Completion(key.clone()))
                    .unwrap()
                    .clone(),
            },
            raw,
        ))
    }

    pub(super) fn restore_completion(
        &self,
        component: &Component,
        memo: &LocalMemo,
        context: &ConditionContext,
        atoms: &BTreeMap<AtomKey, GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<CompletionOutcome> {
        let Some(LocalAnswer::Completion {
            outcome,
            bad_input,
            boundary,
        }) = &memo.answer
        else {
            return Ok(CompletionOutcome::Inconclusive(memo.failure.ok_or(
                CheckError::Internal("missing cached completion failure"),
            )?));
        };
        let component_id = |key: &ComponentKey| {
            self.keys
                .components
                .iter()
                .find_map(|(id, k)| (k == key).then_some(*id))
                .ok_or(CheckError::Internal("missing current completion component"))
        };
        match outcome {
            RegionCompletion::NoContradiction => Ok(CompletionOutcome::NoContradiction),
            RegionCompletion::Inconclusive(_) => Ok(CompletionOutcome::Inconclusive(
                memo.failure
                    .ok_or(CheckError::Internal("missing completion resource reason"))?,
            )),
            RegionCompletion::Deferred(keys) => Ok(CompletionOutcome::Deferred {
                blocked_by: keys.iter().map(component_id).collect::<Result<_>>()?,
            }),
            RegionCompletion::NoMeaning {
                candidate,
                evidence,
            } => {
                let bind = |key: &AtomKey| {
                    atoms
                        .get(key)
                        .cloned()
                        .ok_or(CheckError::Internal("missing current completion atom"))
                };
                let owned_bad = bad_input
                    .as_ref()
                    .ok_or(CheckError::Internal("missing completion condition"))?;
                replay_export(owned_bad, budget)?;
                let bad_input = context.import(owned_bad, atoms, budget)?;
                let present = candidate
                    .present
                    .iter()
                    .map(bind)
                    .collect::<Result<BTreeSet<_>>>()?;
                // Historical conversion visits upstream premises in current arena order.
                let ordered = boundary
                    .iter()
                    .map(|(k, c)| Ok((bind(k)?, c)))
                    .collect::<Result<BTreeMap<_, _>>>()?;
                let mut upstream = BTreeMap::new();
                for (atom, c) in ordered {
                    replay_export(c, budget)?;
                    let condition = context.import(c, atoms, budget)?;
                    let provider = if !self.program.is_possible(&atom)? {
                        CompletedProvider::NoPossibleProducer
                    } else if self.program.inputs.contains(&atom) {
                        CompletedProvider::InputSnapshot
                    } else {
                        CompletedProvider::Component(self.program.component_for(&atom)?.id)
                    };
                    let value_in_witness = c.value_in(&candidate.present)?;
                    upstream.insert(
                        atom,
                        CompletionBoundary {
                            condition,
                            value_in_witness,
                            provider,
                        },
                    );
                }
                budget.charge(self.program.inputs.len(), "local witness extension")?;
                let absent = self.program.inputs.difference(&present).cloned().collect();
                self.program.validate_input_world(&present, budget)?;
                let rules = self.program.component_rules[component.id.index]
                    .iter()
                    .map(|i| self.program.rules[*i].clone())
                    .collect::<Vec<_>>();
                let rewrites = self
                    .program
                    .rewrite_proofs()
                    .filter(|p| component.atoms.contains(&p.candidate.rule.head.atom))
                    .map(|p| p.id)
                    .collect::<Vec<_>>();
                // Reject stale/missing evidence instead of guessing current sources.
                let current_instances = rules
                    .iter()
                    .map(|r| self.keys.instances[&r.id].clone())
                    .collect::<BTreeSet<_>>();
                let current_rewrites = rewrites
                    .iter()
                    .map(|id| self.keys.rewrites[id].clone())
                    .collect::<BTreeSet<_>>();
                if current_instances != evidence.instances || current_rewrites != evidence.rewrites
                {
                    return Err(CheckError::Internal(
                        "cached completion evidence does not bind",
                    ));
                }
                Ok(CompletionOutcome::NoMeaning(Box::new(NoMeaning {
                    component: component.id,
                    bad_input,
                    observation: Observation { present, absent },
                    rules,
                    upstream,
                    rewrites,
                })))
            }
        }
    }
}

/// Conversion historically exported these same local BDDs a second time.
/// Replay their logical charges while reusing the canonical owned graphs. One
/// initial visit plus three visits per nonterminal exactly matches export's DFS,
/// including already-seen children. Individual ticks preserve tight-limit reasons.
fn replay_export(c: &OwnedCondition, budget: &mut Budget<'_>) -> Result<()> {
    budget.tick("BDD operation")?;
    let nodes = c.source_node_count();
    budget.observe("BDD operation", "BDD nodes", nodes);
    if nodes > budget.limits.max_bdd_nodes {
        return Err(crate::boolean::limit("BDD operation", "BDD nodes"));
    }
    budget.charge(c.inputs().len(), "local condition export")?;
    for _ in 0..c.export_visits() {
        budget.tick("local condition export")?;
    }
    Ok(())
}
