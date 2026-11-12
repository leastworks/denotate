//! Owned completion rebinding and logical continuation of a memoized query.
use super::*;

impl PreparedCheck<'_> {
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
        let component_id = |key: &ComponentKey| self.key_view().bind_component(key);
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
                let bind = |key: &AtomKey| self.key_view().bind_atom(key);
                let owned_bad = bad_input
                    .as_ref()
                    .ok_or(CheckError::Internal("missing completion condition"))?;
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
                    .filter(|p| component.atoms.contains(&p.candidate().head.atom))
                    .map(|p| p.id)
                    .collect::<Vec<_>>();
                // Reject stale/missing evidence instead of guessing current sources.
                let current_instances = rules
                    .iter()
                    .map(|r| self.key_view().instance(r.id))
                    .collect::<Result<BTreeSet<_>>>()?;
                let current_rewrites = rewrites
                    .iter()
                    .map(|id| self.key_view().rewrite(*id))
                    .collect::<Result<BTreeSet<_>>>()?;
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
