//! Program-level declaration validation, independent of selected assumptions.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{
    AssumptionCone, AssumptionKey, Corpus, OccurrenceKey, RelationId, RuleKey, SemanticKeys,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// A retained ground cycle, with keys that can be rebound to current provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssumptionCycle(pub Vec<AssumptionCycleEdge>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssumptionCycleEdge {
    pub consumer: AtomKey,
    pub provider: AtomKey,
    pub rule: RuleKey,
    pub premise: OccurrenceKey,
    pub negative: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssumptionValidity {
    Valid,
    Invalid { cycles: Vec<AssumptionCycle> },
    Inconclusive(ResourceReason),
}
impl AssumptionValidity {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Valid => "valid",
            Self::Invalid { .. } => "invalid",
            Self::Inconclusive(_) => "inconclusive",
        }
    }
}

/// Fresh for one complete program snapshot. No assumption activates a constraint
/// here, and no verification is needed to validate a declaration.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AssumptionValidation {
    pub assumptions: BTreeMap<AssumptionKey, AssumptionValidity>,
}
impl AssumptionValidation {
    pub fn is_valid(&self) -> bool {
        self.assumptions
            .values()
            .all(|v| matches!(v, AssumptionValidity::Valid))
    }
    pub fn selected_failure<'a>(
        &'a self,
        corpus: &Corpus,
        keys: &SemanticKeys,
        request: &CheckRequest,
    ) -> Result<Option<&'a AssumptionValidity>> {
        let mut unknown = None;
        for assumption in corpus.assumptions() {
            let relation = keys.relation(assumption.restriction.relation())?;
            if !request.constraints.iter().any(|c| c.relation() == relation) {
                continue;
            }
            let state = self
                .assumptions
                .get(keys.assumption(assumption.id)?)
                .ok_or(CheckError::InvalidRequest(
                    "assumption validation does not cover program",
                ))?;
            match state {
                AssumptionValidity::Invalid { .. } => return Ok(Some(state)),
                AssumptionValidity::Inconclusive(_) => unknown = Some(state),
                AssumptionValidity::Valid => {}
            }
        }
        Ok(unknown)
    }
}

/// Validate all declared assumptions once, before iterating verifications. This
/// deliberately recomputes; no result can survive a facts/domains/eligibility edit.
pub fn validate_assumption_cones(
    corpus: &Corpus,
    domains: &Domains,
    keys: &SemanticKeys,
    limits: &Limits,
) -> Result<AssumptionValidation> {
    Ok(validate_assumption_cones_for_run(corpus, domains, keys, limits)?.result)
}

/// Sealed evidence for this snapshot, not a caller-editable validity assertion.
/// It retains cycle summaries, never the original ground program. The ordinary
/// result remains available for diagnostics, including unselected assumptions.
pub struct ValidatedAssumptions<'a> {
    pub(crate) corpus: &'a Corpus,
    pub(crate) keys: &'a SemanticKeys,
    pub(crate) domains: Domains,
    pub(crate) limits: DeterministicLimits,
    pub(crate) original: Option<Arc<OriginalAssumptionValidation>>,
    result: AssumptionValidation,
}
impl ValidatedAssumptions<'_> {
    pub fn result(&self) -> &AssumptionValidation {
        &self.result
    }
}

/// Program validation whose original-graph evidence can be shared with folded
/// requests through `FixedPreparation::prepare_with_validation`.
pub fn validate_assumption_cones_for_run<'a>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    limits: &Limits,
) -> Result<ValidatedAssumptions<'a>> {
    limits.cancellation.check()?;
    let mut result = AssumptionValidation::default();
    let mut original = None;
    let mut budget = Budget::new(limits);
    let validation: Result<()> = (|| {
        if corpus.assumptions().next().is_none() {
            return Ok(());
        }
        let classified =
            corpus.validate_assumptions_with(|| budget.tick("assumption validation"))?;
        let mut pending = BTreeMap::<RelationId, Vec<AssumptionKey>>::new();
        for assumption in corpus.assumptions() {
            budget.tick("assumption validation")?;
            let key = keys.assumption(assumption.id)?.clone();
            let relation = assumption.restriction.relation();
            match classified[&relation] {
                AssumptionCone::RelationStratified => {
                    result.assumptions.insert(key, AssumptionValidity::Valid);
                }
                AssumptionCone::NeedsGrounding => pending.entry(relation).or_default().push(key),
            }
        }
        if !pending.is_empty() {
            let checked = Arc::new(OriginalAssumptionValidation::prepare(
                corpus, domains, keys, limits,
            )?);
            original = Some(checked.clone());
            for (relation, names) in pending {
                for name in names {
                    result
                        .assumptions
                        .insert(name, checked.validity(relation, &mut budget)?);
                }
            }
        }
        Ok(())
    })();
    if let Err(error) = validation {
        let (resource, details) = match error.in_phase("assumption validation", None) {
            CheckError::LimitExceeded {
                resource, details, ..
            } => (resource, details),
            CheckError::Deadline { details, .. } => ("deadline", details),
            other => return Err(other),
        };
        for assumption in corpus.assumptions() {
            result
                .assumptions
                .entry(keys.assumption(assumption.id)?.clone())
                .or_insert(AssumptionValidity::Inconclusive(ResourceReason {
                    phase: "assumption validation".into(),
                    resource: resource.into(),
                    details,
                }));
        }
    }
    Ok(ValidatedAssumptions {
        corpus,
        keys,
        domains: domains.clone(),
        limits: limits.into(),
        original,
        result,
    })
}

/// A single original grounding answers every relation, including restrictions
/// supplied by unnamed API requests. Root cycles are stored once; relations refer
/// to them. Unrelated cycles do not invalidate a relation's cone.
#[derive(Debug)]
struct OriginalCones {
    blocked: BTreeMap<RelationId, BTreeSet<ComponentId>>,
    cycles: BTreeMap<ComponentId, AssumptionCycle>,
}
#[derive(Debug)]
pub(crate) struct OriginalAssumptionValidation {
    outcome: AnalysisOutcome<OriginalCones>,
    pub receipt: WorkReceipt,
}
impl OriginalAssumptionValidation {
    pub fn prepare(
        corpus: &Corpus,
        domains: &Domains,
        keys: &SemanticKeys,
        limits: &Limits,
    ) -> Result<Self> {
        let mut budget = Budget::tracked(limits);
        let result = (|| {
            let ground = GroundProgram::prepare_using(
                corpus,
                domains,
                &[],
                &BTreeSet::new(),
                &mut budget,
                None,
            )?;
            let mut blocked = BTreeMap::<_, BTreeSet<_>>::new();
            let mut cycles = BTreeMap::new();
            for atom in &ground.atoms {
                budget.tick("assumption validation")?;
                for root in &ground.component_for(atom)?.blocked_by {
                    budget.tick("assumption validation")?;
                    blocked.entry(atom.relation).or_default().insert(*root);
                    if let std::collections::btree_map::Entry::Vacant(entry) = cycles.entry(*root) {
                        entry.insert(ground.assumption_cycle(*root, keys, &mut budget)?);
                    }
                }
            }
            Ok(OriginalCones { blocked, cycles })
        })()
        .map_err(|e: CheckError| e.in_phase("assumption validation", None));
        if let Err(error) = &result {
            budget.failure(error);
        }
        // Operational failures are not reusable results. Logical exhaustion is
        // explicit and shared only within this run, under the same limits.
        let outcome = AnalysisOutcome::from_result(result)?;
        Ok(Self {
            outcome,
            receipt: WorkReceipt {
                allowance: limits.into(),
                own: budget.snapshot(),
                dependencies: BTreeSet::new(),
            },
        })
    }
    fn validity(
        &self,
        relation: RelationId,
        budget: &mut Budget<'_>,
    ) -> Result<AssumptionValidity> {
        budget.tick("assumption validation")?;
        Ok(match &self.outcome {
            AnalysisOutcome::Inconclusive(reason) => {
                AssumptionValidity::Inconclusive(ResourceReason {
                    phase: reason.phase.into(),
                    resource: reason.resource.into(),
                    details: reason.details,
                })
            }
            AnalysisOutcome::Complete(index) => {
                let cycles = index
                    .blocked
                    .get(&relation)
                    .into_iter()
                    .flatten()
                    .map(|id| {
                        let cycle = &index.cycles[id];
                        // The shared index owns one cycle. Every declaration or
                        // request emitting a copy still pays for its evidence.
                        for edge in &cycle.0 {
                            budget.charge(
                                1 + edge.consumer.arguments.len() + edge.provider.arguments.len(),
                                "assumption validation evidence",
                            )?;
                        }
                        Ok(cycle.clone())
                    })
                    .collect::<Result<Vec<_>>>()?;
                if cycles.is_empty() {
                    AssumptionValidity::Valid
                } else {
                    AssumptionValidity::Invalid { cycles }
                }
            }
        })
    }
    pub fn check(
        &self,
        relation: RelationId,
        keys: &SemanticKeys,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        if let AnalysisOutcome::Inconclusive(reason) = &self.outcome {
            return Err((*reason).into());
        }
        match self.validity(relation, budget)? {
            AssumptionValidity::Invalid { cycles } => Err(CheckError::InvalidAssumptionCone {
                relation: keys.relation(relation)?.clone(),
                cycles,
            }),
            AssumptionValidity::Valid => Ok(()),
            AssumptionValidity::Inconclusive(_) => unreachable!(),
        }
    }
}

impl GroundProgram {
    /// Called only on the unrevised graph. `blocked_by` already contains exactly
    /// the negative SCCs reachable from each atom; no new graph analysis is needed.
    pub(crate) fn assumption_cycles(
        &self,
        relation: RelationId,
        keys: &SemanticKeys,
        budget: &mut Budget<'_>,
    ) -> Result<Vec<AssumptionCycle>> {
        let mut blocked = BTreeSet::new();
        for atom in &self.atoms {
            budget.tick("assumption validation")?;
            if atom.relation == relation {
                for component in &self.component_for(atom)?.blocked_by {
                    budget.tick("assumption validation")?;
                    blocked.insert(*component);
                }
            }
        }
        let mut cycles = Vec::new();
        for component in blocked {
            cycles.push(self.assumption_cycle(component, keys, budget)?);
        }
        Ok(cycles)
    }
    fn assumption_cycle(
        &self,
        component: ComponentId,
        keys: &SemanticKeys,
        budget: &mut Budget<'_>,
    ) -> Result<AssumptionCycle> {
        let cycle = self.components[component.index]
            .cycle
            .as_ref()
            .ok_or(CheckError::Internal("assumption blocker has no cycle"))?;
        let mut edges = Vec::new();
        for edge in &cycle.edges {
            budget.tick("assumption validation")?;
            edges.push(AssumptionCycleEdge {
                consumer: AtomKey::from_atom(keys, &edge.consumer)?,
                provider: AtomKey::from_atom(keys, &edge.provider)?,
                rule: keys
                    .rule(
                        self.rule(edge.rule)
                            .ok_or(CheckError::Internal("missing cycle rule"))?
                            .source,
                    )?
                    .clone(),
                premise: keys.bindings().key(edge.premise)?.clone(),
                negative: edge.polarity == Polarity::Negative,
            });
        }
        Ok(AssumptionCycle(edges))
    }
}
