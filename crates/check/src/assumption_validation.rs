//! Program-level declaration validation, independent of selected assumptions.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{
    AssumptionCone, AssumptionKey, Corpus, OccurrenceKey, RelationId, RuleKey, SemanticKeys,
};
use std::collections::{BTreeMap, BTreeSet};

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
    limits.cancellation.check()?;
    let mut result = AssumptionValidation::default();
    if corpus.assumptions().next().is_none() {
        return Ok(result);
    }
    let mut budget = Budget::new(limits);
    let validation: Result<()> = (|| {
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
            let ground = GroundProgram::prepare_using(
                corpus,
                domains,
                &[],
                &BTreeSet::new(),
                &mut budget,
                None,
            )?;
            for (relation, names) in pending {
                let cycles = ground.assumption_cycles(relation, keys, &mut budget)?;
                let state = if cycles.is_empty() {
                    AssumptionValidity::Valid
                } else {
                    AssumptionValidity::Invalid { cycles }
                };
                for name in names {
                    result.assumptions.insert(name, state.clone());
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
    Ok(result)
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
            cycles.push(AssumptionCycle(edges));
        }
        Ok(cycles)
    }
}
