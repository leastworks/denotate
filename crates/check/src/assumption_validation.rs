//! Run-level declaration validation. Selection controls which cones are checked;
//! no assumption's truth is used to validate another assumption.
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
    /// Ground validation is deferred until a run selects this declaration.
    NotSelected,
    Invalid {
        cycles: Vec<AssumptionCycle>,
    },
    Inconclusive(ResourceReason),
}
impl AssumptionValidity {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Valid => "valid",
            Self::NotSelected => "not-selected",
            Self::Invalid { .. } => "invalid",
            Self::Inconclusive(_) => "inconclusive",
        }
    }
}

/// Fresh for one program snapshot and run selection. No assumption activates a
/// constraint here. Unselected ground cones remain explicitly unvalidated.
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
    /// Deferred unselected declarations do not make the run incomplete.
    pub fn has_failures(&self) -> bool {
        self.assumptions.values().any(|v| {
            matches!(
                v,
                AssumptionValidity::Invalid { .. } | AssumptionValidity::Inconclusive(_)
            )
        })
    }
    pub fn selected_failure<'a>(
        &'a self,
        corpus: &Corpus,
        keys: &SemanticKeys,
        request: &CheckRequest,
    ) -> Result<Option<&'a AssumptionValidity>> {
        let mut unknown = None;
        let selected = request.assumption_keys(corpus, keys)?;
        for assumption in corpus.assumptions() {
            let key = keys.assumption(assumption.id)?;
            if !selected.contains(key) {
                continue;
            }
            let state = self.assumptions.get(key).ok_or(CheckError::InvalidRequest(
                "assumption validation does not cover program",
            ))?;
            match state {
                AssumptionValidity::Invalid { .. } => return Ok(Some(state)),
                AssumptionValidity::Inconclusive(_) => unknown = Some(state),
                AssumptionValidity::Valid => {}
                AssumptionValidity::NotSelected => {
                    return Err(CheckError::InvalidRequest(
                        "selected assumption was not covered by run validation",
                    ));
                }
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
/// It retains the shared fold and residual preparation. The ordinary
/// result remains available for diagnostics, including unselected assumptions.
pub struct ValidatedAssumptions<'a> {
    pub(crate) corpus: &'a Corpus,
    pub(crate) keys: &'a SemanticKeys,
    pub(crate) domains: Domains,
    pub(crate) limits: DeterministicLimits,
    pub(crate) fixed: Option<FixedPreparation<'a>>,
    result: AssumptionValidation,
}
impl ValidatedAssumptions<'_> {
    pub fn result(&self) -> &AssumptionValidation {
        &self.result
    }
}

/// Program validation whose fixed truth and residual view can be shared with folded
/// requests through `FixedPreparation::prepare_with_validation`.
pub fn validate_assumption_cones_for_run<'a>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    limits: &Limits,
) -> Result<ValidatedAssumptions<'a>> {
    validate_assumption_cones_using(corpus, domains, keys, limits, || {
        FixedPreparation::prepare(corpus, domains, limits)
    })
}

/// Supply the run's fold factory (for example a session-backed fold). It is called
/// only when declaration classification needs grounding, including with no
/// verifications. No fixed or residual preparation is repeated by later requests.
pub fn validate_assumption_cones_using<'a>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    limits: &Limits,
    prepare: impl FnOnce() -> Result<FixedPreparation<'a>>,
) -> Result<ValidatedAssumptions<'a>> {
    validate_assumption_selection_using(corpus, domains, keys, None, limits, prepare)
}

/// Validate the union of named assumptions selected by the executed requests.
/// Classify every declaration, but invoke the fold factory only if a selected
/// cone needs grounding. An empty request list performs no ground validation.
pub fn validate_selected_assumption_cones_using<'a, 'r>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    requests: impl IntoIterator<Item = &'r CheckRequest>,
    limits: &Limits,
    prepare: impl FnOnce() -> Result<FixedPreparation<'a>>,
) -> Result<ValidatedAssumptions<'a>> {
    limits.cancellation.check()?;
    let mut selected = BTreeSet::new();
    for request in requests {
        limits.cancellation.check()?;
        selected.extend(request.assumption_keys(corpus, keys)?);
    }
    validate_assumption_selection_using(corpus, domains, keys, Some(&selected), limits, prepare)
}

fn validate_assumption_selection_using<'a>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    selected: Option<&BTreeSet<AssumptionKey>>,
    limits: &Limits,
    prepare: impl FnOnce() -> Result<FixedPreparation<'a>>,
) -> Result<ValidatedAssumptions<'a>> {
    limits.cancellation.check()?;
    let mut result = AssumptionValidation::default();
    let mut fixed = None;
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
                AssumptionCone::NeedsGrounding if selected.is_some_and(|s| !s.contains(&key)) => {
                    result
                        .assumptions
                        .insert(key, AssumptionValidity::NotSelected);
                }
                AssumptionCone::NeedsGrounding => pending.entry(relation).or_default().push(key),
            }
        }
        if !pending.is_empty() {
            let prepared = prepare()?;
            prepared.validate_snapshot(corpus, domains, &mut budget)?;
            fixed = Some(prepared);
            let checked = fixed
                .as_ref()
                .unwrap()
                .assumption_preparation(keys, limits)?;
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
            CheckError::Deadline { details, .. } => {
                // No partially prepared artifact survives operational interruption.
                fixed = None;
                ("deadline", details)
            }
            other => return Err(other),
        };
        for assumption in corpus.assumptions() {
            let key = keys.assumption(assumption.id)?.clone();
            result.assumptions.entry(key.clone()).or_insert_with(|| {
                if selected.is_some_and(|s| !s.contains(&key)) {
                    AssumptionValidity::NotSelected
                } else {
                    AssumptionValidity::Inconclusive(ResourceReason {
                        phase: "assumption validation".into(),
                        resource: resource.into(),
                        details,
                    })
                }
            });
        }
    }
    Ok(ValidatedAssumptions {
        corpus,
        keys,
        domains: domains.clone(),
        limits: limits.into(),
        fixed,
        result,
    })
}

/// One assumption-independent residual preparation answers every relation,
/// including later unnamed restrictions. Original instances remain available to
/// admission; validation, W and the SAT engine read the propagated view.
#[derive(Debug)]
struct AssumptionCones {
    base: GroundProgram,
    settled: std::sync::Arc<crate::settled::SettledView>,
    blocked: BTreeMap<RelationId, BTreeSet<ComponentId>>,
    cycles: BTreeMap<ComponentId, AssumptionCycle>,
}
#[derive(Debug)]
pub(crate) struct AssumptionPreparation {
    outcome: AnalysisOutcome<AssumptionCones>,
    pub receipt: WorkReceipt,
    pub settled_receipt: Option<WorkReceipt>,
    pub residual_receipt: Option<WorkReceipt>,
}
impl AssumptionPreparation {
    pub fn prepare(
        fixed: &FixedPreparation<'_>,
        keys: &SemanticKeys,
        limits: &Limits,
    ) -> Result<Self> {
        let mut budget = Budget::tracked(limits);
        let mut settled_receipt = None;
        let mut residual_receipt = None;
        let result = (|| {
            let base = {
                let _profile = limits.profile.span("residual-preparation", None);
                let mut grounding = Budget::tracked(limits);
                let result = GroundProgram::prepare_using_fixed(
                    fixed.corpus,
                    &fixed.domains,
                    &[],
                    &BTreeSet::new(),
                    &mut grounding,
                    None,
                    Some(fixed),
                )
                .and_then(|p| p.with_atom_key_order(keys));
                if let Err(e) = &result {
                    grounding.failure(e);
                }
                residual_receipt = Some(WorkReceipt {
                    allowance: limits.into(),
                    own: grounding.snapshot(),
                    dependencies: BTreeSet::from([QueryKey::FixedFacts]),
                });
                result?
            };
            let ground = {
                let _profile = limits.profile.span("assumption-specialization", None);
                let (result, receipt) = base.settle_atoms_accounted(limits);
                settled_receipt = Some(receipt);
                std::sync::Arc::new(result?)
            };
            let mut blocked = BTreeMap::<_, BTreeSet<_>>::new();
            let mut cycles = BTreeMap::new();
            for atom in &ground.program.atoms {
                budget.tick("assumption validation")?;
                for root in &ground.program.component_for(atom)?.blocked_by {
                    budget.tick("assumption validation")?;
                    blocked.entry(atom.relation).or_default().insert(*root);
                    if let std::collections::btree_map::Entry::Vacant(entry) = cycles.entry(*root) {
                        entry.insert(ground.program.assumption_cycle(*root, keys, &mut budget)?);
                    }
                }
            }
            budget.check("assumption validation")?;
            Ok(AssumptionCones {
                base,
                settled: ground,
                blocked,
                cycles,
            })
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
                dependencies: BTreeSet::from([if settled_receipt.is_some() {
                    QueryKey::SettledAtoms
                } else {
                    QueryKey::ResidualPreparation
                }]),
            },
            settled_receipt,
            residual_receipt,
        })
    }
    pub(crate) fn programs(&self) -> Option<(&GroundProgram, &GroundProgram)> {
        match &self.outcome {
            AnalysisOutcome::Complete(index) => Some((&index.base, &index.settled.program)),
            AnalysisOutcome::Inconclusive(_) => None,
        }
    }
    pub(crate) fn settled(&self) -> Option<&std::sync::Arc<crate::settled::SettledView>> {
        match &self.outcome {
            AnalysisOutcome::Complete(index) => Some(&index.settled),
            _ => None,
        }
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
            AssumptionValidity::Inconclusive(_) | AssumptionValidity::NotSelected => unreachable!(),
        }
    }
}

impl GroundProgram {
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
