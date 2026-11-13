//! Backend-neutral request/result boundary with deterministic per-query receipts.
use crate::*;
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

use crate::limits::Budget;

type Result<T> = std::result::Result<T, CheckError>;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeterministicLimits {
    pub max_atoms: usize,
    pub max_rules: usize,
    pub max_dependencies: usize,
    pub max_work: usize,
    pub max_bdd_variables: usize,
    pub max_bdd_nodes: usize,
    pub max_bdd_tasks: usize,
    pub max_condition_nodes: usize,
}
impl From<&Limits> for DeterministicLimits {
    fn from(l: &Limits) -> Self {
        Self {
            max_atoms: l.max_atoms,
            max_rules: l.max_rules,
            max_dependencies: l.max_dependencies,
            max_work: l.max_work,
            max_bdd_variables: l.max_bdd_variables,
            max_bdd_nodes: l.max_bdd_nodes,
            max_bdd_tasks: l.max_bdd_tasks,
            max_condition_nodes: l.max_condition_nodes,
        }
    }
}
#[derive(Debug, Clone)]
pub struct OperationalLimits {
    pub profile: Profile,
    pub progress: CheckingProgress,
    pub cancellation: Cancellation,
    pub timeout: Duration,
}
impl From<&Limits> for OperationalLimits {
    fn from(l: &Limits) -> Self {
        Self {
            cancellation: l.cancellation.clone(),
            profile: l.profile.clone(),
            progress: l.progress.clone(),
            timeout: l.timeout,
        }
    }
}
impl DeterministicLimits {
    pub fn with_operations(&self, o: &OperationalLimits) -> Limits {
        Limits {
            cancellation: o.cancellation.clone(),
            profile: o.profile.clone(),
            progress: o.progress.clone(),
            timeout: o.timeout,
            max_atoms: self.max_atoms,
            max_rules: self.max_rules,
            max_dependencies: self.max_dependencies,
            max_work: self.max_work,
            max_bdd_variables: self.max_bdd_variables,
            max_bdd_nodes: self.max_bdd_nodes,
            max_bdd_tasks: self.max_bdd_tasks,
            max_condition_nodes: self.max_condition_nodes,
        }
    }
}
/// Fixed BDD algorithm identity for request/result validation, not a selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendIdentity {
    pub backend: String,
    pub configuration: String,
}
impl BackendIdentity {
    pub fn bdd() -> Self {
        Self {
            backend: "bdd".into(),
            configuration: "atom-key-order-v1/per-query-budgets-v1".into(),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RequestScope {
    WholeProgram,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputConstraint {
    AtMostOne {
        relation: RelationKey,
        group_by: Vec<usize>,
    },
    Cardinality {
        kind: Cardinality,
        relation: RelationKey,
        group_by: Vec<usize>,
    },
}
impl InputConstraint {
    pub fn relation(&self) -> &RelationKey {
        match self {
            Self::AtMostOne { relation, .. } | Self::Cardinality { relation, .. } => relation,
        }
    }
    pub fn group_by(&self) -> &[usize] {
        match self {
            Self::AtMostOne { group_by, .. } | Self::Cardinality { group_by, .. } => group_by,
        }
    }
    pub fn kind(&self) -> Cardinality {
        match self {
            Self::AtMostOne { .. } => Cardinality::AtMostOne,
            Self::Cardinality { kind, .. } => *kind,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckRequest {
    pub verification: Option<VerificationKey>,
    pub constraints: Vec<InputConstraint>,
    pub obligations: BTreeSet<ObligationKey>,
    pub notices: BTreeSet<NoticeKey>,
    pub scope: RequestScope,
    pub domains: BTreeMap<SortKey, Vec<ConstantKey>>,
    pub backend: BackendIdentity,
    pub limits: DeterministicLimits,
}
impl CheckRequest {
    pub fn for_verification(
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        verification: VerificationId,
        limits: &Limits,
    ) -> Result<Self> {
        let mut request = Self::all_obligations(corpus, keys, domains, &[], limits)?;
        let (constraints, obligations) = verification_selection(corpus, keys, verification)?;
        request.verification = Some(
            keys.verification(verification)
                .map_err(CheckError::Keys)?
                .clone(),
        );
        request.constraints = constraints;
        request.obligations = obligations;
        request.notices = corpus
            .verification(verification)
            .unwrap()
            .notices
            .iter()
            .map(|id| keys.notice(*id).cloned().map_err(CheckError::Keys))
            .collect::<Result<_>>()?;
        Ok(request)
    }

    pub fn all_obligations(
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        limits: &Limits,
    ) -> Result<Self> {
        keys.validate(corpus).map_err(CheckError::Keys)?;
        let mut keyed_domains = BTreeMap::new();
        for (s, values) in domains {
            let mut values = values
                .iter()
                .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                .collect::<Result<Vec<_>>>()?;
            values.sort(); // Preserve duplicates so validation still rejects them.
            keyed_domains.insert(keys.sort(*s).map_err(CheckError::Keys)?.clone(), values);
        }
        Ok(Self {
            verification: None,
            constraints: constraints
                .iter()
                .map(|c| {
                    Ok(InputConstraint::AtMostOne {
                        relation: keys.relation(c.relation).map_err(CheckError::Keys)?.clone(),
                        group_by: c.group_by.clone(),
                    })
                })
                .collect::<Result<_>>()?,
            obligations: corpus
                .obligations()
                .map(|o| keys.obligation(o.id).cloned().map_err(CheckError::Keys))
                .collect::<Result<_>>()?,
            notices: BTreeSet::new(),
            scope: RequestScope::WholeProgram,
            domains: keyed_domains,
            backend: BackendIdentity::bdd(),
            limits: limits.into(),
        })
    }
    pub fn prepare<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
    ) -> Result<RequestPreparation<'s>> {
        self.prepare_using(corpus, keys, operations, None, None, None)
    }
    pub fn prepare_with_plans<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        plans: &mut dyn JoinPlanStore,
    ) -> Result<RequestPreparation<'s>> {
        self.prepare_using(corpus, keys, operations, Some(plans), None, None)
    }
    /// Relation-SCC grounding with an independent allowance for each owned unit.
    pub fn prepare_with_grounding<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        plans: &mut dyn JoinPlanStore,
        grounding: &mut dyn GroundingStore,
    ) -> Result<RequestPreparation<'s>> {
        self.prepare_using(corpus, keys, operations, Some(plans), Some(grounding), None)
    }
    /// Reuse this run's assumption-independent fixed facts. Declaration checking
    /// uses assumption-independent fixed truth, including for unnamed requests.
    pub fn prepare_with_fixed<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        fixed: &FixedPreparation<'s>,
        plans: Option<&mut dyn JoinPlanStore>,
    ) -> Result<RequestPreparation<'s>> {
        self.prepare_using(corpus, keys, operations, plans, None, Some(fixed))
    }
    fn prepare_using<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        plans: Option<&mut dyn JoinPlanStore>,
        grounding: Option<&mut dyn GroundingStore>,
        fixed: Option<&FixedPreparation<'s>>,
    ) -> Result<RequestPreparation<'s>> {
        operations.cancellation.check()?;
        keys.validate(corpus).map_err(CheckError::Keys)?;
        if self.backend != BackendIdentity::bdd() {
            return Err(CheckError::InvalidRequest("unknown backend/configuration"));
        }
        let all = corpus
            .obligations()
            .map(|o| {
                Ok((
                    keys.obligation(o.id).map_err(CheckError::Keys)?.clone(),
                    o.id,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        let obligations = self
            .obligations
            .iter()
            .map(|key| {
                all.get(key)
                    .copied()
                    .ok_or(CheckError::InvalidRequest("unknown obligation key"))
            })
            .collect::<Result<BTreeSet<_>>>()?;
        for key in &self.notices {
            if !corpus
                .notices()
                .any(|n| keys.notice(n.id).is_ok_and(|k| k == key))
            {
                return Err(CheckError::InvalidRequest("unknown notice key"));
            }
        }
        if let Some(verification) = &self.verification {
            let declaration = corpus
                .verifications()
                .find(|v| keys.verification(v.id).is_ok_and(|key| key == verification))
                .ok_or(CheckError::InvalidRequest("unknown verification key"))?;
            let (constraints, selected) = verification_selection(corpus, keys, declaration.id)?;
            let notices = declaration
                .notices
                .iter()
                .map(|id| keys.notice(*id).cloned().map_err(CheckError::Keys))
                .collect::<Result<BTreeSet<_>>>()?;
            if self.constraints != constraints
                || self.obligations != selected
                || self.notices != notices
            {
                return Err(CheckError::InvalidRequest(
                    "request does not match its verification",
                ));
            }
        }
        let sorts = corpus
            .sorts()
            .map(|s| Ok((keys.sort(s.id).map_err(CheckError::Keys)?, s.id)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let constants = corpus
            .constants()
            .map(|c| Ok((keys.constant(c.id).map_err(CheckError::Keys)?, c.id)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let relations = corpus
            .relations()
            .map(|r| Ok((keys.relation(r.id).map_err(CheckError::Keys)?, r.id)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let domains = self
            .domains
            .iter()
            .map(|(s, v)| {
                Ok((
                    *sorts
                        .get(s)
                        .ok_or(CheckError::InvalidRequest("unknown sort key"))?,
                    v.iter()
                        .map(|k| {
                            constants
                                .get(k)
                                .copied()
                                .ok_or(CheckError::InvalidRequest("unknown constant key"))
                        })
                        .collect::<Result<_>>()?,
                ))
            })
            .collect::<Result<Domains>>()?;
        let constraints = self
            .constraints
            .iter()
            .filter_map(|c| match c {
                InputConstraint::AtMostOne { .. } => Some(c),
                _ => None,
            })
            .map(|c| match c {
                InputConstraint::AtMostOne { relation, group_by } => Ok(InputAtMostOne {
                    relation: *relations
                        .get(relation)
                        .ok_or(CheckError::InvalidRequest("unknown constraint relation"))?,
                    group_by: group_by.clone(),
                }),
                _ => unreachable!(),
            })
            .collect::<Result<Vec<_>>>()?;
        let limits = self.limits.with_operations(operations);
        let mut budget = Budget::tracked(&limits);
        let mut receipts = WorkReceipts::default();
        let mut local_fixed = None;
        let mut fixed = fixed;
        let mut specialized = None;
        if let Some(fixed) = fixed {
            for (key, receipt) in fixed.transfer_receipts.entries() {
                receipts
                    .record(key.clone(), receipt.clone())
                    .map_err(CheckError::Receipts)?;
            }
            receipts
                .record(QueryKey::FixedFacts, fixed.receipt.clone())
                .map_err(CheckError::Receipts)?;
        }
        if let Some(fixed) = fixed {
            if let Err(error) = fixed.validate_snapshot(corpus, &domains, &mut budget) {
                budget.failure(&error);
                let reason = Inconclusive::from_error(error)?;
                let dependencies = receipts
                    .entries()
                    .map(|(k, _)| k.clone())
                    .collect::<Vec<_>>();
                budget.record(&mut receipts, QueryKey::Preparation, dependencies)?;
                return Ok(RequestPreparation::Inconclusive { reason, receipts });
            }
            if let Some(context) = fixed
                .contexts
                .borrow()
                .iter()
                .find(|c| c.constraints == self.constraints)
            {
                if !std::ptr::eq(context.semantic_keys, keys) {
                    return Err(CheckError::InvalidRequest(
                        "shared preparation keys do not match this snapshot",
                    ));
                }
                return context.attach(self, corpus, keys, obligations, operations);
            }
        }
        let prepared_obligations = if fixed.is_some() {
            BTreeSet::new()
        } else {
            obligations.clone()
        };
        let result = (|| {
            let ground_validation = corpus.validate_assumption_relations_with(
                self.constraints
                    .iter()
                    .filter_map(|c| relations.get(c.relation()).copied()),
                || budget.tick("assumptions"),
            )?;
            let needs_grounding = ground_validation
                .values()
                .any(|v| *v == denotate_ir::AssumptionCone::NeedsGrounding);
            if needs_grounding && fixed.is_none() {
                // The direct and optional grounding-cache entry points use the
                // same independently folded meaning for cyclic assumption cones.
                local_fixed = Some(
                    FixedPreparation::prepare(corpus, &domains, &limits)
                        .map_err(|e| e.in_phase("assumption validation", None))?,
                );
                fixed = local_fixed.as_ref();
                receipts
                    .record(QueryKey::FixedFacts, fixed.unwrap().receipt.clone())
                    .map_err(CheckError::Receipts)?;
            }
            if let Some(fixed) = fixed {
                if needs_grounding || fixed.validation.get().is_some() {
                    let checked = fixed.assumption_preparation(keys, &limits)?;
                    if needs_grounding {
                        receipts
                            .record(QueryKey::AssumptionValidation, checked.receipt.clone())
                            .map_err(CheckError::Receipts)?;
                    }
                    for (relation, classification) in &ground_validation {
                        if *classification == denotate_ir::AssumptionCone::NeedsGrounding {
                            checked.check(*relation, keys, &mut budget)?;
                        }
                    }
                    // An unrelated exhausted declaration query must not block a
                    // relation-stratified selection's ordinary preparation.
                    if let Some((base, view)) = checked.programs() {
                        receipts
                            .record(QueryKey::AssumptionValidation, checked.receipt.clone())
                            .map_err(CheckError::Receipts)?;
                        specialized = Some(view.clone());
                        let mut program = base.clone();
                        program.obligations = prepared_obligations.clone();
                        program.build_groups(corpus, &mut budget)?;
                        program.build_input_groups(corpus, &constraints, &mut budget)?;
                        return Ok(program);
                    }
                }
            }
            let _profile = limits.profile.span("residual-preparation", None);
            if let Some(store) = grounding {
                GroundProgram::prepare_grounding(
                    corpus,
                    keys,
                    &domains,
                    &constraints,
                    &prepared_obligations,
                    &mut budget,
                    plans.expect("grounding requires a plan provider"),
                    store,
                    &mut receipts,
                )
            } else {
                GroundProgram::prepare_using_fixed(
                    corpus,
                    &domains,
                    &constraints,
                    &prepared_obligations,
                    &mut budget,
                    plans.map(|store| (keys, store)),
                    fixed,
                )
            }
        })();
        if let Err(error) = &result {
            Inconclusive::from_error(error.clone())?;
            budget.failure(error);
        }
        let dependencies = receipts
            .entries()
            .map(|(k, _)| k.clone())
            .collect::<Vec<_>>();
        let program = match result {
            Ok(p) => p,
            Err(error) => {
                budget.record(&mut receipts, QueryKey::Preparation, dependencies)?;
                return Ok(RequestPreparation::Inconclusive {
                    reason: Inconclusive::from_error(error)?,
                    receipts,
                });
            }
        };
        let key_start = Instant::now();
        let mut program = {
            let _profile = limits.profile.span("input-key-order", None);
            if program.input_order.is_some() {
                program
            } else {
                program.with_atom_key_order(keys)?
            }
        };
        let key_order_time = key_start.elapsed();
        let general = self
            .constraints
            .iter()
            .filter_map(|c| match c {
                InputConstraint::Cardinality {
                    kind,
                    relation,
                    group_by,
                } => Some((kind, relation, group_by)),
                _ => None,
            })
            .map(|(kind, key, group)| {
                let relation = *relations
                    .get(key)
                    .ok_or(CheckError::InvalidRequest("unknown constraint relation"))?;
                let group_by = group.clone();
                Ok(match kind {
                    Cardinality::Empty if group.is_empty() => Restriction::Empty { relation },
                    Cardinality::Empty => {
                        return Err(CheckError::InvalidRequest("empty assumption has grouping"));
                    }
                    Cardinality::AtMostOne => Restriction::AtMostOne { relation, group_by },
                    Cardinality::AtLeastOne => Restriction::AtLeastOne { relation, group_by },
                    Cardinality::ExactlyOne => Restriction::ExactlyOne { relation, group_by },
                })
            })
            .collect::<Result<Vec<_>>>()?;
        if !general.is_empty() {
            if let Err(error) =
                program.install_assumptions(&general, specialized.as_ref(), &mut budget)
            {
                budget.failure(&error);
                let reason = Inconclusive::from_error(error)?;
                budget.record(&mut receipts, QueryKey::Preparation, dependencies)?;
                return Ok(RequestPreparation::Inconclusive { reason, receipts });
            }
        }
        budget.record(&mut receipts, QueryKey::Preparation, dependencies)?;
        let index = {
            let _profile = limits.profile.span("semantic-keys", None);
            let shared = fixed.and_then(|fixed| {
                fixed
                    .contexts
                    .borrow()
                    .iter()
                    .find(|context| std::ptr::eq(context.semantic_keys, keys))
                    .map(|context| context.index.core.clone())
            });
            GroundKeyIndex::build_shared(corpus, keys, &program, shared)
                .map_err(CheckError::Keys)?
        };
        operations.cancellation.check()?;
        let key_computation = key_order_time + index.elapsed;
        if let Some(fixed) = fixed {
            let context = SharedContext {
                constraints: self.constraints.clone(),
                semantic_keys: keys,
                program,
                index,
                receipts,
                admission: Default::default(),
            };
            let mut attached = context.attach(self, corpus, keys, obligations, operations)?;
            if let RequestPreparation::Complete(prepared) = &mut attached {
                prepared.key_computation += key_computation;
            }
            // An exhausted attachment is never retained as a completed context.
            if matches!(attached, RequestPreparation::Complete(_)) {
                fixed.contexts.borrow_mut().push(context);
            }
            return Ok(attached);
        }
        Ok(RequestPreparation::Complete(PreparedCheck {
            request: self.clone(),
            emptiness_examples: EmptinessExamples::default(),
            program,
            keys: index,
            corpus,
            semantic_keys: keys,
            key_computation,
            receipts,
            shared_admission: None,
        }))
    }
    pub fn exhausted(&self, reason: Inconclusive) -> ScopedResults {
        ScopedResults {
            inconsistent_assumptions: false,
            notices: BTreeMap::new(),
            context: self.clone(),
            groups: BTreeMap::new(),
            coverage: BTreeMap::new(),
            emptiness: BTreeMap::new(),
            group_domains: BTreeMap::new(),
            regions: BTreeMap::new(),
            incomplete: BTreeMap::new(),
            unfinished: Some(ResourceReason::from(reason)),
            admission_skips: vec![],
        }
    }
}

/// Legacy adapter for direct input-at-most-one preparation. General restrictions
/// require `CheckRequest::for_verification`; they are rejected here, never omitted.
/// A foreign verification is rejected; unselected assumptions never contribute.
pub fn verification_constraints(
    corpus: &Corpus,
    verification: VerificationId,
) -> Result<Vec<InputAtMostOne>> {
    let declaration = corpus
        .verification(verification)
        .ok_or(CheckError::InvalidRequest("unknown verification"))?;
    declaration
        .assumptions
        .iter()
        .map(|id| {
            let assumption = corpus
                .assumption(*id)
                .ok_or(CheckError::InvalidRequest("unknown assumption"))?;
            match &assumption.restriction {
                Restriction::AtMostOne { relation, group_by }
                    if corpus.relation(*relation).unwrap().role == RelationRole::Input =>
                {
                    Ok(InputAtMostOne {
                        relation: *relation,
                        group_by: group_by.clone(),
                    })
                }
                _ => Err(CheckError::InvalidRequest(
                    "use CheckRequest::for_verification for general assumptions",
                )),
            }
        })
        .collect()
}

fn verification_selection(
    corpus: &Corpus,
    keys: &SemanticKeys,
    verification: VerificationId,
) -> Result<(Vec<InputConstraint>, BTreeSet<ObligationKey>)> {
    let declaration = corpus
        .verification(verification)
        .ok_or(CheckError::InvalidRequest("unknown verification"))?;
    let constraints = declaration
        .assumptions
        .iter()
        .map(|id| {
            let r = &corpus
                .assumption(*id)
                .ok_or(CheckError::InvalidRequest("unknown assumption"))?
                .restriction;
            let relation = keys
                .relation(r.relation())
                .map_err(CheckError::Keys)?
                .clone();
            let group_by = r.group_by().to_vec();
            Ok(
                if r.kind() == Cardinality::AtMostOne
                    && corpus.relation(r.relation()).unwrap().role == RelationRole::Input
                {
                    InputConstraint::AtMostOne { relation, group_by }
                } else {
                    InputConstraint::Cardinality {
                        kind: r.kind(),
                        relation,
                        group_by,
                    }
                },
            )
        })
        .collect::<Result<_>>()?;
    let obligations = declaration
        .obligations
        .iter()
        .map(|id| keys.obligation(*id).cloned().map_err(CheckError::Keys))
        .collect::<Result<_>>()?;
    Ok((constraints, obligations))
}

#[derive(Clone, PartialEq, Eq)]
pub enum UnsupportedReason {
    /// The BDD fixed-point backend cannot settle this negative recursive SCC.
    UnsettledNegativeCycle,
    /// The group's closed dependency cone includes unsettled negative recursion.
    DependsOnUnsettled(BTreeSet<ComponentKey>),
}
// Historical reference artifacts contain this diagnostic Debug spelling.
// Preserve it while using clearer Rust variant names; no semantic capture changes.
impl std::fmt::Debug for UnsupportedReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsettledNegativeCycle => f.write_str("NegativeCycle"),
            Self::DependsOnUnsettled(keys) => {
                f.debug_tuple("UnsettledDependencies").field(keys).finish()
            }
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceReason {
    pub phase: String,
    pub resource: String,
    pub details: LimitDetails,
}
impl From<Inconclusive> for ResourceReason {
    fn from(c: Inconclusive) -> Self {
        Self {
            phase: c.phase.into(),
            resource: c.resource.into(),
            details: c.details,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    pub present: BTreeSet<AtomKey>,
    pub absent: BTreeSet<AtomKey>,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EvidenceKeys {
    pub instances: BTreeSet<InstanceKey>,
    pub occurrences: BTreeSet<OccurrenceKey>,
    pub providers: BTreeSet<ComponentKey>,
    pub rewrites: BTreeSet<RewriteEvidenceKey>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificationScope {
    WholeProgram,
    ConeOnly,
}
/// Only produced by the checked projection of a replayed/certified finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedCandidate {
    pub candidate: Candidate,
    pub tuples: BTreeSet<AtomKey>,
    pub dependency_inputs: Option<Attribution<BTreeSet<AtomKey>>>,
    pub scope: CertificationScope,
    pub confined_to_no_meaning: BTreeSet<ComponentKey>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopedResult {
    Proved,
    Counterexample(CertifiedCandidate, EvidenceKeys),
    Unsupported(UnsupportedReason),
    Inconclusive(ResourceReason),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionCompletion {
    NoContradiction,
    NoMeaning {
        candidate: Candidate,
        evidence: EvidenceKeys,
    },
    Deferred(BTreeSet<ComponentKey>),
    Inconclusive(ResourceReason),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionResult {
    pub outcome: ScopedResult,
    pub completion: RegionCompletion,
    pub admission_skips: Vec<KeyedAdmissionSkip>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyedAdmissionSkip {
    pub kind: AdmissionAttemptKind,
    pub head: AtomKey,
    pub rule: Option<InstanceKey>,
    pub occurrence: Option<OccurrenceKey>,
    pub reason: ResourceReason,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedResults {
    pub admission_skips: Vec<KeyedAdmissionSkip>,
    pub inconsistent_assumptions: bool,
    pub notices: BTreeMap<NoticeKey, NoticeResult>,
    pub context: CheckRequest,
    pub groups: BTreeMap<GroupKey, ScopedResult>,
    pub emptiness: BTreeMap<ObligationKey, EmptinessResult>,
    pub coverage: BTreeMap<ObligationKey, CoverageResult>,
    /// Compact domain of legal groups, including trivially proved zero/one-member
    /// groups. Empty when none are selected or preparation did not finish.
    pub group_domains: BTreeMap<ObligationKey, KeyedGroups>,
    pub regions: BTreeMap<ComponentKey, RegionResult>,
    pub incomplete: BTreeMap<ComponentKey, ResourceReason>,
    /// Exhaustion before enumeration. Does not erase earlier completed scopes.
    pub unfinished: Option<ResourceReason>,
}

impl ScopedResults {
    /// The uniqueness result for uniqueness-bearing obligations (including
    /// exactly-one), not a combined coverage/uniqueness verdict. Coverage is
    /// reported separately in `coverage`.
    pub fn group(&self, key: &GroupKey) -> Option<ScopedResult> {
        if self.inconsistent_assumptions {
            return None;
        }
        if let Some(result) = self.groups.get(key) {
            return Some(result.clone());
        }
        let domain = self.group_domains.get(&key.obligation)?;
        domain.key(&key.obligation, key.tuple.clone()).ok()?;
        if !domain.kind.has_uniqueness() {
            return self
                .coverage
                .get(&key.obligation)?
                .proved()
                .then_some(ScopedResult::Proved);
        }
        if domain.members.get(&key.tuple).map_or(0, BTreeSet::len) <= 1 {
            Some(ScopedResult::Proved)
        } else {
            None
        }
    }
}

type SharedAdmission =
    std::sync::Arc<std::sync::OnceLock<(std::sync::Arc<GroundCore>, WorkReceipt)>>;

/// Bound to one source snapshot. No arena handles escape into a session cache.
pub(crate) struct SharedContext<'a> {
    constraints: Vec<InputConstraint>,
    semantic_keys: &'a SemanticKeys,
    program: GroundProgram,
    index: GroundKeyIndex,
    receipts: WorkReceipts,
    admission: SharedAdmission,
}
impl SharedContext<'_> {
    fn attach<'s>(
        &self,
        request: &CheckRequest,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        obligations: BTreeSet<ObligationId>,
        operations: &OperationalLimits,
    ) -> Result<RequestPreparation<'s>> {
        let limits = request.limits.with_operations(operations);
        let original = self.receipts.get(&QueryKey::Preparation).unwrap();
        let mut budget = Budget::resume(&limits, original.own.clone());
        let mut program = self.program.clone();
        program.obligations = obligations;
        let result = program.build_groups(corpus, &mut budget);
        if let Err(error) = &result {
            budget.failure(error);
        }
        let mut receipts = self.receipts.clone();
        receipts.invalidate(&QueryKey::Preparation);
        budget.record(
            &mut receipts,
            QueryKey::Preparation,
            original.dependencies.clone(),
        )?;
        if let Err(error) = result {
            return Ok(RequestPreparation::Inconclusive {
                reason: Inconclusive::from_error(error)?,
                receipts,
            });
        }
        let start = Instant::now();
        let mut index = self.index.clone();
        index.build_groups(corpus, keys, &program)?;
        operations.cancellation.check()?;
        Ok(RequestPreparation::Complete(PreparedCheck {
            request: request.clone(),
            emptiness_examples: Default::default(),
            program,
            keys: index,
            corpus,
            semantic_keys: keys,
            key_computation: start.elapsed(),
            receipts,
            shared_admission: Some(self.admission.clone()),
        }))
    }
}

pub struct PreparedCheck<'s> {
    shared_admission: Option<SharedAdmission>,
    pub(crate) request: CheckRequest,
    pub(crate) emptiness_examples: EmptinessExamples,
    pub(crate) program: GroundProgram,
    pub(crate) keys: GroundKeyIndex,
    corpus: &'s Corpus,
    pub(crate) semantic_keys: &'s SemanticKeys,
    key_computation: Duration,
    pub(crate) receipts: WorkReceipts,
}
pub enum RequestPreparation<'s> {
    Complete(PreparedCheck<'s>),
    Inconclusive {
        reason: Inconclusive,
        receipts: WorkReceipts,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStage {
    SymbolicEvaluation,
    Verification,
}
impl CheckStage {
    pub fn label(self) -> &'static str {
        match self {
            Self::SymbolicEvaluation => "symbolic evaluation",
            Self::Verification => "verification",
        }
    }
}
pub enum CheckOutcome<'p> {
    Complete(CheckedReport<'p>),
    Inconclusive {
        stage: CheckStage,
        reason: Inconclusive,
        receipts: WorkReceipts,
    },
}
/// Optional observations of this invocation, never cached or compared as meaning.
#[derive(Debug, Default)]
pub struct VerificationMetrics {
    /// Time in the selected-notice pass, including projection to semantic keys.
    /// None means that pass was not reached or no notices were selected.
    pub notices: Option<Duration>,
}
pub struct CheckedReport<'p> {
    /// Fresh snapshot-owned presentation/replay detail; never memoized.
    pub verification: Verification<'p>,
    pub results: Accounted<ScopedResults>,
}
impl PreparedCheck<'_> {
    /// Choose retained diagnostic examples for this invocation. This does not
    /// change the request, candidate scan, semantic budgets or cache inputs.
    /// Sessions recompute emptiness evidence using the current choice.
    pub fn with_emptiness_examples(mut self, examples: EmptinessExamples) -> Self {
        self.emptiness_examples = examples;
        self
    }
    pub fn request(&self) -> &CheckRequest {
        &self.request
    }
    pub fn receipts(&self) -> &WorkReceipts {
        &self.receipts
    }
    pub fn program(&self) -> &GroundProgram {
        &self.program
    }
    pub fn keys(&self) -> &GroundKeyIndex {
        &self.keys
    }
    pub fn key_view(&self) -> GroundKeyView<'_> {
        self.keys
            .view(self.corpus, self.semantic_keys, &self.program)
    }
    /// Initial ordering/schema/group projection. On-demand local query keys
    /// are accounted in LocalMetrics; admission needs no key refresh.
    pub fn key_computation(&self) -> Duration {
        self.key_computation
    }
    pub fn admit(self, operations: &OperationalLimits) -> Result<Self> {
        self.admit_with_progress(operations, None)
    }
    /// Observational, invocation-local progress; never retained with admission.
    pub fn admit_with_progress(
        mut self,
        operations: &OperationalLimits,
        observer: Option<&AdmissionObserver<'_>>,
    ) -> Result<Self> {
        let limits = self.request.limits.with_operations(operations);
        let mut budget = Budget::tracked(&limits);
        operations.cancellation.check()?;
        budget.check("admission")?;
        if let Some((program, receipt)) = self.shared_admission.as_ref().and_then(|c| c.get()) {
            self.program.core = program.clone();
            self.receipts.invalidate(&QueryKey::Admission);
            self.receipts
                .record(QueryKey::Admission, receipt.clone())
                .map_err(CheckError::Receipts)?;
            crate::admission_progress::AdmissionReporter::new(observer).snapshot(
                &self.program,
                0,
                "reused",
            );
            return Ok(self);
        }
        self.program = self.program.admit_observed(&mut budget, observer)?;
        self.receipts.invalidate(&QueryKey::Admission);
        budget.record(
            &mut self.receipts,
            QueryKey::Admission,
            [QueryKey::Preparation],
        )?;
        // Keys are projected from the current graph on demand. Admission already
        // stores its changed bodies and original proofs there; no key refresh.
        operations.cancellation.check()?;
        if self.program.admission_limit().is_none() {
            if let Some(cell) = &self.shared_admission {
                let _ = cell.set((
                    self.program.core.clone(),
                    self.receipts.get(&QueryKey::Admission).unwrap().clone(),
                ));
            }
        }

        Ok(self)
    }
    pub fn verify(&self, operations: &OperationalLimits) -> Result<CheckOutcome<'_>> {
        self.verify_observed(operations, None)
    }
    /// As `verify`, with observational timings reset even if this call fails early.
    pub fn verify_with_metrics(
        &self,
        operations: &OperationalLimits,
        metrics: &mut VerificationMetrics,
    ) -> Result<CheckOutcome<'_>> {
        *metrics = VerificationMetrics::default();
        self.verify_observed(operations, Some(metrics))
    }
    pub(crate) fn verify_observed(
        &self,
        operations: &OperationalLimits,
        metrics: Option<&mut VerificationMetrics>,
    ) -> Result<CheckOutcome<'_>> {
        let limits = self.request.limits.with_operations(operations);
        if !self.program.assumptions_consistent() {
            operations.cancellation.check()?;
            let verification = Verification::inconsistent(&self.program);
            let mut results = self.project(&verification, self.semantic_keys)?;
            results.group_domains.clear();
            return Ok(CheckOutcome::Complete(CheckedReport {
                verification,
                results: Accounted {
                    value: results,
                    receipts: self.receipts.clone(),
                },
            }));
        }
        let mut receipts = self.receipts.clone();
        let mut budget = Budget::tracked(&limits);
        let meaning = self.program.symbolic_impl(&mut budget, true);
        if let Err(error) = &meaning {
            Inconclusive::from_error(error.clone())?;
            budget.failure(error);
        }
        let dependency = if receipts.get(&QueryKey::Admission).is_some() {
            QueryKey::Admission
        } else {
            QueryKey::Preparation
        };
        budget.record(&mut receipts, QueryKey::Symbolic, [dependency])?;
        let meaning = match AnalysisOutcome::from_result(meaning)? {
            AnalysisOutcome::Complete(m) => m,
            AnalysisOutcome::Inconclusive(reason) => {
                return Ok(CheckOutcome::Inconclusive {
                    stage: CheckStage::SymbolicEvaluation,
                    reason,
                    receipts,
                });
            }
        };
        let mut queries = QueryRun {
            keys: self.semantic_keys,
            ground: &self.program,
            receipts: &mut receipts,
        };
        let verification = match AnalysisOutcome::from_result(meaning.verify_queries(
            &limits,
            &limits,
            &limits,
            self.emptiness_examples,
            Some(&mut queries),
        ))? {
            AnalysisOutcome::Complete(r) => r,
            AnalysisOutcome::Inconclusive(reason) => {
                return Ok(CheckOutcome::Inconclusive {
                    stage: CheckStage::Verification,
                    reason,
                    receipts,
                });
            }
        };
        let mut results = self.project(&verification, self.semantic_keys)?;
        results.notices = self.check_notices(operations, &mut receipts, metrics)?;
        receipts.total().map_err(CheckError::Receipts)?;
        operations.cancellation.check()?;
        Ok(CheckOutcome::Complete(CheckedReport {
            verification,
            results: Accounted {
                value: results,
                receipts,
            },
        }))
    }
    pub(crate) fn check_notices(
        &self,
        operations: &OperationalLimits,
        receipts: &mut WorkReceipts,
        metrics: Option<&mut VerificationMetrics>,
    ) -> Result<BTreeMap<NoticeKey, NoticeResult>> {
        let start = metrics
            .as_ref()
            .filter(|_| !self.request.notices.is_empty() && self.program.assumptions_consistent())
            .map(|_| Instant::now());
        let result = self.check_notices_inner(operations, receipts);
        if let Some(metrics) = metrics {
            metrics.notices = start.map(|start| start.elapsed());
        }
        result
    }
    fn check_notices_inner(
        &self,
        operations: &OperationalLimits,
        receipts: &mut WorkReceipts,
    ) -> Result<BTreeMap<NoticeKey, NoticeResult>> {
        let limits = self.request.limits.with_operations(operations);
        let mut out = BTreeMap::new();
        if !self.program.assumptions_consistent() {
            return Ok(out);
        }
        for key in &self.request.notices {
            let n = self
                .corpus
                .notices()
                .find(|n| self.semantic_keys.notice(n.id).is_ok_and(|k| k == key))
                .ok_or(CheckError::InvalidRequest("unknown notice key"))?;
            let _stage = limits
                .progress
                .advisory("notice", CheckingTarget::Notice(n.id));
            let mut budget = Budget::tracked(&limits);
            let result =
                self.program
                    .analyze_condition_with_budget(n.condition, n.within, &mut budget)?;
            // Deadlines are operational outcomes, never recorded as semantic work.
            if !matches!(
                result.state,
                NoticeState::Unknown(NoticeUnknown::Deadline { .. })
            ) {
                let dependency = if receipts.get(&QueryKey::Admission).is_some() {
                    QueryKey::Admission
                } else {
                    QueryKey::Preparation
                };
                budget.record(receipts, QueryKey::Notice(key.clone()), [dependency])?;
            }
            let example = |w: NoticeWitness| -> Result<NoticeExample> {
                let convert = |a: &GroundAtom| {
                    AtomKey::from_atom(self.semantic_keys, a).map_err(CheckError::Keys)
                };
                Ok(NoticeExample {
                    observation: Candidate {
                        present: w
                            .observation
                            .present
                            .iter()
                            .map(convert)
                            .collect::<Result<_>>()?,
                        absent: w
                            .observation
                            .absent
                            .iter()
                            .map(convert)
                            .collect::<Result<_>>()?,
                    },
                    replay_scope: w.replay_scope,
                })
            };
            let mut blockers = BTreeMap::new();
            for id in &result.blocked_by {
                let key = self.key_view().component(*id)?;
                let cycle = self
                    .program
                    .component(*id)
                    .and_then(|c| c.cycle.as_ref())
                    .ok_or(CheckError::Internal("missing notice blocking cycle"))?;
                let rules = cycle
                    .edges
                    .iter()
                    .map(|edge| {
                        let rule = self
                            .program
                            .rule(edge.rule)
                            .ok_or(CheckError::Internal("missing notice blocking rule"))?;
                        self.semantic_keys
                            .rule(rule.source)
                            .cloned()
                            .map_err(CheckError::Keys)
                    })
                    .collect::<Result<BTreeSet<_>>>()?;
                blockers.insert(key, rules);
            }
            out.insert(
                key.clone(),
                NoticeResult {
                    state: result.state,
                    blockers,
                    when_true: result.when_true.map(example).transpose()?,
                    when_false: result.when_false.map(example).transpose()?,
                },
            );
        }
        Ok(out)
    }
    pub(crate) fn project(
        &self,
        report: &Verification<'_>,
        keys: &SemanticKeys,
    ) -> Result<ScopedResults> {
        let atom = |a: &GroundAtom| AtomKey::from_atom(keys, a).map_err(CheckError::Keys);
        let candidate = |o: &Observation| -> Result<Candidate> {
            Ok(Candidate {
                present: o.present.iter().map(&atom).collect::<Result<_>>()?,
                absent: o.absent.iter().map(&atom).collect::<Result<_>>()?,
            })
        };
        let component = |id: &ComponentId| self.key_view().component(*id);
        let project_skip = |s: &AdmissionSkip| -> Result<KeyedAdmissionSkip> {
            Ok(KeyedAdmissionSkip {
                kind: s.kind,
                head: atom(&s.head)?,
                rule: s.rule.map(|r| self.key_view().instance(r)).transpose()?,
                occurrence: s
                    .occurrence
                    .map(|o| keys.bindings().key(o).cloned().map_err(CheckError::Keys))
                    .transpose()?,
                reason: s.reason.into(),
            })
        };
        let mut admission_skips = self
            .program
            .admission_skips()
            .map(&project_skip)
            .collect::<Result<Vec<_>>>()?;
        admission_skips.sort_by(|a, b| {
            (&a.head, a.kind, &a.rule, &a.occurrence).cmp(&(
                &b.head,
                b.kind,
                &b.rule,
                &b.occurrence,
            ))
        });
        let mut out = ScopedResults {
            admission_skips,
            inconsistent_assumptions: !self.program.assumptions_consistent(),
            notices: BTreeMap::new(),
            context: self.request.clone(),
            groups: BTreeMap::new(),
            coverage: BTreeMap::new(),
            emptiness: BTreeMap::new(),
            group_domains: self.keys.groups.clone(),
            regions: BTreeMap::new(),
            incomplete: BTreeMap::new(),
            unfinished: None,
        };
        for (id, e) in &report.emptiness {
            out.emptiness.insert(
                keys.obligation(*id).map_err(CheckError::Keys)?.clone(),
                EmptinessResult {
                    present: e.present,
                    inconclusive: e.inconclusive,
                    unresolved: e.unresolved,
                    examples: e
                        .examples
                        .iter()
                        .map(|e| -> Result<_> {
                            Ok(PresenceExample {
                                tuple: AtomKey::from_atom(keys, &e.tuple)
                                    .map_err(CheckError::Keys)?,
                                observation: candidate(&e.observation)?,
                                replay_scope: e.replay_scope,
                                dependency_inputs: project_dependency_inputs(
                                    e.dependency_inputs.as_ref(),
                                    keys,
                                )?,
                                attribution: e
                                    .attribution
                                    .as_ref()
                                    .map(|a| -> Result<_> {
                                        Ok(match a {
                                            Attribution::Incomplete(c) => {
                                                Attribution::Incomplete(*c)
                                            }
                                            Attribution::Complete(steps) => {
                                                let mut evidence = EvidenceKeys::default();
                                                for step in steps.values() {
                                                    if let GroundEvidence::Derived {
                                                        rule, ..
                                                    } = &step.evidence
                                                    {
                                                        self.rule_evidence(
                                                            rule,
                                                            keys,
                                                            &mut evidence,
                                                        )?;
                                                    }
                                                }
                                                Attribution::Complete(evidence)
                                            }
                                        })
                                    })
                                    .transpose()?,
                            })
                        })
                        .collect::<Result<_>>()?,
                },
            );
        }
        for (id, coverage) in &report.coverage {
            out.coverage.insert(
                keys.obligation(*id).map_err(CheckError::Keys)?.clone(),
                CoverageResult {
                    examined: coverage.examined,
                    missing: coverage.missing,
                    unsupported: coverage.unsupported,
                    inconclusive: coverage.inconclusive,
                    no_groups: coverage.no_groups,
                    examples: coverage
                        .examples
                        .iter()
                        .map(|e| {
                            Ok(CoverageExample {
                                group: e
                                    .group
                                    .iter()
                                    .map(|id| keys.constant(*id).cloned().map_err(CheckError::Keys))
                                    .collect::<Result<_>>()?,
                                observation: candidate(&e.observation)?,
                                replay_scope: e.replay_scope,
                                dependency_inputs: project_dependency_inputs(
                                    e.dependency_inputs.as_ref(),
                                    keys,
                                )?,
                            })
                        })
                        .collect::<Result<_>>()?,
                },
            );
        }
        for g in &report.groups {
            let key = GroupKey {
                obligation: keys
                    .obligation(g.group.obligation)
                    .map_err(CheckError::Keys)?
                    .clone(),
                tuple: g
                    .group
                    .key
                    .iter()
                    .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                    .collect::<Result<_>>()?,
            };
            let result = match &g.outcome {
                VerifiedOutcome::Proved => ScopedResult::Proved,
                VerifiedOutcome::Inconclusive(c) => ScopedResult::Inconclusive((*c).into()),
                VerifiedOutcome::Unsupported => {
                    ScopedResult::Unsupported(UnsupportedReason::DependsOnUnsettled(
                        g.cone
                            .blocked_by
                            .iter()
                            .map(&component)
                            .collect::<Result<_>>()?,
                    ))
                }
                VerifiedOutcome::Counterexample(c) => {
                    let mut evidence = EvidenceKeys::default();
                    let residual = match &c.certification {
                        Some(CertificationOutcome::Certified(v)) => Some(&v.providers),
                        _ => None,
                    };
                    for step in c.evidence.values() {
                        if let GroundEvidence::Derived { rule, premises } = &step.evidence {
                            self.rule_evidence(rule, keys, &mut evidence)?;
                            for p in premises {
                                match p {
                                    PremiseEvidence::Positive { occurrence, .. } => {
                                        evidence.occurrences.insert(
                                            keys.bindings()
                                                .key(*occurrence)
                                                .map_err(CheckError::Keys)?
                                                .clone(),
                                        );
                                    }
                                    PremiseEvidence::Absent {
                                        occurrence,
                                        provider,
                                        ..
                                    } => {
                                        evidence.occurrences.insert(
                                            keys.bindings()
                                                .key(*occurrence)
                                                .map_err(CheckError::Keys)?
                                                .clone(),
                                        );
                                        if let CompletedProvider::Component(id) = provider {
                                            let key = if let Some(atoms) =
                                                residual.and_then(|p| p.get(id))
                                            {
                                                ComponentKey(
                                                    atoms
                                                        .iter()
                                                        .map(&atom)
                                                        .collect::<Result<BTreeSet<_>>>()?
                                                        .into_iter()
                                                        .collect::<Vec<_>>()
                                                        .into(),
                                                )
                                            } else {
                                                component(id)?
                                            };
                                            evidence.providers.insert(key);
                                        }
                                    }
                                    PremiseEvidence::Discharged {
                                        literal_occurrence,
                                        proof,
                                    } => {
                                        evidence.occurrences.insert(
                                            keys.bindings()
                                                .key(*literal_occurrence)
                                                .map_err(CheckError::Keys)?
                                                .clone(),
                                        );
                                        evidence.rewrites.insert(self.key_view().rewrite(*proof)?);
                                    }
                                }
                            }
                        }
                    }
                    ScopedResult::Counterexample(
                        CertifiedCandidate {
                            candidate: candidate(&c.observation)?,
                            tuples: c.tuples.iter().map(&atom).collect::<Result<_>>()?,
                            dependency_inputs: project_dependency_inputs(
                                c.dependency_inputs.as_ref(),
                                keys,
                            )?,
                            scope: match c.replay_scope {
                                ReplayScope::WholeProgram => CertificationScope::WholeProgram,
                                ReplayScope::ConeOnly => CertificationScope::ConeOnly,
                            },
                            confined_to_no_meaning: c
                                .confined_to_no_meaning
                                .iter()
                                .map(&component)
                                .collect::<Result<_>>()?,
                        },
                        evidence,
                    )
                }
            };
            out.groups.insert(key, result);
        }
        // Nontrivial groups are explicit above. Empty/singleton domain groups
        // remain represented compactly in GroundKeyIndex, never enumerated here.
        for r in &report.unresolved {
            let outcome = match r.outcome {
                RegionOutcome::Unsupported => {
                    ScopedResult::Unsupported(UnsupportedReason::UnsettledNegativeCycle)
                }
                RegionOutcome::Inconclusive(c) => ScopedResult::Inconclusive(c.into()),
            };
            let completion = match &r.completion {
                CompletionOutcome::NoContradiction => RegionCompletion::NoContradiction,
                CompletionOutcome::Inconclusive(c) => RegionCompletion::Inconclusive((*c).into()),
                CompletionOutcome::Deferred { blocked_by } => RegionCompletion::Deferred(
                    blocked_by.iter().map(&component).collect::<Result<_>>()?,
                ),
                CompletionOutcome::NoMeaning(n) => {
                    let mut evidence = EvidenceKeys::default();
                    for r in &n.rules {
                        self.rule_evidence(r, keys, &mut evidence)?;
                    }
                    for id in &n.rewrites {
                        evidence.rewrites.insert(self.key_view().rewrite(*id)?);
                    }
                    for b in n.upstream.values() {
                        if let CompletedProvider::Component(id) = b.provider {
                            evidence.providers.insert(component(&id)?);
                        }
                    }
                    RegionCompletion::NoMeaning {
                        candidate: candidate(&n.observation)?,
                        evidence,
                    }
                }
            };
            out.regions.insert(
                component(&r.component)?,
                RegionResult {
                    outcome,
                    completion,
                    admission_skips: r
                        .admission_skips
                        .iter()
                        .map(&project_skip)
                        .collect::<Result<_>>()?,
                },
            );
        }
        for (id, c) in &report.incomplete_evaluation {
            out.incomplete.insert(component(id)?, (*c).into());
        }
        Ok(out)
    }
    pub(crate) fn rule_evidence(
        &self,
        rule: &GroundRule,
        keys: &SemanticKeys,
        evidence: &mut EvidenceKeys,
    ) -> Result<()> {
        evidence
            .instances
            .insert(self.key_view().instance(rule.id)?);
        for a in std::iter::once(&rule.head).chain(rule.body.iter().map(|l| &l.term)) {
            for id in std::iter::once(a.occurrence).chain(a.arguments.iter().copied()) {
                evidence
                    .occurrences
                    .insert(keys.bindings().key(id).map_err(CheckError::Keys)?.clone());
            }
        }
        Ok(())
    }
}

fn project_dependency_inputs(
    scope: Option<&Attribution<BTreeSet<GroundAtom>>>,
    keys: &SemanticKeys,
) -> Result<Option<Attribution<BTreeSet<AtomKey>>>> {
    scope
        .map(|scope| {
            Ok(match scope {
                Attribution::Incomplete(c) => Attribution::Incomplete(*c),
                Attribution::Complete(inputs) => Attribution::Complete(
                    inputs
                        .iter()
                        .map(|a| AtomKey::from_atom(keys, a).map_err(CheckError::Keys))
                        .collect::<Result<_>>()?,
                ),
            })
        })
        .transpose()
}
