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
    pub cancellation: Cancellation,
    pub timeout: Duration,
}
impl From<&Limits> for OperationalLimits {
    fn from(l: &Limits) -> Self {
        Self {
            cancellation: l.cancellation.clone(),
            timeout: l.timeout,
        }
    }
}
impl DeterministicLimits {
    pub fn with_operations(&self, o: &OperationalLimits) -> Limits {
        Limits {
            cancellation: o.cancellation.clone(),
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
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckRequest {
    pub verification: Option<VerificationKey>,
    pub constraints: Vec<InputConstraint>,
    pub obligations: BTreeSet<ObligationKey>,
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
        // All current restrictions are input at-most-one constraints: the world
        // with every input absent witnesses their joint consistency.
        request.constraints = constraints;
        request.obligations = obligations;
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
        self.prepare_using(corpus, keys, operations, None, None)
    }
    pub fn prepare_with_plans<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        plans: &mut dyn JoinPlanStore,
    ) -> Result<RequestPreparation<'s>> {
        self.prepare_using(corpus, keys, operations, Some(plans), None)
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
        self.prepare_using(corpus, keys, operations, Some(plans), Some(grounding))
    }
    fn prepare_using<'s>(
        &self,
        corpus: &'s Corpus,
        keys: &'s SemanticKeys,
        operations: &OperationalLimits,
        plans: Option<&mut dyn JoinPlanStore>,
        grounding: Option<&mut dyn GroundingStore>,
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
        if let Some(verification) = &self.verification {
            let declaration = corpus
                .verifications()
                .find(|v| keys.verification(v.id).is_ok_and(|key| key == verification))
                .ok_or(CheckError::InvalidRequest("unknown verification key"))?;
            let (constraints, selected) = verification_selection(corpus, keys, declaration.id)?;
            if self.constraints != constraints || self.obligations != selected {
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
            .map(|c| match c {
                InputConstraint::AtMostOne { relation, group_by } => Ok(InputAtMostOne {
                    relation: *relations
                        .get(relation)
                        .ok_or(CheckError::InvalidRequest("unknown constraint relation"))?,
                    group_by: group_by.clone(),
                }),
            })
            .collect::<Result<Vec<_>>>()?;
        let limits = self.limits.with_operations(operations);
        let mut budget = Budget::tracked(&limits);
        let mut receipts = WorkReceipts::default();
        let result = if let Some(store) = grounding {
            GroundProgram::prepare_grounding(
                corpus,
                keys,
                &domains,
                &constraints,
                &obligations,
                &mut budget,
                plans.expect("grounding requires a plan provider"),
                store,
                &mut receipts,
            )
        } else {
            GroundProgram::prepare_using(
                corpus,
                &domains,
                &constraints,
                &obligations,
                &mut budget,
                plans.map(|store| (keys, store)),
            )
        };
        if let Err(error) = &result {
            Inconclusive::from_error(error.clone())?;
            budget.failure(error);
        }
        let dependencies = receipts
            .entries()
            .map(|(k, _)| k.clone())
            .collect::<Vec<_>>();
        budget.record(&mut receipts, QueryKey::Preparation, dependencies)?;
        let program = match result {
            Ok(p) => p,
            Err(error) => {
                return Ok(RequestPreparation::Inconclusive {
                    reason: Inconclusive::from_error(error)?,
                    receipts,
                });
            }
        };
        let key_start = Instant::now();
        let program = program.with_atom_key_order(keys)?;
        let index = GroundKeyIndex::build(corpus, keys, &program).map_err(CheckError::Keys)?;
        operations.cancellation.check()?;
        Ok(RequestPreparation::Complete(PreparedCheck {
            request: self.clone(),
            program,
            keys: index,
            corpus,
            semantic_keys: keys,
            key_computation: key_start.elapsed(),
            receipts,
        }))
    }
    pub fn exhausted(&self, reason: Inconclusive) -> ScopedResults {
        ScopedResults {
            context: self.clone(),
            groups: BTreeMap::new(),
            coverage: BTreeMap::new(),
            emptiness: BTreeMap::new(),
            group_domains: BTreeMap::new(),
            regions: BTreeMap::new(),
            incomplete: BTreeMap::new(),
            unfinished: Some(ResourceReason::from(reason)),
        }
    }
}

/// Lower the selected IR restrictions for keyed requests and direct preparation.
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
                Restriction::AtMostOne { relation, group_by } => Ok(InputAtMostOne {
                    relation: *relation,
                    group_by: group_by.clone(),
                }),
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
    let constraints = verification_constraints(corpus, verification)?
        .into_iter()
        .map(|c| {
            Ok(InputConstraint::AtMostOne {
                relation: keys.relation(c.relation).map_err(CheckError::Keys)?.clone(),
                group_by: c.group_by,
            })
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
}
impl From<Inconclusive> for ResourceReason {
    fn from(c: Inconclusive) -> Self {
        Self {
            phase: c.phase.into(),
            resource: c.resource.into(),
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
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedResults {
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

pub struct PreparedCheck<'s> {
    pub(crate) request: CheckRequest,
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
pub struct CheckedReport<'p> {
    /// Fresh snapshot-owned presentation/replay detail; never memoized.
    pub verification: Verification<'p>,
    pub results: Accounted<ScopedResults>,
}
impl PreparedCheck<'_> {
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
    /// Full ground-key work, including initial ordering/indexing and every
    /// post-admission refresh. Frontends add their installation-key phase.
    pub fn key_computation(&self) -> Duration {
        self.key_computation
    }
    pub fn admit(mut self, operations: &OperationalLimits) -> Result<Self> {
        let limits = self.request.limits.with_operations(operations);
        let mut budget = Budget::tracked(&limits);
        self.program = self.program.admit_with_budget(&mut budget)?;
        self.receipts.invalidate(&QueryKey::Admission);
        budget.record(
            &mut self.receipts,
            QueryKey::Admission,
            [QueryKey::Preparation],
        )?;
        self.keys = GroundKeyIndex::build(self.corpus, self.semantic_keys, &self.program)
            .map_err(CheckError::Keys)?;
        self.key_computation += self.keys.elapsed;
        operations.cancellation.check()?;
        Ok(self)
    }
    pub fn verify(&self, operations: &OperationalLimits) -> Result<CheckOutcome<'_>> {
        let limits = self.request.limits.with_operations(operations);
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
            ground: &self.keys,
            receipts: &mut receipts,
        };
        let verification = match AnalysisOutcome::from_result(meaning.verify_queries(
            &limits,
            &limits,
            &limits,
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
        let results = self.project(&verification, self.semantic_keys)?;
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
        let component = |id: &ComponentId| {
            self.keys
                .components
                .get(id)
                .cloned()
                .ok_or(CheckError::Internal("missing committed component key"))
        };
        let mut out = ScopedResults {
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
                    inconclusive: e.inconclusive,
                    unresolved: e.unresolved,
                    example: e
                        .example
                        .as_ref()
                        .map(|e| {
                            Ok(PresenceExample {
                                tuple: AtomKey::from_atom(keys, &e.tuple)
                                    .map_err(CheckError::Keys)?,
                                observation: candidate(&e.observation)?,
                                replay_scope: e.replay_scope,
                            })
                        })
                        .transpose()?,
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
                                        evidence.rewrites.insert(
                                            self.keys
                                                .rewrites
                                                .get(proof)
                                                .ok_or(CheckError::Internal(
                                                    "missing rewrite evidence key",
                                                ))?
                                                .clone(),
                                        );
                                    }
                                }
                            }
                        }
                    }
                    ScopedResult::Counterexample(
                        CertifiedCandidate {
                            candidate: candidate(&c.observation)?,
                            tuples: c.tuples.iter().map(&atom).collect::<Result<_>>()?,
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
                        evidence.rewrites.insert(
                            self.keys
                                .rewrites
                                .get(id)
                                .ok_or(CheckError::Internal("missing no-meaning rewrite key"))?
                                .clone(),
                        );
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
        evidence.instances.insert(
            self.keys
                .instances
                .get(&rule.id)
                .ok_or(CheckError::Internal("missing original instance key"))?
                .clone(),
        );
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
