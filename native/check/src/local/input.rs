//! Owned semantic query inputs and outputs, projected from the committed round.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LocalScope {
    Group(GroupKey),
    Region(ComponentKey),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalObligation {
    pub relation: RelationKey,
    pub group_by: Vec<usize>,
    pub domains: Vec<BTreeSet<ConstantKey>>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalComponent {
    pub recursive: bool,
    pub blocked_by: BTreeSet<ComponentKey>,
}
/// Structural inputs supplied by fresh grounding today, or cached grounding later.
/// No full-snapshot key computation is required by an individual query lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalInput {
    /// Only regions that replay discharge proofs need this context. Its BDD
    /// universe is conservatively global, explicit and owned.
    pub completion_context: Option<LocalCompletionContext>,
    pub scope: LocalScope,
    pub roots: BTreeSet<AtomKey>,
    pub obligation: Option<LocalObligation>,
    pub facts: BTreeSet<AtomKey>,
    pub possible: BTreeSet<AtomKey>,
    pub inputs: BTreeSet<AtomKey>,
    pub components: BTreeMap<ComponentKey, LocalComponent>,
    pub rules: BTreeMap<InstanceKey, GroundInstance>,
    pub original_dependencies: BTreeMap<InstanceKey, GroundInstance>,
    pub rewrites: BTreeSet<RewriteEvidenceKey>,
    pub domains: BTreeMap<SortKey, Vec<ConstantKey>>,
    pub constraints: Vec<InputConstraint>,
    pub input_groups: BTreeSet<BTreeSet<AtomKey>>,
    pub request_scope: RequestScope,
    pub backend: BackendIdentity,
    pub limits: DeterministicLimits,
    pub admission_limit: Option<Inconclusive>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalCompletionContext {
    pub inputs: BTreeSet<AtomKey>,
    pub input_groups: BTreeSet<BTreeSet<AtomKey>>,
    pub proofs: BTreeMap<RewriteEvidenceKey, (OwnedCondition, OwnedCondition)>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalEvaluation {
    pub permitted: OwnedCondition,
    pub conditions: BTreeMap<AtomKey, OwnedCondition>,
    pub incomplete: BTreeMap<ComponentKey, Inconclusive>,
}
/// Overlap is a candidate condition, not a certified Counterexample. Replay stays fresh.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalVerdict {
    Proved,
    Overlap(OwnedCondition),
    /// Validated concrete observation; fresh current-snapshot replay is still required.
    Candidate(Candidate),
    Unsupported(UnsupportedReason),
    Inconclusive(ResourceReason),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalAnswer {
    Group(LocalVerdict),
    Completion {
        outcome: RegionCompletion,
        bad_input: Option<OwnedCondition>,
        boundary: BTreeMap<AtomKey, OwnedCondition>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalArtifact {
    pub input: LocalInput,
    pub evaluation: Option<LocalEvaluation>,
    pub answer: Option<LocalAnswer>,
}
/// Physical work in coarse BDD obligation cones, never a semantic query result.
#[derive(Debug, Default)]
pub struct SccWork {
    /// Includes attempted evaluations that exhaust a deterministic allowance.
    pub cone_evaluations: usize,
    pub elapsed: Duration,
}
#[derive(Debug, Default)]
pub struct LocalMetrics {
    pub keys: Duration,
    /// Local context setup and symbolic evaluation, excluding owned BDD export.
    pub evaluation: Duration,
    pub export: Duration,
    pub conversion: Duration,
    pub completion: Duration,
    pub property: Duration,
    pub finding_context: Duration,
    pub cone_atoms: usize,
    pub unique_atoms: usize,
    pub cone_inputs: usize,
    /// Per-check physical work; cache hits and SAT group queries add nothing.
    /// Timing covers SCC fixed-point evaluation, excluding context setup/export.
    pub scc_work: BTreeMap<ComponentKey, SccWork>,
}
impl LocalMetrics {
    pub fn merge_scc_work(&mut self, work: BTreeMap<ComponentKey, SccWork>) {
        for (key, measured) in work {
            let total = self.scc_work.entry(key).or_default();
            total.cone_evaluations += measured.cone_evaluations;
            total.elapsed += measured.elapsed;
        }
    }
}
pub struct LocalCheckedReport<'p> {
    pub checked: CheckedReport<'p>,
    pub queries: BTreeMap<LocalScope, LocalArtifact>,
    pub metrics: LocalMetrics,
}
pub enum LocalCheckOutcome<'p> {
    Complete(LocalCheckedReport<'p>),
    Inconclusive {
        reason: Inconclusive,
        receipts: WorkReceipts,
    },
}

/// Exhaustive dispatch is deliberate: a future constraint variant cannot silently
/// inherit at-most-one's downward-closed, all-outside-inputs-absent extension.
pub fn validate_local_constraints(constraints: &[InputConstraint]) -> Result<()> {
    for constraint in constraints {
        match constraint {
            InputConstraint::AtMostOne { .. } => {}
        }
    }
    Ok(())
}
impl PreparedCheck<'_> {
    pub(super) fn local_input(
        &self,
        scope: LocalScope,
        cone: &DependencyCone,
        context: &ConditionContext,
    ) -> Result<LocalInput> {
        let atom =
            |a: &GroundAtom| AtomKey::from_atom(self.semantic_keys, a).map_err(CheckError::Keys);
        let components = cone
            .components
            .iter()
            .map(|id| {
                let c = self
                    .program
                    .component(*id)
                    .ok_or(CheckError::Internal("missing local component"))?;
                Ok((
                    self.keys.components[id].clone(),
                    LocalComponent {
                        recursive: c.recursive,
                        blocked_by: c
                            .blocked_by
                            .iter()
                            .map(|id| self.keys.components[id].clone())
                            .collect(),
                    },
                ))
            })
            .collect::<Result<_>>()?;
        // Original producer closure carries removed literals and dropped alternatives.
        // Include forwarding certificates too: their dependencies can leave the final cone.
        let mut needed = cone.facts.clone();
        let mut originals = BTreeMap::new();
        let mut rewrites = BTreeSet::new();
        loop {
            let before = (needed.len(), originals.len(), rewrites.len());
            for rule in self.program.original_rules() {
                if needed.contains(&rule.head.atom) {
                    let key = &self.keys.instances[&rule.id];
                    originals.insert(key.clone(), self.keys.content[key].clone());
                    needed.extend(rule.body.iter().map(|l| l.term.atom.clone()));
                }
            }
            for proof in self.program.rewrite_proofs() {
                if needed.contains(&proof.candidate.rule.head.atom) {
                    rewrites.insert(self.keys.rewrites[&proof.id].clone());
                    for producer in std::iter::once(&proof.candidate)
                        .chain(&proof.producers)
                        .chain(proof.upper_bounds.iter().flat_map(|b| b.producers.iter()))
                    {
                        needed.insert(producer.rule.head.atom.clone());
                        needed.extend(producer.rule.body.iter().map(|l| l.term.atom.clone()));
                    }
                }
            }
            if before == (needed.len(), originals.len(), rewrites.len()) {
                break;
            }
        }
        let facts = cone
            .facts
            .iter()
            .map(&atom)
            .collect::<Result<BTreeSet<_>>>()?;
        let inputs = cone
            .facts
            .intersection(&self.program.inputs)
            .map(&atom)
            .collect::<Result<BTreeSet<_>>>()?;
        let dependency_atoms = needed.iter().map(&atom).collect::<Result<Vec<_>>>()?;
        let sorts: BTreeSet<_> = dependency_atoms
            .iter()
            .flat_map(|a| a.arguments.iter().map(|c| c.sort.clone()))
            .collect();
        let relations: BTreeSet<_> = dependency_atoms
            .iter()
            .map(|a| a.relation.clone())
            .collect();
        let obligation = match &scope {
            LocalScope::Group(key) => {
                let domain = &self.keys.groups[&key.obligation];
                Some(LocalObligation {
                    relation: domain.relation.clone(),
                    group_by: domain.columns.clone(),
                    domains: domain.domains.clone(),
                })
            }
            LocalScope::Region(_) => None,
        };
        let completion_context = if matches!(scope, LocalScope::Region(_)) {
            let proofs = self
                .program
                .rewrite_proofs()
                .filter(|p| {
                    matches!(p.kind, RewriteKind::Discharge { .. })
                        && cone.rules.contains(&p.candidate.rule.id)
                })
                .collect::<Vec<_>>();
            if proofs.is_empty() {
                None
            } else {
                // Projection is fresh, like key construction. It copies already
                // certified formulas, not a new semantic check or hidden read.
                let limits = Limits {
                    max_work: usize::MAX,
                    max_bdd_nodes: usize::MAX,
                    max_bdd_variables: usize::MAX,
                    timeout: Duration::MAX,
                    ..Limits::default()
                };
                let mut budget = Budget::new(&limits);
                Some(LocalCompletionContext {
                    inputs: self
                        .program
                        .inputs
                        .iter()
                        .map(&atom)
                        .collect::<Result<_>>()?,
                    input_groups: self
                        .program
                        .input_groups
                        .iter()
                        .map(|g| g.iter().map(&atom).collect::<Result<_>>())
                        .collect::<Result<_>>()?,
                    proofs: proofs
                        .into_iter()
                        .map(|p| {
                            Ok((
                                self.keys.rewrites[&p.id].clone(),
                                (
                                    context.export(
                                        &p.candidate.condition,
                                        self.semantic_keys,
                                        &mut budget,
                                    )?,
                                    context.export(&p.coverage, self.semantic_keys, &mut budget)?,
                                ),
                            ))
                        })
                        .collect::<Result<_>>()?,
                })
            }
        } else {
            None
        };
        Ok(LocalInput {
            completion_context,
            obligation,
            scope,
            roots: cone.roots.iter().map(&atom).collect::<Result<_>>()?,
            facts,
            possible: cone
                .facts
                .iter()
                .filter(|a| self.program.atom_index.contains_key(*a))
                .map(&atom)
                .collect::<Result<_>>()?,
            inputs,
            components,
            rules: cone
                .rules
                .iter()
                .map(|id| {
                    let k = &self.keys.instances[id];
                    (k.clone(), self.keys.committed[k].clone())
                })
                .collect(),
            original_dependencies: originals,
            rewrites,
            domains: self
                .request
                .domains
                .iter()
                .filter(|(s, _)| sorts.contains(*s))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            constraints: self
                .request
                .constraints
                .iter()
                .filter(|c| match c {
                    InputConstraint::AtMostOne { relation, .. } => relations.contains(relation),
                })
                .cloned()
                .collect(),
            input_groups: self
                .program
                .input_groups
                .iter()
                .map(|g| {
                    g.iter()
                        .filter(|a| cone.facts.contains(*a))
                        .map(&atom)
                        .collect::<Result<BTreeSet<_>>>()
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .filter(|g| !g.is_empty())
                .collect(),
            request_scope: self.request.scope.clone(),
            backend: self.request.backend.clone(),
            limits: self.request.limits.clone(),
            admission_limit: self.program.admission_limit().map(Into::into),
        })
    }
}

/// Fully completed owned query pair. No physical execution metadata in equality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalMemo {
    pub evaluation: Option<LocalEvaluation>,
    pub answer: Option<LocalAnswer>,
    pub failure: Option<Inconclusive>,
    pub evaluation_receipt: WorkReceipt,
    pub answer_receipt: WorkReceipt,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedEvaluation {
    pub value: Option<std::sync::Arc<LocalEvaluation>>,
    pub failure: Option<Inconclusive>,
    pub receipt: WorkReceipt,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedAnswer {
    pub value: Option<LocalAnswer>,
    pub failure: Option<Inconclusive>,
    pub receipt: WorkReceipt,
}
/// Storage-neutral executor. The session runs the same owned functions through
/// tracked queries; the fresh driver executes them directly.
pub trait LocalMemoStore {
    fn execute(
        &mut self,
        input: &LocalInput,
        operations: &OperationalLimits,
        metrics: &mut LocalMetrics,
    ) -> Result<std::sync::Arc<LocalMemo>>;
}
pub struct NoLocalMemo;
impl LocalMemoStore for NoLocalMemo {
    fn execute(
        &mut self,
        input: &LocalInput,
        operations: &OperationalLimits,
        metrics: &mut LocalMetrics,
    ) -> Result<std::sync::Arc<LocalMemo>> {
        let evaluation = evaluate_owned_local(input, operations, metrics)?;
        let answer = answer_owned_local(
            input,
            evaluation.value.as_deref(),
            evaluation.failure,
            operations,
            metrics,
        )?;
        Ok(std::sync::Arc::new(LocalMemo {
            evaluation: evaluation.value.as_deref().cloned(),
            answer: answer.value,
            failure: answer.failure.or(evaluation.failure),
            evaluation_receipt: evaluation.receipt,
            answer_receipt: answer.receipt,
        }))
    }
}

impl LocalInput {
    pub fn uses_sat(&self) -> bool {
        self.backend == BackendIdentity::sat() && matches!(self.scope, LocalScope::Group(_))
    }

    /// Group verdicts consume conditions and scope, not producer implementation
    /// or attribution. Salsa can backdate this projection after equal evaluation.
    pub fn for_answer(&self) -> Self {
        let mut input = self.clone();
        if matches!(input.scope, LocalScope::Group(_)) && !input.uses_sat() {
            input.rules.clear();
            input.original_dependencies.clear();
            input.rewrites.clear();
            input.completion_context = None;
        }
        input
    }
}
