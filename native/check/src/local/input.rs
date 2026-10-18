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
    pub admission_limit: Option<ResourceReason>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalEvaluation {
    pub permitted: OwnedCondition,
    pub conditions: BTreeMap<AtomKey, OwnedCondition>,
    pub incomplete: BTreeMap<ComponentKey, ResourceReason>,
}
/// Overlap is a candidate condition, not a certified Counterexample. Replay stays fresh.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalVerdict {
    Proved,
    Overlap(OwnedCondition),
    Unsupported(CapabilityReason),
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
        Ok(LocalInput {
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
    pub(super) fn own_completion(
        &self,
        completion: &CompletionOutcome,
        context: &ConditionContext,
        budget: &mut Budget<'_>,
        export_time: &mut Duration,
    ) -> Result<LocalAnswer> {
        let atom =
            |a: &GroundAtom| AtomKey::from_atom(self.semantic_keys, a).map_err(CheckError::Keys);
        let mut bad_input = None;
        let mut boundary = BTreeMap::new();
        let outcome = match completion {
            CompletionOutcome::NoContradiction => RegionCompletion::NoContradiction,
            CompletionOutcome::Inconclusive(c) => RegionCompletion::Inconclusive((*c).into()),
            CompletionOutcome::Deferred { blocked_by } => RegionCompletion::Deferred(
                blocked_by
                    .iter()
                    .map(|id| self.keys.components[id].clone())
                    .collect(),
            ),
            CompletionOutcome::NoMeaning(f) => {
                let mut evidence = EvidenceKeys::default();
                for r in &f.rules {
                    self.rule_evidence(r, self.semantic_keys, &mut evidence)?;
                }
                for id in &f.rewrites {
                    evidence.rewrites.insert(self.keys.rewrites[id].clone());
                }
                for (a, b) in &f.upstream {
                    boundary.insert(
                        atom(a)?,
                        timed_export(
                            context,
                            &b.condition,
                            self.semantic_keys,
                            budget,
                            export_time,
                        )?,
                    );
                    if let CompletedProvider::Component(id) = b.provider {
                        evidence.providers.insert(self.keys.components[&id].clone());
                    }
                }
                bad_input = Some(timed_export(
                    context,
                    &f.bad_input,
                    self.semantic_keys,
                    budget,
                    export_time,
                )?);
                RegionCompletion::NoMeaning {
                    candidate: Candidate {
                        present: f
                            .observation
                            .present
                            .iter()
                            .map(&atom)
                            .collect::<Result<_>>()?,
                        absent: f
                            .observation
                            .absent
                            .iter()
                            .map(&atom)
                            .collect::<Result<_>>()?,
                    },
                    evidence,
                }
            }
        };
        Ok(LocalAnswer::Completion {
            outcome,
            bad_input,
            boundary,
        })
    }
}

/// Fully completed local query pair. Logical charges survive value eviction.
/// Only owned semantic values cross this boundary; presentation remains current.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalMemo {
    /// A proof that component-order changes preserve storage peaks, not just truth.
    pub reorder_safe: bool,
    pub evaluation: Option<LocalEvaluation>,
    pub answer: Option<LocalAnswer>,
    pub failure: Option<Inconclusive>,
    pub evaluation_receipt: WorkReceipt,
    pub answer_receipt: WorkReceipt,
}
/// The checker does not depend on a storage engine. A session validates structural
/// inputs and supplies only fully completed query pairs from the same boundary.
pub trait LocalMemoStore {
    fn get(
        &mut self,
        input: &LocalInput,
        work: &LocalWorkInput,
    ) -> Option<std::sync::Arc<LocalMemo>>;
    fn put(&mut self, input: &LocalInput, work: &LocalWorkInput, value: std::sync::Arc<LocalMemo>);
}
pub struct NoLocalMemo;
impl LocalMemoStore for NoLocalMemo {
    fn get(&mut self, _: &LocalInput, _: &LocalWorkInput) -> Option<std::sync::Arc<LocalMemo>> {
        None
    }
    fn put(&mut self, _: &LocalInput, _: &LocalWorkInput, _: std::sync::Arc<LocalMemo>) {}
}

/// Execution order and fresh discovery charges are receipt dependencies, even
/// when semantic inputs compare equal. No arena IDs are retained here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalWorkInput {
    pub discovery: WorkCharges,
    pub components: Vec<(ComponentKey, Vec<AtomKey>, Vec<InstanceKey>)>,
    pub completion_rewrite_scan: usize,
    pub fact_order: Vec<AtomKey>,
    pub completion: Option<CompletionWorkInput>,
}
/// Completion's scoped replay still scans global rules/components and validates
/// global W. These are accounting dependencies, separate from projected semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionWorkInput {
    pub rules_scanned: usize,
    pub component_gaps: Vec<usize>,
    pub constraint_sizes: Vec<usize>,
    pub discharge_context: Option<DischargeWorkInput>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DischargeWorkInput {
    pub inputs: Vec<AtomKey>,
    pub groups: Vec<Vec<AtomKey>>,
    pub proofs: Vec<(RewriteEvidenceKey, Vec<u8>, Vec<u8>)>,
}
impl PreparedCheck<'_> {
    pub(super) fn local_work_input(
        &self,
        cone: &DependencyCone,
        discovery: WorkCharges,
        region: bool,
    ) -> LocalWorkInput {
        let fact_order = cone
            .facts
            .iter()
            .map(|a| self.keys.atoms[a].clone())
            .collect();
        let completion = region.then(|| {
            let mut last = 0;
            let mut gaps = Vec::new();
            for id in &cone.components {
                gaps.push(id.index - last);
                last = id.index + 1;
            }
            gaps.push(self.program.components.len() - last);
            let proofs: Vec<_> = self
                .program
                .rewrite_proofs()
                .filter(|p| {
                    matches!(p.kind, RewriteKind::Discharge { .. })
                        && cone.rules.contains(&p.candidate.rule.id)
                })
                .map(|p| {
                    (
                        self.keys.rewrites[&p.id].clone(),
                        p.candidate.condition.accounting_graph(),
                        p.coverage.accounting_graph(),
                    )
                })
                .collect();
            let discharge_context = (!proofs.is_empty()).then(|| DischargeWorkInput {
                inputs: self
                    .program
                    .input_order
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(|a| self.keys.atoms[a].clone())
                    .collect(),
                groups: self
                    .program
                    .input_groups
                    .iter()
                    .map(|g| g.iter().map(|a| self.keys.atoms[a].clone()).collect())
                    .collect(),
                proofs,
            });
            CompletionWorkInput {
                rules_scanned: self.program.rules.len(),
                component_gaps: gaps,
                constraint_sizes: self.program.input_groups.iter().map(Vec::len).collect(),
                discharge_context,
            }
        });
        LocalWorkInput {
            discovery,
            fact_order,
            completion,
            components: cone
                .components
                .iter()
                .map(|id| &self.program.components[id.index])
                .map(|c| {
                    (
                        self.keys.components[&c.id].clone(),
                        c.atoms.iter().map(|a| self.keys.atoms[a].clone()).collect(),
                        self.program.component_rules[c.id.index]
                            .iter()
                            .map(|r| self.keys.instances[&self.program.rules[*r].id].clone())
                            .collect(),
                    )
                })
                .collect(),
            completion_rewrite_scan: if region {
                self.program.rewrite_proofs().count()
            } else {
                0
            },
        }
    }
}

impl LocalWorkInput {
    pub fn same_component_work(&self, other: &Self) -> bool {
        self.discovery == other.discovery
            && self.completion == other.completion
            && self.completion_rewrite_scan == other.completion_rewrite_scan
            && self
                .components
                .iter()
                .map(|(k, a, r)| (k, (a, r)))
                .collect::<BTreeMap<_, _>>()
                == other
                    .components
                    .iter()
                    .map(|(k, a, r)| (k, (a, r)))
                    .collect::<BTreeMap<_, _>>()
    }
}
