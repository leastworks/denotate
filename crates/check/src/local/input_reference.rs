//! Pre-index construction (e0aa115) retained only as an equality oracle.
//! Keep its full scans independent of the production index/worklist.
use super::*;

impl PreparedCheck<'_> {
    pub fn local_input_scanning_reference(
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
                    self.key_view().component(*id)?,
                    LocalComponent {
                        recursive: c.recursive,
                        blocked_by: c
                            .blocked_by
                            .iter()
                            .map(|id| self.key_view().component(*id))
                            .collect::<Result<_>>()?,
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
                    let key = self.key_view().instance(rule.id)?;
                    originals.insert(key, self.key_view().original(rule.id)?);
                    needed.extend(rule.body.iter().map(|l| l.term.atom.clone()));
                }
            }
            for proof in self.program.rewrite_proofs() {
                if needed.contains(&proof.candidate().head.atom) {
                    rewrites.insert(self.key_view().rewrite(proof.id)?);
                    for producer in proof.summaries() {
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
                        && cone.rules.contains(&p.candidate().id)
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
                                self.key_view().rewrite(p.id)?,
                                (
                                    context.export(
                                        &p.symbolic().expect("discharge").candidate.condition,
                                        self.semantic_keys,
                                        &mut budget,
                                    )?,
                                    context.export(
                                        &p.symbolic().expect("discharge").coverage,
                                        self.semantic_keys,
                                        &mut budget,
                                    )?,
                                ),
                            ))
                        })
                        .collect::<Result<_>>()?,
                })
            }
        } else {
            None
        };
        let input_order = self.local_variable_order(cone, context, completion_context.is_some())?;
        Ok(LocalInput {
            input_order,
            completion_context,
            obligation,
            scope,
            roots: cone.roots.iter().map(&atom).collect::<Result<_>>()?,
            facts,
            possible: cone
                .facts
                .iter()
                .filter(|a| {
                    self.program.atom_index.contains_key(*a)
                        || self.program.fixed_value(a).is_some()
                })
                .map(&atom)
                .collect::<Result<_>>()?,
            inputs,
            components,
            rules: cone
                .rules
                .iter()
                .map(|id| {
                    Ok((
                        self.key_view().instance(*id)?,
                        self.key_view().committed(*id)?,
                    ))
                })
                .collect::<Result<_>>()?,
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
                    InputConstraint::AtMostOne { relation, .. }
                    | InputConstraint::Cardinality { relation, .. } => relations.contains(relation),
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
