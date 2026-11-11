//! Derived semantic index over the committed ground round, with original instances
//! retained for provenance. Membership identities are not complete cache inputs.
use crate::*;
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomKey {
    pub relation: RelationKey,
    pub arguments: Vec<ConstantKey>,
}
impl AtomKey {
    pub fn from_atom(
        keys: &SemanticKeys,
        atom: &GroundAtom,
    ) -> std::result::Result<Self, KeyError> {
        Ok(Self {
            relation: keys.relation(atom.relation)?.clone(),
            arguments: atom
                .arguments
                .iter()
                .map(|c| keys.constant(*c).cloned())
                .collect::<std::result::Result<_, _>>()?,
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceKey {
    pub rule: RuleKey,
    /// Complete typed-variable order, including variables occurring only in body.
    pub substitution: Vec<(VariableKey, ConstantKey)>,
}
impl InstanceKey {
    pub(crate) fn from_rule(
        corpus: &Corpus,
        keys: &SemanticKeys,
        r: &GroundRule,
    ) -> std::result::Result<Self, KeyError> {
        let source = corpus
            .rule(r.source)
            .ok_or(KeyError::UnknownOccurrence(r.source.into()))?;
        if source.body.len() != r.body.len()
            || source.body.iter().zip(&r.body).any(|(a, b)| {
                matches!(a, Literal::Negative(_)) != (b.polarity == Polarity::Negative)
            })
        {
            return Err(KeyError::InvalidStructure(
                "original ground rule does not match source schema",
            ));
        }
        let mut substitution = BTreeMap::new();
        for (a, g) in std::iter::once((&source.head, &r.head)).chain(
            source
                .body
                .iter()
                .zip(&r.body)
                .map(|(a, b)| (a.atom(), &b.term)),
        ) {
            if a.id() != g.occurrence
                || a.relation() != g.atom.relation
                || a.arguments().len() != g.atom.arguments.len()
                || g.arguments != a.arguments().iter().map(|t| t.id()).collect::<Vec<_>>()
            {
                return Err(KeyError::InvalidStructure(
                    "ground/source occurrence mismatch",
                ));
            }
            for (t, c) in a.arguments().iter().zip(&g.atom.arguments) {
                let value = keys.constant(*c)?.clone();
                match t.value() {
                    Term::Constant(expected) if expected != c => {
                        return Err(KeyError::InvalidStructure("ground constant mismatch"));
                    }
                    Term::Constant(_) => {}
                    Term::Variable { name, sort } => {
                        let variable = VariableKey {
                            sort: keys.sort(*sort)?.clone(),
                            name: name.as_str().into(),
                        };
                        if variable.sort != value.sort {
                            return Err(KeyError::InvalidStructure(
                                "ground variable sort mismatch",
                            ));
                        }
                        if substitution
                            .insert(variable, value.clone())
                            .is_some_and(|old| old != value)
                        {
                            return Err(KeyError::InvalidStructure("inconsistent substitution"));
                        }
                    }
                }
            }
        }
        Ok(InstanceKey {
            rule: keys.rule(r.source)?.clone(),
            substitution: substitution.into_iter().collect(),
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ComponentKey(pub Arc<[AtomKey]>);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroupKey {
    pub obligation: ObligationKey,
    pub tuple: Vec<ConstantKey>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KeyedGroundOccurrence {
    pub atom: AtomKey,
    pub occurrence: OccurrenceKey,
    pub arguments: Vec<OccurrenceKey>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GroundInstance {
    pub schema: Arc<RuleSchema>,
    pub head: KeyedGroundOccurrence,
    pub body: Vec<(bool, KeyedGroundOccurrence)>,
}
/// Tracks empty and singleton groups without materializing a Cartesian product
/// of grouping domains. Every legal tuple has a GroupKey, even when not in members.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KeyedGroups {
    pub kind: Cardinality,
    pub relation: RelationKey,
    pub columns: Vec<usize>,
    pub domains: Vec<BTreeSet<ConstantKey>>,
    pub members: BTreeMap<Vec<ConstantKey>, BTreeSet<AtomKey>>,
}
impl KeyedGroups {
    pub fn key(
        &self,
        obligation: &ObligationKey,
        tuple: Vec<ConstantKey>,
    ) -> std::result::Result<GroupKey, KeyError> {
        if tuple.len() != self.domains.len()
            || tuple.iter().zip(&self.domains).any(|(v, d)| !d.contains(v))
        {
            return Err(KeyError::InvalidStructure("invalid grouping tuple"));
        }
        Ok(GroupKey {
            obligation: obligation.clone(),
            tuple,
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KeyedRewriteKind {
    Discharge(OccurrenceKey),
    RedundantProducer,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RewriteEvidenceKey {
    pub candidate: InstanceKey,
    pub kind: KeyedRewriteKind,
    pub producers: BTreeSet<InstanceKey>,
}
#[derive(Debug, Clone)]
pub struct GroundKeyIndex {
    pub(crate) core: Arc<GroundKeyCore>,
    pub groups: BTreeMap<ObligationKey, KeyedGroups>,
    pub elapsed: Duration,
}
#[derive(Debug, Clone)]
pub struct GroundKeyCore {
    /// Current executable content; original instances remain available for provenance.
    pub committed: BTreeMap<InstanceKey, GroundInstance>,
    pub dropped: BTreeSet<InstanceKey>,
    pub rewrites: BTreeMap<RewriteProofId, RewriteEvidenceKey>,
    pub atoms: BTreeMap<GroundAtom, AtomKey>,
    pub instances: BTreeMap<GroundRuleId, InstanceKey>,
    pub content: BTreeMap<InstanceKey, GroundInstance>,
    pub components: BTreeMap<ComponentId, ComponentKey>,
}
impl std::ops::Deref for GroundKeyIndex {
    type Target = GroundKeyCore;
    fn deref(&self) -> &GroundKeyCore {
        &self.core
    }
}
impl std::ops::DerefMut for GroundKeyIndex {
    fn deref_mut(&mut self) -> &mut GroundKeyCore {
        Arc::make_mut(&mut self.core)
    }
}
impl GroundKeyIndex {
    pub(crate) fn into_content(self) -> BTreeMap<InstanceKey, GroundInstance> {
        Arc::unwrap_or_clone(self.core).content
    }
    /// Index the committed round, retaining original instances for provenance.
    /// Key errors are creator failures, separate from resource exhaustion. The
    /// key phase adds no logical charges to existing preparation/check budgets.
    pub fn build(
        corpus: &Corpus,
        keys: &SemanticKeys,
        program: &GroundProgram,
    ) -> std::result::Result<Self, KeyError> {
        let start = Instant::now();
        keys.validate(corpus)?;
        let mut out = Self {
            core: Arc::new(GroundKeyCore {
                committed: BTreeMap::new(),
                dropped: BTreeSet::new(),
                rewrites: BTreeMap::new(),
                atoms: BTreeMap::new(),
                instances: BTreeMap::new(),
                content: BTreeMap::new(),
                components: BTreeMap::new(),
            }),
            groups: BTreeMap::new(),
            elapsed: Duration::ZERO,
        };
        let core = Arc::get_mut(&mut out.core).unwrap();
        // Include impossible negative premises too; they have identity but no SCC.
        for atom in program.atoms().chain(
            program
                .original_rules()
                .flat_map(|r| r.body.iter().map(|l| &l.term.atom)),
        ) {
            if !core.atoms.contains_key(atom) {
                core.atoms
                    .insert(atom.clone(), AtomKey::from_atom(keys, atom)?);
            }
        }
        let schemas: BTreeMap<_, _> = corpus
            .rules()
            .map(|r| Ok((r.id, Arc::new(keys.rule_schema(r)?))))
            .collect::<std::result::Result<_, KeyError>>()?;
        let occurrence =
            |g: &GroundOccurrence| -> std::result::Result<KeyedGroundOccurrence, KeyError> {
                Ok(KeyedGroundOccurrence {
                    atom: AtomKey::from_atom(keys, &g.atom)?,
                    occurrence: keys.bindings().key(g.occurrence)?.clone(),
                    arguments: g
                        .arguments
                        .iter()
                        .map(|id| keys.bindings().key(*id).cloned())
                        .collect::<std::result::Result<_, _>>()?,
                })
            };
        for r in program.original_rules() {
            let key = InstanceKey::from_rule(corpus, keys, r)?;
            let value = GroundInstance {
                schema: schemas[&r.source].clone(),
                head: occurrence(&r.head)?,
                body: r
                    .body
                    .iter()
                    .map(|l| Ok((l.polarity == Polarity::Negative, occurrence(&l.term)?)))
                    .collect::<std::result::Result<_, KeyError>>()?,
            };
            if core.content.insert(key.clone(), value).is_some() {
                return Err(KeyError::InvalidStructure("duplicate ground instance key"));
            }
            core.instances.insert(r.id, key);
        }
        for r in program.rules() {
            let key = core.instances[&r.id].clone();
            core.committed.insert(
                key.clone(),
                GroundInstance {
                    schema: core.content[&key].schema.clone(),
                    head: occurrence(&r.head)?,
                    body: r
                        .body
                        .iter()
                        .map(|l| Ok((l.polarity == Polarity::Negative, occurrence(&l.term)?)))
                        .collect::<std::result::Result<_, KeyError>>()?,
                },
            );
        }
        core.dropped = core
            .content
            .keys()
            .filter(|k| !core.committed.contains_key(*k))
            .cloned()
            .collect();
        for proof in program.rewrite_proofs() {
            core.rewrites.insert(
                proof.id,
                RewriteEvidenceKey {
                    candidate: core.instances[&proof.candidate.rule.id].clone(),
                    kind: match proof.kind {
                        RewriteKind::Discharge { literal_occurrence } => {
                            KeyedRewriteKind::Discharge(
                                keys.bindings().key(literal_occurrence)?.clone(),
                            )
                        }
                        RewriteKind::RedundantProducer => KeyedRewriteKind::RedundantProducer,
                    },
                    producers: proof
                        .producers
                        .iter()
                        .map(|p| core.instances[&p.rule.id].clone())
                        .collect(),
                },
            );
        }
        for c in program.components() {
            let atoms: BTreeSet<_> = c.atoms.iter().map(|a| core.atoms[a].clone()).collect();
            core.components.insert(
                c.id,
                ComponentKey(atoms.into_iter().collect::<Vec<_>>().into()),
            );
        }
        out.build_groups(corpus, keys, program)?;
        out.elapsed = start.elapsed();
        Ok(out)
    }
    pub(crate) fn build_groups(
        &mut self,
        corpus: &Corpus,
        keys: &SemanticKeys,
        program: &GroundProgram,
    ) -> std::result::Result<(), KeyError> {
        self.groups.clear();
        for o in corpus
            .obligations()
            .filter(|o| program.obligations.contains(&o.id))
        {
            if o.requirement.kind() == denotate_ir::Cardinality::Empty {
                continue;
            }
            let relation = &o.requirement.relation();
            let group_by = o.requirement.group_by();
            let signature = corpus
                .relation(*relation)
                .ok_or(KeyError::UnknownOccurrence((*relation).into()))?;
            let mut domains = Vec::new();
            for column in group_by {
                domains.push(
                    program
                        .domain(signature.parameters[*column].sort)
                        .ok_or(KeyError::InvalidStructure("missing grouping domain"))?
                        .iter()
                        .map(|c| keys.constant(*c).cloned())
                        .collect::<std::result::Result<_, _>>()?,
                );
            }
            let mut groups = KeyedGroups {
                kind: o.requirement.kind(),
                relation: keys.relation(*relation)?.clone(),
                columns: group_by.to_vec(),
                domains,
                members: BTreeMap::new(),
            };
            for a in program.atoms().filter(|a| a.relation == *relation) {
                let atom = &self.atoms[a];
                let tuple = group_by
                    .iter()
                    .map(|i| atom.arguments[*i].clone())
                    .collect();
                groups
                    .members
                    .entry(tuple)
                    .or_default()
                    .insert(atom.clone());
            }
            self.groups.insert(keys.obligation(o.id)?.clone(), groups);
        }
        Ok(())
    }
}

/// Frontend-owned pairing: no semantic index is smuggled into Corpus/BDD IDs.
pub struct KeyedPreparation {
    pub program: GroundProgram,
    pub keys: GroundKeyIndex,
}
