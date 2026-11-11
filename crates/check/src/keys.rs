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
impl ComponentKey {
    pub fn from_component(
        program: &GroundProgram,
        keys: &SemanticKeys,
        id: ComponentId,
    ) -> Result<Self> {
        let component = program
            .component(id)
            .ok_or(CheckError::Internal("missing committed component"))?;
        Ok(Self(
            component
                .atoms
                .iter()
                .map(|a| AtomKey::from_atom(keys, a).map_err(CheckError::Keys))
                .collect::<Result<BTreeSet<_>>>()?
                .into_iter()
                .collect::<Vec<_>>()
                .into(),
        ))
    }
}
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
/// Source schemas shared by every request and admitted view of this snapshot.
/// Ground bodies already live in GroundProgram; never retain keyed copies here.
#[derive(Debug)]
pub struct GroundKeyCore {
    schemas: BTreeMap<RuleId, Arc<RuleSchema>>,
    relations: BTreeMap<RelationKey, RelationId>,
    constants: BTreeMap<ConstantKey, ConstantId>,
}
impl GroundKeyIndex {
    /// Index source schemas and selected groups, without expanding ground instances.
    /// Checked ground programs already enforce instance uniqueness and typed binding.
    pub fn build(
        corpus: &Corpus,
        keys: &SemanticKeys,
        program: &GroundProgram,
    ) -> std::result::Result<Self, KeyError> {
        Self::build_shared(corpus, keys, program, None)
    }
    pub(crate) fn build_shared(
        corpus: &Corpus,
        keys: &SemanticKeys,
        program: &GroundProgram,
        shared: Option<Arc<GroundKeyCore>>,
    ) -> std::result::Result<Self, KeyError> {
        let start = Instant::now();
        keys.validate(corpus)?;
        // GroundProgram is constructed only by the checked grounding paths.
        // Validate its snapshot even when no consumer requests an instance.
        for relation in program.signatures.keys() {
            keys.relation(*relation)?;
        }
        for (sort, domain) in &program.domains {
            keys.sort(*sort)?;
            for constant in domain {
                keys.constant(*constant)?;
            }
        }
        let core = if let Some(core) = shared {
            core
        } else {
            Arc::new(GroundKeyCore {
                relations: corpus
                    .relations()
                    .map(|r| Ok((keys.relation(r.id)?.clone(), r.id)))
                    .collect::<std::result::Result<_, KeyError>>()?,
                constants: corpus
                    .constants()
                    .map(|c| Ok((keys.constant(c.id)?.clone(), c.id)))
                    .collect::<std::result::Result<_, KeyError>>()?,
                schemas: corpus
                    .rules()
                    .map(|r| Ok((r.id, Arc::new(keys.rule_schema(r)?))))
                    .collect::<std::result::Result<_, KeyError>>()?,
            })
        };
        let mut out = Self {
            core,
            groups: BTreeMap::new(),
            elapsed: Duration::ZERO,
        };
        out.build_groups(corpus, keys, program)?;
        out.elapsed = start.elapsed();
        Ok(out)
    }
    /// Explicit projection from the current snapshot and admitted graph. The view
    /// holds no cache: owned outputs contain stable keys and complete structure.
    pub fn view<'a>(
        &'a self,
        corpus: &'a Corpus,
        keys: &'a SemanticKeys,
        program: &'a GroundProgram,
    ) -> GroundKeyView<'a> {
        GroundKeyView {
            index: self,
            corpus,
            keys,
            program,
        }
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
                let atom = AtomKey::from_atom(keys, a)?;
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

/// On-demand semantic projection. Original and committed bodies are read from
/// the graph's original-rule storage and rewrite overlay respectively.
#[derive(Clone, Copy)]
pub struct GroundKeyView<'a> {
    index: &'a GroundKeyIndex,
    corpus: &'a Corpus,
    keys: &'a SemanticKeys,
    program: &'a GroundProgram,
}
impl GroundKeyView<'_> {
    pub fn atom(&self, atom: &GroundAtom) -> Result<AtomKey> {
        AtomKey::from_atom(self.keys, atom).map_err(CheckError::Keys)
    }
    pub fn instance(&self, id: GroundRuleId) -> Result<InstanceKey> {
        let rule = self
            .program
            .original_rule(id)
            .ok_or(CheckError::Internal("missing original ground rule"))?;
        InstanceKey::from_rule(self.corpus, self.keys, rule).map_err(CheckError::Keys)
    }
    fn occurrence(&self, g: &GroundOccurrence) -> Result<KeyedGroundOccurrence> {
        Ok(KeyedGroundOccurrence {
            atom: self.atom(&g.atom)?,
            occurrence: self
                .keys
                .bindings()
                .key(g.occurrence)
                .map_err(CheckError::Keys)?
                .clone(),
            arguments: g
                .arguments
                .iter()
                .map(|id| {
                    self.keys
                        .bindings()
                        .key(*id)
                        .cloned()
                        .map_err(CheckError::Keys)
                })
                .collect::<Result<_>>()?,
        })
    }
    fn body(&self, rule: &GroundRule) -> Result<GroundInstance> {
        Ok(GroundInstance {
            schema: self
                .index
                .core
                .schemas
                .get(&rule.source)
                .ok_or(CheckError::Internal("missing source schema"))?
                .clone(),
            head: self.occurrence(&rule.head)?,
            body: rule
                .body
                .iter()
                .map(|l| Ok((l.polarity == Polarity::Negative, self.occurrence(&l.term)?)))
                .collect::<Result<_>>()?,
        })
    }
    pub fn original(&self, id: GroundRuleId) -> Result<GroundInstance> {
        self.body(
            self.program
                .original_rule(id)
                .ok_or(CheckError::Internal("missing original ground rule"))?,
        )
    }
    pub fn committed(&self, id: GroundRuleId) -> Result<GroundInstance> {
        self.body(
            self.program
                .rule(id)
                .ok_or(CheckError::Internal("missing committed ground rule"))?,
        )
    }
    pub fn component(&self, id: ComponentId) -> Result<ComponentKey> {
        ComponentKey::from_component(self.program, self.keys, id)
    }
    pub fn bind_atom(&self, key: &AtomKey) -> Result<GroundAtom> {
        let relation = self
            .index
            .core
            .relations
            .get(&key.relation)
            .ok_or(CheckError::Internal("missing current relation"))?;
        let arguments = key
            .arguments
            .iter()
            .map(|c| {
                self.index
                    .core
                    .constants
                    .get(c)
                    .copied()
                    .ok_or(CheckError::Internal("missing current constant"))
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(GroundAtom::new(*relation, arguments))
    }
    pub fn bind_component(&self, key: &ComponentKey) -> Result<ComponentId> {
        let first = key
            .0
            .first()
            .ok_or(CheckError::Internal("empty component key"))?;
        let component = self.program.component_for(&self.bind_atom(first)?)?;
        if self.component(component.id)? != *key {
            return Err(CheckError::Internal("component membership changed"));
        }
        Ok(component.id)
    }
    pub fn rewrite(&self, id: RewriteProofId) -> Result<RewriteEvidenceKey> {
        let proof = self
            .program
            .rewrite_proof(id)
            .ok_or(CheckError::Internal("missing rewrite proof"))?;
        Ok(RewriteEvidenceKey {
            candidate: self.instance(proof.candidate.rule.id)?,
            kind: match proof.kind {
                RewriteKind::Discharge { literal_occurrence } => KeyedRewriteKind::Discharge(
                    self.keys
                        .bindings()
                        .key(literal_occurrence)
                        .map_err(CheckError::Keys)?
                        .clone(),
                ),
                RewriteKind::RedundantProducer => KeyedRewriteKind::RedundantProducer,
            },
            producers: proof
                .producers
                .iter()
                .map(|p| self.instance(p.rule.id))
                .collect::<Result<_>>()?,
        })
    }
    pub fn rewrites(&self) -> Result<BTreeMap<RewriteProofId, RewriteEvidenceKey>> {
        self.program
            .rewrite_proofs()
            .map(|p| Ok((p.id, self.rewrite(p.id)?)))
            .collect()
    }
    /// Explicit full export for the optional relation-grounding cache and structural
    /// comparisons. Normal preparation, admission and findings never call this.
    pub fn original_content(&self) -> Result<BTreeMap<InstanceKey, GroundInstance>> {
        self.program
            .original_rules()
            .map(|r| Ok((self.instance(r.id)?, self.original(r.id)?)))
            .collect()
    }
}

/// Frontend-owned pairing: no semantic index is smuggled into Corpus/BDD IDs.
pub struct KeyedPreparation {
    pub program: GroundProgram,
    pub keys: GroundKeyIndex,
}
