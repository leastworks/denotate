//! Owned semantic identities beside a Corpus. Frontends supply identity; this
//! module never infers owners from display names. No persisted encoding contract.
use crate::*;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OwnerKey {
    namespace: Arc<str>,
    value: Arc<[u8]>,
}
impl OwnerKey {
    pub fn new(namespace: impl Into<Arc<str>>, value: impl Into<Arc<[u8]>>) -> Self {
        Self {
            namespace: namespace.into(),
            value: value.into(),
        }
    }
    pub fn namespace(&self) -> &str {
        &self.namespace
    }
    pub fn value(&self) -> &[u8] {
        &self.value
    }
}
// Most comparisons within a snapshot share an immutable owner allocation.
// This shortcut only proves equality; independently allocated owners still use
// full structural comparison, with exactly the same order and hash semantics.
impl Ord for OwnerKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.namespace.cmp(&other.namespace).then_with(|| {
            if Arc::ptr_eq(&self.value, &other.value) {
                std::cmp::Ordering::Equal
            } else {
                self.value.cmp(&other.value)
            }
        })
    }
}
impl PartialOrd for OwnerKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QualifiedKey {
    pub namespace: Arc<str>,
    pub name: Arc<str>,
}
impl QualifiedKey {
    pub fn new(namespace: impl Into<Arc<str>>, name: impl Into<Arc<str>>) -> Self {
        Self {
            namespace: namespace.into(),
            name: name.into(),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortKey(pub QualifiedKey);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstantKey {
    pub sort: SortKey,
    pub name: Arc<str>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RelationKey {
    Named(QualifiedKey),
    Generated { owner: OwnerKey, local: usize },
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleKey {
    Installed { owner: OwnerKey, local: usize },
    Library(QualifiedKey),
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObligationKey(pub QualifiedKey);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssumptionKey(pub QualifiedKey);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VerificationKey(pub QualifiedKey);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OccurrenceKey {
    Sort(SortKey),
    Constant(ConstantKey),
    Relation(RelationKey),
    Rule(RuleKey),
    Obligation(ObligationKey),
    Assumption(AssumptionKey),
    Verification(VerificationKey),
    Installed {
        owner: OwnerKey,
        local: usize,
    },
    /// Position within one library rule: head first, then body atoms; None is
    /// the atom occurrence, Some is its argument occurrence.
    Library {
        rule: RuleKey,
        atom: usize,
        argument: Option<usize>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyError {
    UnknownOccurrence(OccurrenceId),
    MissingBinding(OccurrenceId),
    MissingKey(OccurrenceKey),
    DuplicateKey(OccurrenceKey),
    DuplicateOccurrence(OccurrenceId),
    InvalidKind(OccurrenceId),
    InvalidStructure(&'static str),
}
impl std::fmt::Display for KeyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid semantic binding: {self:?}")
    }
}
impl std::error::Error for KeyError {}
type Result<T> = std::result::Result<T, KeyError>;

/// Checked bijection for this snapshot, separate from semantic equality and
/// many-to-many source provenance. Rebinding resolves an occurrence here, then
/// reads its current Provenance/attribution. Errors are creator failures.
#[derive(Debug, Default)]
pub struct CurrentBindings {
    forward: BTreeMap<OccurrenceKey, OccurrenceId>,
    reverse: BTreeMap<OccurrenceId, OccurrenceKey>,
}
impl CurrentBindings {
    pub fn bind(
        &mut self,
        corpus: &Corpus,
        key: OccurrenceKey,
        id: impl Into<OccurrenceId>,
    ) -> Result<()> {
        let id = id.into();
        if !corpus.contains_occurrence(id) {
            return Err(KeyError::UnknownOccurrence(id));
        }
        if self.forward.contains_key(&key) {
            return Err(KeyError::DuplicateKey(key));
        }
        if self.reverse.contains_key(&id) {
            return Err(KeyError::DuplicateOccurrence(id));
        }
        self.forward.insert(key.clone(), id);
        self.reverse.insert(id, key);
        Ok(())
    }
    pub fn resolve(&self, key: &OccurrenceKey) -> Result<OccurrenceId> {
        self.forward
            .get(key)
            .copied()
            .ok_or_else(|| KeyError::MissingKey(key.clone()))
    }
    pub fn key(&self, id: impl Into<OccurrenceId>) -> Result<&OccurrenceKey> {
        let id = id.into();
        self.reverse.get(&id).ok_or(KeyError::MissingBinding(id))
    }
    pub fn entries(&self) -> impl Iterator<Item = (&OccurrenceKey, OccurrenceId)> {
        self.forward.iter().map(|(k, v)| (k, *v))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableKey {
    pub sort: SortKey,
    pub name: Arc<str>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TermKey {
    Constant(ConstantKey),
    Variable(VariableKey),
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomSchema {
    pub relation: RelationKey,
    pub occurrence: OccurrenceKey,
    pub arguments: Vec<(OccurrenceKey, TermKey)>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleSchema {
    pub head: AtomSchema,
    /// Ordered occurrences, including duplicates. true means negative.
    pub body: Vec<(bool, AtomSchema)>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RelationSchema {
    pub input: bool,
    pub parameters: Vec<(Arc<str>, SortKey)>,
}

/// Installation side table. Typed declarations and rules share the same checked
/// occurrence bijection. Internal Corpus IDs and allocation order are untouched.
#[derive(Debug, Default)]
pub struct SemanticKeys {
    bindings: CurrentBindings,
}
macro_rules! accessors {
    ($($get:ident, $bind:ident, $id:ty, $key:ty, $variant:ident, $lookup:ident;)*) => {$(
        pub fn $get(&self, id: $id) -> Result<&$key> {
            match self.bindings.key(id)? {
                OccurrenceKey::$variant(k) => Ok(k),
                _ => Err(KeyError::InvalidKind(id.into())),
            }
        }
        pub fn $bind(&mut self, corpus: &Corpus, id: $id, key: $key) -> Result<()> {
            if corpus.$lookup(id).is_none() { return Err(KeyError::UnknownOccurrence(id.into())); }
            self.bindings.bind(corpus, OccurrenceKey::$variant(key), id)
        }
    )*};
}
impl SemanticKeys {
    pub fn bindings(&self) -> &CurrentBindings {
        &self.bindings
    }
    accessors! {
        sort, bind_sort, SortId, SortKey, Sort, sort;
        constant, bind_constant, ConstantId, ConstantKey, Constant, constant;
        relation, bind_relation, RelationId, RelationKey, Relation, relation;
        rule, bind_rule, RuleId, RuleKey, Rule, rule;
        obligation, bind_obligation, ObligationId, ObligationKey, Obligation, obligation;
        assumption, bind_assumption, AssumptionId, AssumptionKey, Assumption, assumption;
        verification, bind_verification, VerificationId, VerificationKey, Verification, verification;
    }
    pub fn bind_occurrence(
        &mut self,
        corpus: &Corpus,
        id: OccurrenceId,
        key: OccurrenceKey,
    ) -> Result<()> {
        // Typed declarations/rules must use the corresponding typed methods.
        if !matches!(
            key,
            OccurrenceKey::Installed { .. } | OccurrenceKey::Library { .. }
        ) {
            return Err(KeyError::InvalidKind(id));
        }
        self.bindings.bind(corpus, key, id)
    }
    pub fn atom_schema(&self, atom: &Atom) -> Result<AtomSchema> {
        Ok(AtomSchema {
            relation: self.relation(atom.relation())?.clone(),
            occurrence: self.bindings.key(atom.id())?.clone(),
            arguments: atom
                .arguments()
                .iter()
                .map(|a| {
                    Ok((
                        self.bindings.key(a.id())?.clone(),
                        match a.value() {
                            Term::Constant(c) => TermKey::Constant(self.constant(*c)?.clone()),
                            Term::Variable { name, sort } => TermKey::Variable(VariableKey {
                                sort: self.sort(*sort)?.clone(),
                                name: name.as_str().into(),
                            }),
                        },
                    ))
                })
                .collect::<Result<_>>()?,
        })
    }
    pub fn rule_schema(&self, rule: &Rule) -> Result<RuleSchema> {
        self.rule(rule.id)?;
        Ok(RuleSchema {
            head: self.atom_schema(&rule.head)?,
            body: rule
                .body
                .iter()
                .map(|l| {
                    Ok((
                        matches!(l, Literal::Negative(_)),
                        self.atom_schema(l.atom())?,
                    ))
                })
                .collect::<Result<_>>()?,
        })
    }
    pub fn relation_schema(&self, relation: &Relation) -> Result<RelationSchema> {
        self.relation(relation.id)?;
        Ok(RelationSchema {
            input: relation.role == RelationRole::Input,
            parameters: relation
                .parameters
                .iter()
                .map(|p| Ok((p.name.as_str().into(), self.sort(p.sort)?.clone())))
                .collect::<Result<_>>()?,
        })
    }
    /// Validate complete coverage and correct typed declaration bindings. A table
    /// from a different Corpus is rejected even when all semantic keys are equal.
    pub fn validate(&self, corpus: &Corpus) -> Result<()> {
        for (_, id) in self.bindings.entries() {
            if !corpus.contains_occurrence(id) {
                return Err(KeyError::UnknownOccurrence(id));
            }
        }
        for s in corpus.sorts() {
            self.sort(s.id)?;
        }
        for c in corpus.constants() {
            if self.constant(c.id)?.sort != *self.sort(c.sort)? {
                return Err(KeyError::InvalidKind(c.id.into()));
            }
        }
        for r in corpus.relations() {
            let generated = matches!(self.relation(r.id)?, RelationKey::Generated { .. });
            if generated != corpus.is_generated_relation(r.id) {
                return Err(KeyError::InvalidKind(r.id.into()));
            }
            for p in &r.parameters {
                self.sort(p.sort)?;
            }
        }
        for r in corpus.rules() {
            self.rule(r.id)?;
            for a in std::iter::once(&r.head).chain(r.body.iter().map(Literal::atom)) {
                if !matches!(
                    self.bindings.key(a.id())?,
                    OccurrenceKey::Installed { .. } | OccurrenceKey::Library { .. }
                ) {
                    return Err(KeyError::InvalidKind(a.id()));
                }
                for t in a.arguments() {
                    if !matches!(
                        self.bindings.key(t.id())?,
                        OccurrenceKey::Installed { .. } | OccurrenceKey::Library { .. }
                    ) {
                        return Err(KeyError::InvalidKind(t.id()));
                    }
                }
            }
        }
        for o in corpus.obligations() {
            self.obligation(o.id)?;
        }
        for a in corpus.assumptions() {
            self.assumption(a.id)?;
        }
        for v in corpus.verifications() {
            self.verification(v.id)?;
        }
        Ok(())
    }
}
