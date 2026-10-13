use crate::ids::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructionError {
    EmptyName(&'static str),
    DuplicateName {
        kind: &'static str,
        name: String,
    },
    UnknownSort(SortId),
    UnknownConstant(ConstantId),
    UnknownRelation(RelationId),
    ForeignAtom(OccurrenceId),
    Arity {
        relation: RelationId,
        expected: usize,
        actual: usize,
    },
    SortMismatch {
        relation: RelationId,
        argument: usize,
        expected: SortId,
        actual: SortId,
    },
    VariableSortConflict {
        name: String,
        expected: SortId,
        actual: SortId,
    },
    UnsafeVariable {
        name: String,
        occurrence: OccurrenceId,
    },
    InputDefinition(RelationId),
    InvalidGroupColumn {
        relation: RelationId,
        column: Column,
    },
    DuplicateGroupColumn {
        relation: RelationId,
        index: usize,
    },
}

impl fmt::Display for ConstructionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Structured variants are the API; this fallback is for creator logs.
        write!(f, "Invalid IR construction: {self:?}")
    }
}
impl std::error::Error for ConstructionError {}

type Result<T> = std::result::Result<T, ConstructionError>;

#[derive(Debug, PartialEq, Eq)]
pub struct Sort {
    pub id: SortId,
    pub name: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Constant {
    pub id: ConstantId,
    pub name: String,
    pub sort: SortId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationRole {
    Input,
    Derived,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub sort: SortId,
}

impl Parameter {
    pub fn new(name: impl Into<String>, sort: SortId) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Relation {
    pub id: RelationId,
    pub name: String,
    pub role: RelationRole,
    pub parameters: Vec<Parameter>,
}

/// Names identify variables within a rule, never across rules. Reusing a Term
/// in two rules does not link their variable bindings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Constant(ConstantId),
    Variable { name: String, sort: SortId },
}

impl Term {
    pub fn variable(name: impl Into<String>, sort: SortId) -> Self {
        Self::Variable {
            name: name.into(),
            sort,
        }
    }
}

impl From<ConstantId> for Term {
    fn from(id: ConstantId) -> Self {
        Self::Constant(id)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TermOccurrence {
    id: OccurrenceId,
    value: Term,
}

impl TermOccurrence {
    pub fn id(&self) -> OccurrenceId {
        self.id
    }
    pub fn value(&self) -> &Term {
        &self.value
    }
}

// Not Clone: another use must be constructed as another occurrence, even when
// its semantic value is identical. All children share the atom's arena.
#[derive(Debug, PartialEq, Eq)]
pub struct Atom {
    id: OccurrenceId,
    relation: RelationId,
    arguments: Vec<TermOccurrence>,
}

impl Atom {
    pub fn id(&self) -> OccurrenceId {
        self.id
    }
    pub fn relation(&self) -> RelationId {
        self.relation
    }
    pub fn arguments(&self) -> &[TermOccurrence] {
        &self.arguments
    }

    fn occurrences(&self) -> impl Iterator<Item = OccurrenceId> + '_ {
        std::iter::once(self.id).chain(self.arguments.iter().map(TermOccurrence::id))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Positive(Atom),
    Negative(Atom),
}

impl Literal {
    pub fn atom(&self) -> &Atom {
        match self {
            Self::Positive(atom) | Self::Negative(atom) => atom,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Rule {
    pub id: RuleId,
    pub head: Atom,
    pub body: Vec<Literal>,
}

impl Rule {
    /// Facts use the same representation as rules, with an empty body.
    pub fn is_fact(&self) -> bool {
        self.body.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Column {
    Name(String),
    Index(usize),
}

impl From<&str> for Column {
    fn from(name: &str) -> Self {
        Self::Name(name.into())
    }
}

/// Count distinct tuples in the remaining columns, per grouping tuple.
/// This is a requirement over settled meaning, not behavior or an input assumption.
#[derive(Debug, PartialEq, Eq)]
pub enum Requirement {
    AtMostOne {
        relation: RelationId,
        group_by: Vec<usize>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct Obligation {
    pub id: ObligationId,
    pub name: String,
    pub requirement: Requirement,
    /// Library-owned presentation metadata. Binding/rendering is deferred to
    /// the validation/evidence slice; no template language is implemented here.
    pub message_template: String,
}

/// Assembled relational declarations and rules. No source spans or domain-specific
/// concepts. Mutations go through checked constructors; accessors are read-only.
#[derive(Debug)]
pub struct Corpus {
    arena: Arena,
    next: usize,
    sorts: BTreeMap<SortId, Sort>,
    constants: BTreeMap<ConstantId, Constant>,
    relations: BTreeMap<RelationId, Relation>,
    rules: BTreeMap<RuleId, Rule>,
    obligations: BTreeMap<ObligationId, Obligation>,
    occurrences: BTreeSet<OccurrenceId>,
}

impl Default for Corpus {
    fn default() -> Self {
        Self {
            arena: Arena::new(),
            next: 0,
            sorts: BTreeMap::new(),
            constants: BTreeMap::new(),
            relations: BTreeMap::new(),
            rules: BTreeMap::new(),
            obligations: BTreeMap::new(),
            occurrences: BTreeSet::new(),
        }
    }
}

fn named(name: &str, kind: &'static str) -> Result<()> {
    if name.is_empty() {
        Err(ConstructionError::EmptyName(kind))
    } else {
        Ok(())
    }
}

impl Corpus {
    pub fn new() -> Self {
        Self::default()
    }

    fn fresh(&mut self) -> OccurrenceId {
        let id = OccurrenceId {
            arena: self.arena,
            index: self.next,
        };
        self.next += 1;
        id
    }

    pub fn contains_occurrence(&self, id: OccurrenceId) -> bool {
        self.occurrences.contains(&id)
    }

    pub fn sorts(&self) -> impl Iterator<Item = &Sort> {
        self.sorts.values()
    }
    pub fn constants(&self) -> impl Iterator<Item = &Constant> {
        self.constants.values()
    }
    pub fn relations(&self) -> impl Iterator<Item = &Relation> {
        self.relations.values()
    }
    pub fn rules(&self) -> impl Iterator<Item = &Rule> {
        self.rules.values()
    }
    pub fn obligations(&self) -> impl Iterator<Item = &Obligation> {
        self.obligations.values()
    }
    pub fn sort(&self, id: SortId) -> Option<&Sort> {
        self.sorts.get(&id)
    }
    pub fn constant(&self, id: ConstantId) -> Option<&Constant> {
        self.constants.get(&id)
    }
    pub fn relation(&self, id: RelationId) -> Option<&Relation> {
        self.relations.get(&id)
    }
    pub fn rule(&self, id: RuleId) -> Option<&Rule> {
        self.rules.get(&id)
    }
    pub fn obligation(&self, id: ObligationId) -> Option<&Obligation> {
        self.obligations.get(&id)
    }

    fn require_sort(&self, sort: SortId) -> Result<()> {
        self.sort(sort)
            .map(|_| ())
            .ok_or(ConstructionError::UnknownSort(sort))
    }

    pub fn declare_sort(&mut self, name: impl Into<String>) -> Result<SortId> {
        let name = name.into();
        named(&name, "sort")?;
        if self.sorts().any(|s| s.name == name) {
            return Err(ConstructionError::DuplicateName { kind: "sort", name });
        }
        let id = SortId(self.fresh());
        self.sorts.insert(id, Sort { id, name });
        self.occurrences.insert(id.into());
        Ok(id)
    }

    pub fn declare_constant(
        &mut self,
        name: impl Into<String>,
        sort: SortId,
    ) -> Result<ConstantId> {
        let name = name.into();
        self.require_sort(sort)?;
        named(&name, "constant")?;
        if self.constants().any(|c| c.sort == sort && c.name == name) {
            return Err(ConstructionError::DuplicateName {
                kind: "constant in sort",
                name,
            });
        }
        let id = ConstantId(self.fresh());
        self.constants.insert(id, Constant { id, name, sort });
        self.occurrences.insert(id.into());
        Ok(id)
    }

    pub fn declare_relation(
        &mut self,
        name: impl Into<String>,
        role: RelationRole,
        parameters: impl IntoIterator<Item = Parameter>,
    ) -> Result<RelationId> {
        let name = name.into();
        named(&name, "relation")?;
        if self.relations().any(|r| r.name == name) {
            return Err(ConstructionError::DuplicateName {
                kind: "relation",
                name,
            });
        }
        let parameters: Vec<_> = parameters.into_iter().collect();
        let mut names = BTreeSet::new();
        for parameter in &parameters {
            self.require_sort(parameter.sort)?;
            named(&parameter.name, "parameter")?;
            if !names.insert(&parameter.name) {
                return Err(ConstructionError::DuplicateName {
                    kind: "parameter",
                    name: parameter.name.clone(),
                });
            }
        }
        let id = RelationId(self.fresh());
        self.relations.insert(
            id,
            Relation {
                id,
                name,
                role,
                parameters,
            },
        );
        self.occurrences.insert(id.into());
        Ok(id)
    }

    pub fn atom(
        &mut self,
        relation: RelationId,
        arguments: impl IntoIterator<Item = Term>,
    ) -> Result<Atom> {
        let declaration = self
            .relation(relation)
            .ok_or(ConstructionError::UnknownRelation(relation))?;
        let arguments: Vec<_> = arguments.into_iter().collect();
        if arguments.len() != declaration.parameters.len() {
            return Err(ConstructionError::Arity {
                relation,
                expected: declaration.parameters.len(),
                actual: arguments.len(),
            });
        }
        for (index, (term, parameter)) in arguments.iter().zip(&declaration.parameters).enumerate()
        {
            let actual = match term {
                Term::Constant(id) => {
                    self.constant(*id)
                        .ok_or(ConstructionError::UnknownConstant(*id))?
                        .sort
                }
                Term::Variable { name, sort } => {
                    named(name, "variable")?;
                    self.require_sort(*sort)?;
                    *sort
                }
            };
            if actual != parameter.sort {
                return Err(ConstructionError::SortMismatch {
                    relation,
                    argument: index,
                    expected: parameter.sort,
                    actual,
                });
            }
        }
        Ok(Atom {
            id: self.fresh(),
            relation,
            arguments: arguments
                .into_iter()
                .map(|value| TermOccurrence {
                    id: self.fresh(),
                    value,
                })
                .collect(),
        })
    }

    pub fn add_fact(&mut self, head: Atom) -> Result<RuleId> {
        self.add_rule(head, [])
    }

    pub fn add_rule(
        &mut self,
        head: Atom,
        body: impl IntoIterator<Item = Literal>,
    ) -> Result<RuleId> {
        let body: Vec<_> = body.into_iter().collect();
        let atoms = || std::iter::once(&head).chain(body.iter().map(Literal::atom));
        // Atom constructors already checked signatures. Verify corpus ownership
        // before using their handles, including atoms constructed by other corpora.
        for atom in atoms() {
            if atom.id.arena != self.arena {
                return Err(ConstructionError::ForeignAtom(atom.id));
            }
        }
        let relation = self
            .relation(head.relation)
            .ok_or(ConstructionError::UnknownRelation(head.relation))?;
        if relation.role == RelationRole::Input {
            return Err(ConstructionError::InputDefinition(head.relation));
        }
        let mut sorts = BTreeMap::new();
        for atom in atoms() {
            for argument in &atom.arguments {
                if let Term::Variable { name, sort } = &argument.value {
                    if let Some(expected) = sorts.insert(name, *sort) {
                        if expected != *sort {
                            return Err(ConstructionError::VariableSortConflict {
                                name: name.clone(),
                                expected,
                                actual: *sort,
                            });
                        }
                    }
                }
            }
        }
        let bound: BTreeSet<_> = body
            .iter()
            .filter_map(|literal| match literal {
                Literal::Positive(atom) => Some(atom),
                Literal::Negative(_) => None,
            })
            .flat_map(|atom| &atom.arguments)
            .filter_map(|argument| match &argument.value {
                Term::Variable { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        for atom in std::iter::once(&head).chain(body.iter().filter_map(|literal| match literal {
            Literal::Negative(atom) => Some(atom),
            _ => None,
        })) {
            for argument in &atom.arguments {
                if let Term::Variable { name, .. } = &argument.value {
                    if !bound.contains(name.as_str()) {
                        return Err(ConstructionError::UnsafeVariable {
                            name: name.clone(),
                            occurrence: argument.id,
                        });
                    }
                }
            }
        }
        let occurrences: Vec<_> = atoms().flat_map(Atom::occurrences).collect();
        let id = RuleId(self.fresh());
        self.occurrences.extend(occurrences);
        self.occurrences.insert(id.into());
        self.rules.insert(id, Rule { id, head, body });
        Ok(id)
    }

    pub fn at_most_one(
        &mut self,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        let name = name.into();
        named(&name, "obligation")?;
        if self.obligations().any(|o| o.name == name) {
            return Err(ConstructionError::DuplicateName {
                kind: "obligation",
                name,
            });
        }
        let declaration = self
            .relation(relation)
            .ok_or(ConstructionError::UnknownRelation(relation))?;
        let mut indices = Vec::new();
        for column in group_by {
            let index = match &column {
                Column::Name(name) => declaration.parameters.iter().position(|p| p.name == *name),
                Column::Index(index) => (*index < declaration.parameters.len()).then_some(*index),
            }
            .ok_or_else(|| ConstructionError::InvalidGroupColumn {
                relation,
                column: column.clone(),
            })?;
            if indices.contains(&index) {
                return Err(ConstructionError::DuplicateGroupColumn { relation, index });
            }
            indices.push(index);
        }
        let id = ObligationId(self.fresh());
        self.obligations.insert(
            id,
            Obligation {
                id,
                name,
                requirement: Requirement::AtMostOne {
                    relation,
                    group_by: indices,
                },
                message_template: message_template.into(),
            },
        );
        self.occurrences.insert(id.into());
        Ok(id)
    }
}
