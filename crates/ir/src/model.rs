use crate::{Namespace, ids::*};
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
    /// Assumptions restrict permitted input worlds, so they name input relations.
    InvalidAssumption {
        relation: RelationId,
        reason: &'static str,
    },
    UnknownAssumption(AssumptionId),
    UnknownNotice(NoticeId),
    InvalidNoticeRelation(RelationId),
    UnknownObligation(ObligationId),
    InvalidInputDomain {
        input: RelationId,
        provider: RelationId,
        reason: &'static str,
    },
    DuplicateReference {
        verification: String,
        reference: OccurrenceId,
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
    /// Optional fact-derived eligibility relation; matching positional signature.
    pub input_domain: Option<RelationId>,
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

/// Independent checks required by a cardinality obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cardinality {
    AtMostOne,
    AtLeastOne,
    ExactlyOne,
    Empty,
}
impl Cardinality {
    pub fn has_coverage(self) -> bool {
        matches!(self, Self::AtLeastOne | Self::ExactlyOne)
    }
    pub fn has_uniqueness(self) -> bool {
        matches!(self, Self::AtMostOne | Self::ExactlyOne)
    }
}

/// Cardinality of distinct tuples, grouped where the requirement has grouping.
/// Obligations require this of settled meaning; restrictions use the same shape
/// to constrain independently evaluated input/derived meaning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Requirement {
    Empty {
        relation: RelationId,
    },
    AtMostOne {
        relation: RelationId,
        group_by: Vec<usize>,
    },
    AtLeastOne {
        relation: RelationId,
        group_by: Vec<usize>,
    },
    ExactlyOne {
        relation: RelationId,
        group_by: Vec<usize>,
    },
}

impl Requirement {
    pub fn kind(&self) -> Cardinality {
        match self {
            Self::AtMostOne { .. } => Cardinality::AtMostOne,
            Self::AtLeastOne { .. } => Cardinality::AtLeastOne,
            Self::ExactlyOne { .. } => Cardinality::ExactlyOne,
            Self::Empty { .. } => Cardinality::Empty,
        }
    }
    pub fn relation(&self) -> RelationId {
        match self {
            Self::AtMostOne { relation, .. }
            | Self::AtLeastOne { relation, .. }
            | Self::ExactlyOne { relation, .. }
            | Self::Empty { relation } => *relation,
        }
    }
    /// Grouping columns; empty for the ungrouped emptiness requirement as well
    /// as globally grouped requirements. Use `kind()` to distinguish them.
    pub fn group_by(&self) -> &[usize] {
        match self {
            Self::Empty { .. } => &[],
            Self::AtMostOne { group_by, .. }
            | Self::AtLeastOne { group_by, .. }
            | Self::ExactlyOne { group_by, .. } => group_by,
        }
    }
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

/// A selected restriction on independently evaluated input/derived meaning.
/// It shares cardinality vocabulary with obligations, but constrains worlds.
pub type Restriction = Requirement;

#[derive(Debug, PartialEq, Eq)]
pub struct Assumption {
    pub id: AssumptionId,
    pub name: String,
    pub restriction: Restriction,
}

/// Advisory variability query over zero-arity relations. No effect on meaning or
/// obligation verdicts; `within: None` denotes the whole permitted context.
#[derive(Debug, PartialEq, Eq)]
pub struct Notice {
    pub id: NoticeId,
    pub name: String,
    pub condition: RelationId,
    pub within: Option<RelationId>,
    pub message: String,
}

/// A named verification context: the assumptions that define permitted input worlds
/// and the obligations checked under them. Declaring an assumption activates nothing;
/// only a verification's selection does. References keep their authored order.
#[derive(Debug, PartialEq, Eq)]
pub struct VerificationDeclaration {
    pub id: VerificationId,
    pub name: String,
    pub assumptions: Vec<AssumptionId>,
    pub obligations: Vec<ObligationId>,
    pub notices: Vec<NoticeId>,
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
    // Generated relation display names are not members of the frontend namespace.
    generated_relations: BTreeSet<RelationId>,
    rules: BTreeMap<RuleId, Rule>,
    obligations: BTreeMap<ObligationId, Obligation>,
    assumptions: BTreeMap<AssumptionId, Assumption>,
    notices: BTreeMap<NoticeId, Notice>,
    verifications: BTreeMap<VerificationId, VerificationDeclaration>,
    occurrences: BTreeSet<OccurrenceId>,
    namespaces: BTreeMap<OccurrenceId, Namespace>,
}

/// Top-level declarations, rules and contracts, excluding atom/term occurrences.
/// Each kind retains corpus order; this does not impose a semantic global order.
pub fn top_level(c: &Corpus) -> Vec<OccurrenceId> {
    c.sorts()
        .map(|x| x.id.into())
        .chain(c.constants().map(|x| x.id.into()))
        .chain(c.relations().map(|x| x.id.into()))
        .chain(c.rules().map(|x| x.id.into()))
        .chain(c.obligations().map(|x| x.id.into()))
        .chain(c.assumptions().map(|x| x.id.into()))
        .chain(c.notices().map(|x| x.id.into()))
        .chain(c.verifications().map(|x| x.id.into()))
        .collect()
}
impl Default for Corpus {
    fn default() -> Self {
        Self {
            arena: Arena::new(),
            next: 0,
            sorts: BTreeMap::new(),
            constants: BTreeMap::new(),
            relations: BTreeMap::new(),
            generated_relations: BTreeSet::new(),
            rules: BTreeMap::new(),
            obligations: BTreeMap::new(),
            assumptions: BTreeMap::new(),
            notices: BTreeMap::new(),
            verifications: BTreeMap::new(),
            occurrences: BTreeSet::new(),
            namespaces: BTreeMap::new(),
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
    pub fn assumptions(&self) -> impl Iterator<Item = &Assumption> {
        self.assumptions.values()
    }
    pub fn assumption(&self, id: AssumptionId) -> Option<&Assumption> {
        self.assumptions.get(&id)
    }
    pub fn notices(&self) -> impl Iterator<Item = &Notice> {
        self.notices.values()
    }
    pub fn notice(&self, id: NoticeId) -> Option<&Notice> {
        self.notices.get(&id)
    }

    pub fn notice_varies_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        condition: RelationId,
        within: Option<RelationId>,
        message: impl Into<String>,
    ) -> Result<NoticeId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "notice")?;
        if self
            .notices()
            .any(|n| n.name == name && self.namespace(n.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName {
                kind: "notice",
                name,
            });
        }
        for id in std::iter::once(condition).chain(within) {
            let r = self
                .relation(id)
                .ok_or(ConstructionError::UnknownRelation(id))?;
            if !r.parameters.is_empty() {
                return Err(ConstructionError::InvalidNoticeRelation(id));
            }
        }
        let id = NoticeId(self.fresh());
        self.notices.insert(
            id,
            Notice {
                id,
                name,
                condition,
                within,
                message: message.into(),
            },
        );
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    pub fn verifications(&self) -> impl Iterator<Item = &VerificationDeclaration> {
        self.verifications.values()
    }
    pub fn verification(&self, id: VerificationId) -> Option<&VerificationDeclaration> {
        self.verifications.get(&id)
    }

    fn require_sort(&self, sort: SortId) -> Result<()> {
        self.sort(sort)
            .map(|_| ())
            .ok_or(ConstructionError::UnknownSort(sort))
    }

    /// Explicit owning namespace of a declaration (including a generated helper)
    /// or rule. Atoms/terms are occurrences within a rule, not namespace owners.
    /// Foreign handles and non-owner occurrences return None.
    pub fn namespace(&self, id: impl Into<OccurrenceId>) -> Option<&Namespace> {
        self.namespaces.get(&id.into())
    }

    pub fn declare_sort(&mut self, name: impl Into<String>) -> Result<SortId> {
        self.declare_sort_in(Namespace::default(), name)
    }
    pub fn declare_sort_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
    ) -> Result<SortId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "sort")?;
        if self
            .sorts()
            .any(|s| s.name == name && self.namespace(s.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName { kind: "sort", name });
        }
        let id = SortId(self.fresh());
        self.sorts.insert(id, Sort { id, name });
        self.namespaces.insert(id.into(), namespace);
        self.occurrences.insert(id.into());
        Ok(id)
    }

    pub fn declare_constant(
        &mut self,
        name: impl Into<String>,
        sort: SortId,
    ) -> Result<ConstantId> {
        self.declare_constant_in(Namespace::default(), name, sort)
    }
    pub fn declare_constant_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        sort: SortId,
    ) -> Result<ConstantId> {
        let namespace = namespace.into();
        let name = name.into();
        self.require_sort(sort)?;
        named(&name, "constant")?;
        if self
            .constants()
            .any(|c| c.sort == sort && c.name == name && self.namespace(c.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName {
                kind: "constant in sort",
                name,
            });
        }
        let id = ConstantId(self.fresh());
        self.constants.insert(id, Constant { id, name, sort });
        self.namespaces.insert(id.into(), namespace);
        self.occurrences.insert(id.into());
        Ok(id)
    }

    pub(crate) fn set_input_domain(
        &mut self,
        input: RelationId,
        provider: RelationId,
    ) -> Result<()> {
        let relation = self
            .relations
            .get_mut(&input)
            .ok_or(ConstructionError::UnknownRelation(input))?;
        if relation.input_domain.is_some() {
            return Err(ConstructionError::InvalidInputDomain {
                input,
                provider,
                reason: "input already has a domain provider",
            });
        }
        relation.input_domain = Some(provider);
        Ok(())
    }

    pub fn declare_relation(
        &mut self,
        name: impl Into<String>,
        role: RelationRole,
        parameters: impl IntoIterator<Item = Parameter>,
    ) -> Result<RelationId> {
        self.declare_relation_in(Namespace::default(), name, role, parameters)
    }
    pub fn declare_relation_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        role: RelationRole,
        parameters: impl IntoIterator<Item = Parameter>,
    ) -> Result<RelationId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "relation")?;
        if self.relations().any(|r| {
            r.name == name
                && !self.is_generated_relation(r.id)
                && self.namespace(r.id) == Some(&namespace)
        }) {
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
                input_domain: None,
            },
        );
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    /// A generated identity outside the frontend relation-name namespace.
    /// Display labels preserve deterministic document-wide helper numbering.
    /// A frontend may declare the same display name before or after this call;
    /// consumers must resolve frontend names only among non-generated relations.
    pub fn declare_generated_relation(&mut self) -> RelationId {
        self.declare_generated_relation_in(Namespace::default())
    }

    /// Generate a helper in the transformation's explicit owning namespace.
    /// Numbering remains corpus-wide display text, not identity or ownership.
    pub fn declare_generated_relation_in(&mut self, namespace: impl Into<Namespace>) -> RelationId {
        let name = format!("$condition_{}", self.generated_relations.len() + 1);
        self.declare_generated_relation_named_in(namespace, name)
            .expect("generated label is nonempty")
    }

    /// Restore an explicit generated display label when loading text. Identity
    /// remains independent of the label and outside the frontend namespace.
    /// Generated relations are zero-arity derived helpers, as in installation.
    pub fn declare_generated_relation_named(
        &mut self,
        name: impl Into<String>,
    ) -> Result<RelationId> {
        self.declare_generated_relation_named_in(Namespace::default(), name)
    }

    /// A generated label need not be unique, even within one namespace. Identity
    /// remains the fresh handle plus the generated kind; frontend names cannot
    /// alias it. The exporter may choose distinct display labels later.
    pub fn declare_generated_relation_named_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
    ) -> Result<RelationId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "generated relation")?;
        let id = RelationId(self.fresh());
        self.relations.insert(
            id,
            Relation {
                id,
                name,
                role: RelationRole::Derived,
                parameters: vec![],
                input_domain: None,
            },
        );
        self.generated_relations.insert(id);
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    pub fn is_generated_relation(&self, id: RelationId) -> bool {
        self.generated_relations.contains(&id)
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

    pub fn add_fact_in(&mut self, namespace: impl Into<Namespace>, head: Atom) -> Result<RuleId> {
        self.add_rule_in(namespace, head, [])
    }

    pub fn add_rule(
        &mut self,
        head: Atom,
        body: impl IntoIterator<Item = Literal>,
    ) -> Result<RuleId> {
        self.add_rule_in(Namespace::default(), head, body)
    }

    /// The rule belongs to the supplied namespace, independently of the head
    /// and body declarations' namespaces. Transformations can read this owner
    /// with [`Self::namespace`] and pass it to helper/recipe installation.
    pub fn add_rule_in(
        &mut self,
        namespace: impl Into<Namespace>,
        head: Atom,
        body: impl IntoIterator<Item = Literal>,
    ) -> Result<RuleId> {
        let namespace = namespace.into();
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
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    pub fn at_most_one(
        &mut self,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.at_most_one_in(
            Namespace::default(),
            name,
            relation,
            group_by,
            message_template,
        )
    }
    pub fn at_most_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.cardinality_in(
            namespace.into(),
            name.into(),
            relation,
            group_by,
            message_template.into(),
            Cardinality::AtMostOne,
        )
    }
    pub fn at_least_one(
        &mut self,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.at_least_one_in(
            Namespace::default(),
            name,
            relation,
            group_by,
            message_template,
        )
    }
    pub fn at_least_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.cardinality_in(
            namespace.into(),
            name.into(),
            relation,
            group_by,
            message_template.into(),
            Cardinality::AtLeastOne,
        )
    }
    pub fn exactly_one(
        &mut self,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.exactly_one_in(
            Namespace::default(),
            name,
            relation,
            group_by,
            message_template,
        )
    }
    pub fn exactly_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.cardinality_in(
            namespace.into(),
            name.into(),
            relation,
            group_by,
            message_template.into(),
            Cardinality::ExactlyOne,
        )
    }
    /// Require no tuple in any permitted world. This obligation has no grouping.
    pub fn empty(
        &mut self,
        name: impl Into<String>,
        relation: RelationId,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.empty_in(Namespace::default(), name, relation, message_template)
    }
    pub fn empty_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        message_template: impl Into<String>,
    ) -> Result<ObligationId> {
        self.cardinality_in(
            namespace.into(),
            name.into(),
            relation,
            [],
            message_template.into(),
            Cardinality::Empty,
        )
    }
    fn cardinality_in(
        &mut self,
        namespace: Namespace,
        name: String,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
        message_template: String,
        kind: Cardinality,
    ) -> Result<ObligationId> {
        named(&name, "obligation")?;
        if self
            .obligations()
            .any(|o| o.name == name && self.namespace(o.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName {
                kind: "obligation",
                name,
            });
        }
        let indices = self.group_columns(relation, group_by)?;
        let id = ObligationId(self.fresh());
        self.obligations.insert(
            id,
            Obligation {
                id,
                name,
                requirement: match kind {
                    Cardinality::Empty => Requirement::Empty { relation },
                    Cardinality::AtMostOne => Requirement::AtMostOne {
                        relation,
                        group_by: indices,
                    },
                    Cardinality::AtLeastOne => Requirement::AtLeastOne {
                        relation,
                        group_by: indices,
                    },
                    Cardinality::ExactlyOne => Requirement::ExactlyOne {
                        relation,
                        group_by: indices,
                    },
                },
                message_template: message_template.into(),
            },
        );
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    fn group_columns(
        &self,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
    ) -> Result<Vec<usize>> {
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
        Ok(indices)
    }

    /// Declare a named restriction. Classify the completed rule graph with
    /// `validate_assumptions`; cones requiring grounding are validated by the checker.
    pub fn assume_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        kind: Cardinality,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
    ) -> Result<AssumptionId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "assumption")?;
        if self
            .assumptions()
            .any(|a| a.name == name && self.namespace(a.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName {
                kind: "assumption",
                name,
            });
        }
        let indices = self.group_columns(relation, group_by)?;
        if kind == Cardinality::Empty && !indices.is_empty() {
            return Err(ConstructionError::InvalidGroupColumn {
                relation,
                column: Column::Index(indices[0]),
            });
        }
        let restriction = match kind {
            Cardinality::AtMostOne => Restriction::AtMostOne {
                relation,
                group_by: indices,
            },
            Cardinality::AtLeastOne => Restriction::AtLeastOne {
                relation,
                group_by: indices,
            },
            Cardinality::ExactlyOne => Restriction::ExactlyOne {
                relation,
                group_by: indices,
            },
            Cardinality::Empty => Restriction::Empty { relation },
        };
        let id = AssumptionId(self.fresh());
        self.assumptions.insert(
            id,
            Assumption {
                id,
                name,
                restriction,
            },
        );
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }

    pub fn assume_at_most_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
    ) -> Result<AssumptionId> {
        self.assume_in(namespace, name, Cardinality::AtMostOne, relation, group_by)
    }
    pub fn assume_at_least_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
    ) -> Result<AssumptionId> {
        self.assume_in(namespace, name, Cardinality::AtLeastOne, relation, group_by)
    }
    pub fn assume_exactly_one_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
        group_by: impl IntoIterator<Item = Column>,
    ) -> Result<AssumptionId> {
        self.assume_in(namespace, name, Cardinality::ExactlyOne, relation, group_by)
    }
    pub fn assume_empty_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        relation: RelationId,
    ) -> Result<AssumptionId> {
        self.assume_in(namespace, name, Cardinality::Empty, relation, [])
    }

    /// Declare a verification selecting assumptions and obligations of this corpus.
    pub fn verification_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        assumptions: impl IntoIterator<Item = AssumptionId>,
        obligations: impl IntoIterator<Item = ObligationId>,
    ) -> Result<VerificationId> {
        self.verification_with_notices_in(namespace, name, assumptions, obligations, [])
    }

    pub fn verification_with_notices_in(
        &mut self,
        namespace: impl Into<Namespace>,
        name: impl Into<String>,
        assumptions: impl IntoIterator<Item = AssumptionId>,
        obligations: impl IntoIterator<Item = ObligationId>,
        notices: impl IntoIterator<Item = NoticeId>,
    ) -> Result<VerificationId> {
        let namespace = namespace.into();
        let name = name.into();
        named(&name, "verification")?;
        if self
            .verifications()
            .any(|v| v.name == name && self.namespace(v.id) == Some(&namespace))
        {
            return Err(ConstructionError::DuplicateName {
                kind: "verification",
                name,
            });
        }
        let assumptions: Vec<_> = assumptions.into_iter().collect();
        let obligations: Vec<_> = obligations.into_iter().collect();
        let notices: Vec<_> = notices.into_iter().collect();
        let mut seen = BTreeSet::new();
        for &a in &assumptions {
            if self.assumption(a).is_none() {
                return Err(ConstructionError::UnknownAssumption(a));
            }
            if !seen.insert(OccurrenceId::from(a)) {
                return Err(ConstructionError::DuplicateReference {
                    verification: name,
                    reference: a.into(),
                });
            }
        }
        for &o in &obligations {
            if self.obligation(o).is_none() {
                return Err(ConstructionError::UnknownObligation(o));
            }
            if !seen.insert(OccurrenceId::from(o)) {
                return Err(ConstructionError::DuplicateReference {
                    verification: name,
                    reference: o.into(),
                });
            }
        }
        for &n in &notices {
            if self.notice(n).is_none() {
                return Err(ConstructionError::UnknownNotice(n));
            }
            if !seen.insert(OccurrenceId::from(n)) {
                return Err(ConstructionError::DuplicateReference {
                    verification: name,
                    reference: n.into(),
                });
            }
        }
        let id = VerificationId(self.fresh());
        self.verifications.insert(
            id,
            VerificationDeclaration {
                id,
                name,
                assumptions,
                obligations,
                notices,
            },
        );
        self.occurrences.insert(id.into());
        self.namespaces.insert(id.into(), namespace);
        Ok(id)
    }
}
