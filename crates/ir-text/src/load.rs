use crate::{
    Diagnostic, ProgramMembership, Result, SourceFile,
    ast::{self, Atom as AstAtom, Decl, Name, Scope, Statement, namespace_key},
    error,
};
use denotate_check::{CheckRequest, Domains, Limits};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

#[derive(Clone, Debug)]
pub struct DocumentInfo {
    /// Explicit namespaces and namespaces containing declarations/location
    /// entries. Empty implicit global scopes (including import-only files) are omitted.
    pub namespaces: BTreeSet<Namespace>,
    pub uri: String,
    pub revision: u64,
    pub ownership: String,
    pub snapshot: SnapshotId,
    /// Exact location syntax for step 2; it is not interpreted as DSL origins yet.
    pub location_syntax: Vec<SourceSpan>,
}
#[derive(Debug)]
pub struct LoadedProgram {
    pub root: String,
    pub corpus: Corpus,
    pub keys: SemanticKeys,
    pub sources: Sources,
    /// Exact current .den origins; upstream associations remain separate.
    pub provenance: Provenance,
    pub embedded: crate::origins::EmbeddedOrigins,
    pub domains: Domains,
    pub documents: Vec<DocumentInfo>,
    pub membership: ProgramMembership,
    /// Occurrence -> owning document URI. Look up user/library classification
    /// in `documents`; namespace identity and provenance are independent.
    pub owners: BTreeMap<OccurrenceId, String>,
}
impl LoadedProgram {
    pub fn verification_requests(
        &self,
        limits: &Limits,
    ) -> std::result::Result<Vec<(VerificationKey, CheckRequest)>, denotate_check::CheckError> {
        let mut requests = self
            .corpus
            .verifications()
            .map(|v| {
                let request = CheckRequest::for_verification(
                    &self.corpus,
                    &self.keys,
                    &self.domains,
                    v.id,
                    limits,
                )?;
                Ok((
                    request.verification.clone().expect("named request"),
                    request,
                ))
            })
            .collect::<std::result::Result<Vec<_>, denotate_check::CheckError>>()?;
        requests.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(requests)
    }
}

struct Builder {
    program: LoadedProgram,
    snapshots: BTreeMap<String, SnapshotId>,
    sorts: BTreeMap<(Namespace, String), SortId>,
    relations: BTreeMap<(Namespace, String, bool), RelationId>,
    constants: BTreeMap<(Namespace, SortId, String), ConstantId>,
}
fn diagnostic(m: &Scope, span: Range<usize>, message: impl Into<String>) -> Vec<Diagnostic> {
    error(&m.source, span, message)
}
fn construction<T>(
    m: &Scope,
    span: Range<usize>,
    value: std::result::Result<T, impl std::fmt::Display>,
) -> Result<T> {
    value.map_err(|e| diagnostic(m, span, e.to_string()))
}

fn ir_construction<T>(
    m: &Scope,
    span: Range<usize>,
    value: std::result::Result<T, ConstructionError>,
    corpus: &Corpus,
) -> Result<T> {
    let qualified =
        |id: OccurrenceId, name: &str| match corpus.namespace(id).filter(|ns| !ns.is_global()) {
            Some(ns) => format!("{}::{name}", namespace_key(ns)),
            None => name.to_owned(),
        };
    let sort = |id| {
        corpus
            .sort(id)
            .map(|s| qualified(s.id.into(), &s.name))
            .unwrap_or_else(|| "<unknown sort>".into())
    };
    let relation = |id| {
        corpus
            .relation(id)
            .map(|r| qualified(r.id.into(), &r.name))
            .unwrap_or_else(|| "<unknown relation>".into())
    };
    value.map_err(|e| {
        let message = match e {
            ConstructionError::EmptyName(kind) => format!("The {kind} name must not be empty"),
            ConstructionError::DuplicateName { kind, name } => {
                format!("Duplicate {kind} name {name:?}")
            }
            ConstructionError::UnknownSort(_) => "Unknown sort in IR construction".into(),
            ConstructionError::UnknownConstant(_) => "Unknown constant in IR construction".into(),
            ConstructionError::UnknownRelation(_) => "Unknown relation in IR construction".into(),
            ConstructionError::ForeignAtom(_) => "Atom belongs to a different program".into(),
            ConstructionError::Arity {
                relation: id,
                expected,
                actual,
            } => format!(
                "Relation {:?} expects {expected} arguments, got {actual}",
                relation(id)
            ),
            ConstructionError::SortMismatch {
                relation: id,
                argument,
                expected,
                actual,
            } => format!(
                "Argument {} of relation {:?} expects sort {:?}, got {:?}",
                argument + 1,
                relation(id),
                sort(expected),
                sort(actual)
            ),
            ConstructionError::VariableSortConflict {
                name,
                expected,
                actual,
            } => format!(
                "Variable {name:?} has conflicting sorts {:?} and {:?}",
                sort(expected),
                sort(actual)
            ),
            ConstructionError::UnsafeVariable { name, .. } => {
                format!("Variable {name:?} must occur in a positive body literal")
            }
            ConstructionError::InputDefinition(id) => format!(
                "Input relation {:?} cannot be defined by a rule",
                relation(id)
            ),
            ConstructionError::InvalidGroupColumn {
                relation: id,
                column,
            } => format!(
                "Invalid grouping column {column:?} for relation {:?}",
                relation(id)
            ),
            ConstructionError::DuplicateGroupColumn {
                relation: id,
                index,
            } => format!(
                "Duplicate grouping column {} for relation {:?}",
                index + 1,
                relation(id)
            ),
            ConstructionError::AssumptionOverDerived(id) => format!(
                "Assumptions restrict inputs; relation {:?} is not an input",
                relation(id)
            ),
            ConstructionError::UnknownAssumption(_) => {
                "Unknown assumption in IR construction".into()
            }
            ConstructionError::UnknownObligation(_) => {
                "Unknown obligation in IR construction".into()
            }
            ConstructionError::DuplicateReference { verification, .. } => {
                format!("Verification {verification:?} selects the same declaration twice")
            }
        };
        diagnostic(m, span, message)
    })
}
fn candidate_keys(m: &Scope, name: &Name) -> Vec<(Namespace, String, bool)> {
    crate::index::candidate_keys(
        crate::index::visible_namespaces(
            &m.namespace,
            m.imports.iter().map(|(ns, _)| ns),
            name.namespace.as_ref(),
        ),
        &name.text,
        name.generated,
    )
}
fn one<T: Copy>(
    m: &Scope,
    name: &Name,
    kind: &str,
    candidates: impl IntoIterator<Item = T>,
) -> Result<T> {
    let candidates = candidates.into_iter().collect::<Vec<_>>();
    match candidates.as_slice() {
        [id] => Ok(*id),
        [] => Err(diagnostic(
            m,
            name.span.clone(),
            format!("Unknown {kind} {:?}", name.text),
        )),
        _ => Err(diagnostic(
            m,
            name.span.clone(),
            format!(
                "Ambiguous {kind} {:?}; qualify it with its namespace",
                name.text
            ),
        )),
    }
}
impl Builder {
    fn sort(&self, m: &Scope, n: &Name) -> Result<SortId> {
        one(
            m,
            n,
            "sort",
            candidate_keys(m, n)
                .into_iter()
                .filter_map(|(namespace, text, _)| self.sorts.get(&(namespace, text)).copied()),
        )
    }
    fn relation(&self, m: &Scope, n: &Name) -> Result<RelationId> {
        one(
            m,
            n,
            "relation",
            candidate_keys(m, n)
                .into_iter()
                .filter_map(|key| self.relations.get(&key).copied()),
        )
    }
    fn constant(&self, m: &Scope, n: &Name, sort: SortId) -> Result<ConstantId> {
        one(
            m,
            n,
            "constant of the expected sort",
            candidate_keys(m, n)
                .into_iter()
                .filter_map(|(namespace, text, _)| {
                    self.constants.get(&(namespace, sort, text)).copied()
                }),
        )
    }
    fn span(&self, m: &Scope, range: Range<usize>) -> Result<SourceSpan> {
        construction(
            m,
            range.clone(),
            self.program
                .sources
                .span(self.snapshots[&m.source.uri], range),
        )
    }
    fn origin(
        &mut self,
        m: &Scope,
        id: impl Into<OccurrenceId>,
        range: Range<usize>,
    ) -> Result<()> {
        let id = id.into();
        let span = self.span(m, range.clone())?;
        construction(
            m,
            range,
            self.program.provenance.attach(
                &self.program.corpus,
                &self.program.sources,
                id,
                [Origin::new(span)],
            ),
        )?;
        self.program.owners.insert(id, m.source.uri.clone());
        Ok(())
    }
    fn atom(
        &mut self,
        m: &Scope,
        a: &AstAtom,
        used: &mut BTreeSet<String>,
        anon: &mut usize,
    ) -> Result<denotate_ir::Atom> {
        let relation = self.relation(m, &a.name)?;
        let parameters = self
            .program
            .corpus
            .relation(relation)
            .unwrap()
            .parameters
            .clone();
        if parameters.len() != a.terms.len() {
            return Err(diagnostic(
                m,
                a.span.clone(),
                format!(
                    "Relation {:?} expects {} arguments, got {}",
                    a.name.text,
                    parameters.len(),
                    a.terms.len()
                ),
            ));
        }
        let mut terms = Vec::new();
        for (term, param) in a.terms.iter().zip(parameters) {
            if term.anonymous {
                loop {
                    let name = format!("__den_anonymous_{anon}");
                    *anon += 1;
                    if used.insert(name.clone()) {
                        terms.push(Term::variable(name, param.sort));
                        break;
                    }
                }
            } else if term.variable {
                terms.push(Term::variable(&term.name.text, param.sort));
            } else {
                terms.push(Term::Constant(self.constant(m, &term.name, param.sort)?));
            }
        }
        ir_construction(
            m,
            a.span.clone(),
            self.program.corpus.atom(relation, terms),
            &self.program.corpus,
        )
    }
    fn rule(
        &mut self,
        m: &Scope,
        statement: &Statement,
        head: &AstAtom,
        body: &[(bool, AstAtom)],
        duplicates: &mut BTreeMap<(Namespace, String), usize>,
    ) -> Result<()> {
        let mut used = std::iter::once(head)
            .chain(body.iter().map(|(_, a)| a))
            .flat_map(|a| a.terms.iter())
            .filter(|t| t.variable)
            .map(|t| t.name.text.clone())
            .collect();
        let mut anon = 0;
        let h = self.atom(m, head, &mut used, &mut anon)?;
        let mut b = Vec::new();
        for (negative, a) in body {
            let a = self.atom(m, a, &mut used, &mut anon)?;
            b.push(if *negative {
                Literal::Negative(a)
            } else {
                Literal::Positive(a)
            });
        }
        let atom_key = |atom: &denotate_ir::Atom| {
            let terms = atom
                .arguments()
                .iter()
                .map(|term| match term.value() {
                    Term::Constant(id) => {
                        format!("constant:{:?}", self.program.keys.constant(*id).unwrap())
                    }
                    Term::Variable { name, sort } => format!(
                        "variable:{name:?}:{:?}",
                        self.program.keys.sort(*sort).unwrap()
                    ),
                })
                .collect::<Vec<_>>();
            format!(
                "{:?}:{terms:?}",
                self.program.keys.relation(atom.relation()).unwrap()
            )
        };
        let signature = format!(
            "{}:{:?}",
            atom_key(&h),
            b.iter()
                .map(|literal| (
                    matches!(literal, Literal::Negative(_)),
                    atom_key(literal.atom())
                ))
                .collect::<Vec<_>>()
        );
        let duplicate = duplicates
            .entry((m.namespace.clone(), signature.clone()))
            .or_default();
        let owner = OwnerKey::new(
            format!("denotate/rule/{}", namespace_key(&m.namespace)),
            format!("{signature}/{duplicate}").into_bytes(),
        );
        *duplicate += 1;
        let id = ir_construction(
            m,
            statement.span.clone(),
            self.program.corpus.add_rule_in(&m.namespace, h, b),
            &self.program.corpus,
        )?;
        construction(
            m,
            statement.span.clone(),
            self.program.keys.bind_rule(
                &self.program.corpus,
                id,
                RuleKey::Installed {
                    owner: owner.clone(),
                    local: 0,
                },
            ),
        )?;
        self.origin(m, id, statement.span.clone())?;
        let rule = self.program.corpus.rule(id).unwrap();
        let occurrences = std::iter::once(&rule.head)
            .chain(rule.body.iter().map(Literal::atom))
            .zip(std::iter::once(head).chain(body.iter().map(|(_, a)| a)))
            .flat_map(|(atom, ast)| {
                std::iter::once((atom.id(), ast.span.clone())).chain(
                    atom.arguments()
                        .iter()
                        .zip(&ast.terms)
                        .map(|(t, a)| (t.id(), a.name.span.clone())),
                )
            })
            .collect::<Vec<_>>();
        for (index, (id, span)) in occurrences.into_iter().enumerate() {
            construction(
                m,
                span.clone(),
                self.program.keys.bind_occurrence(
                    &self.program.corpus,
                    id,
                    OccurrenceKey::Installed {
                        owner: owner.clone(),
                        local: index + 1,
                    },
                ),
            )?;
            self.origin(m, id, span)?;
        }
        Ok(())
    }
}

/// Load the explicitly supplied program. `use` affects lookup only. All
/// declaration passes precede rule installation, independently of file order.
pub fn load(membership: &ProgramMembership, documents: &[SourceFile]) -> Result<LoadedProgram> {
    load_with_resolver(membership, documents, None)
}

pub fn load_with_resolver(
    membership: &ProgramMembership,
    documents: &[SourceFile],
    resolver: Option<&mut dyn crate::origins::OriginResolver>,
) -> Result<LoadedProgram> {
    let members = membership.members()?;
    let mut sources = BTreeMap::<String, &SourceFile>::new();
    for source in documents.iter().filter(|s| members.contains_key(&s.uri)) {
        if let Some(previous) = sources.insert(source.uri.clone(), source) {
            if previous.revision != source.revision || previous.text != source.text {
                return Err(error(
                    source,
                    0..0,
                    "Conflicting snapshots for the same file",
                ));
            }
        }
    }
    let mut scopes = Vec::new();
    for uri in members.keys() {
        let source = sources.get(uri).ok_or_else(|| {
            vec![Diagnostic {
                uri: uri.clone(),
                range: 0..0,
                message: "Missing member snapshot".into(),
            }]
        })?;
        scopes.extend(ast::parse(source)?);
    }
    // An enclosing namespace exists even when only a descendant is declared.
    let mut namespaces = BTreeSet::new();
    for m in &scopes {
        for length in 0..=m.namespace.segments().len() {
            namespaces
                .insert(Namespace::new(m.namespace.segments()[..length].iter().cloned()).unwrap());
        }
    }
    for m in &scopes {
        for (import, span) in &m.imports {
            if !namespaces.contains(import) {
                return Err(diagnostic(
                    m,
                    span.clone(),
                    format!("Unknown namespace {:?}", namespace_key(import)),
                ));
            }
        }
    }
    let mut b = Builder {
        program: LoadedProgram {
            root: membership.root.clone(),
            corpus: Corpus::new(),
            keys: SemanticKeys::default(),
            sources: Sources::new(),
            provenance: Provenance::new(),
            embedded: Default::default(),
            domains: BTreeMap::new(),
            documents: Vec::new(),
            membership: membership.clone(),
            owners: BTreeMap::new(),
        },
        snapshots: BTreeMap::new(),
        sorts: BTreeMap::new(),
        relations: BTreeMap::new(),
        constants: BTreeMap::new(),
    };
    for (uri, source) in &sources {
        let snapshot = b
            .program
            .sources
            .add(
                uri.as_str(),
                source.revision,
                "denotate",
                source.text.clone(),
            )
            .map_err(|e| error(source, 0..0, e.to_string()))?;
        b.snapshots.insert(uri.clone(), snapshot);
        let file_scopes = scopes
            .iter()
            .filter(|m| m.source.uri == *uri)
            .collect::<Vec<_>>();
        let locations = file_scopes
            .iter()
            .flat_map(|m| m.locations.iter())
            .map(|range| {
                b.program
                    .sources
                    .span(snapshot, range.clone())
                    .map_err(|e| error(source, range.clone(), e.to_string()))
            })
            .collect::<Result<_>>()?;
        b.program.documents.push(DocumentInfo {
            namespaces: file_scopes
                .iter()
                .filter(|m| {
                    !m.namespace.is_global() || !m.statements.is_empty() || !m.locations.is_empty()
                })
                .map(|m| m.namespace.clone())
                .collect(),
            uri: uri.clone(),
            revision: source.revision,
            ownership: members[uri].clone(),
            snapshot,
            location_syntax: locations,
        });
    }
    for m in &scopes {
        let name = &m.namespace;
        for s in &m.statements {
            if let Decl::Sort(n) = &s.decl {
                let id = ir_construction(
                    m,
                    n.span.clone(),
                    b.program.corpus.declare_sort_in(name, &n.text),
                    &b.program.corpus,
                )?;
                b.sorts.insert((name.clone(), n.text.clone()), id);
                construction(
                    m,
                    n.span.clone(),
                    b.program.keys.bind_sort(
                        &b.program.corpus,
                        id,
                        SortKey(QualifiedKey::new(namespace_key(name), n.text.as_str())),
                    ),
                )?;
                b.origin(m, id, n.span.clone())?;
            }
        }
    }
    // Install all signatures/constants before resolving rules across files.
    for m in &scopes {
        let module = &m.namespace;
        for s in &m.statements {
            match &s.decl {
                Decl::Constants(names, sort) => {
                    let sort = b.sort(m, sort)?;
                    for n in names {
                        let id = ir_construction(
                            m,
                            n.span.clone(),
                            b.program.corpus.declare_constant_in(module, &n.text, sort),
                            &b.program.corpus,
                        )?;
                        b.constants
                            .insert((module.clone(), sort, n.text.clone()), id);
                        let key = ConstantKey {
                            sort: b.program.keys.sort(sort).unwrap().clone(),
                            name: serde_json::to_string(&(namespace_key(module), &n.text))
                                .expect("strings serialize to JSON")
                                .into(),
                        };
                        construction(
                            m,
                            n.span.clone(),
                            b.program.keys.bind_constant(&b.program.corpus, id, key),
                        )?;
                        b.origin(m, id, n.span.clone())?;
                    }
                }
                Decl::Relation(n, input, parameters) => {
                    let lookup = (module.clone(), n.text.clone(), n.generated);
                    if b.relations.contains_key(&lookup) {
                        return Err(diagnostic(
                            m,
                            n.span.clone(),
                            format!("Duplicate relation {:?}", n.text),
                        ));
                    }
                    let params = parameters
                        .iter()
                        .map(|(p, sort)| Ok(Parameter::new(&p.text, b.sort(m, sort)?)))
                        .collect::<Result<Vec<_>>>()?;
                    let id = if n.generated {
                        if *input || !params.is_empty() {
                            return Err(diagnostic(
                                m,
                                n.span.clone(),
                                "Generated helpers must be zero-arity derived relations",
                            ));
                        }
                        ir_construction(
                            m,
                            n.span.clone(),
                            b.program
                                .corpus
                                .declare_generated_relation_named_in(module, &n.text),
                            &b.program.corpus,
                        )?
                    } else {
                        ir_construction(
                            m,
                            n.span.clone(),
                            b.program.corpus.declare_relation_in(
                                module,
                                &n.text,
                                if *input {
                                    RelationRole::Input
                                } else {
                                    RelationRole::Derived
                                },
                                params,
                            ),
                            &b.program.corpus,
                        )?
                    };
                    b.relations.insert(lookup, id);
                    let key = if n.generated {
                        RelationKey::Generated {
                            owner: OwnerKey::new(
                                format!("denotate/generated/{}", namespace_key(module)),
                                n.text.as_bytes(),
                            ),
                            local: 0,
                        }
                    } else {
                        RelationKey::Named(QualifiedKey::new(
                            namespace_key(module),
                            n.text.as_str(),
                        ))
                    };
                    construction(
                        m,
                        n.span.clone(),
                        b.program.keys.bind_relation(&b.program.corpus, id, key),
                    )?;
                    b.origin(m, id, n.span.clone())?;
                }
                _ => (),
            }
        }
    }
    for sort in b.program.corpus.sorts() {
        b.program.domains.insert(
            sort.id,
            b.program
                .corpus
                .constants()
                .filter(|c| c.sort == sort.id)
                .map(|c| c.id)
                .collect(),
        );
    }
    let mut explicit_domains = BTreeSet::new();
    let mut duplicates = BTreeMap::new();
    for m in &scopes {
        let module = &m.namespace;
        for s in &m.statements {
            match &s.decl {
                Decl::Rule(head, body) => {
                    b.rule(m, s, head, body, &mut duplicates)?;
                }
                Decl::Domain(sort, values) => {
                    let id = b.sort(m, sort)?;
                    if !explicit_domains.insert(id) {
                        return Err(diagnostic(
                            m,
                            s.span.clone(),
                            "More than one explicit domain for this sort in the checked closure",
                        ));
                    }
                    let values = values
                        .iter()
                        .map(|n| b.constant(m, n, id))
                        .collect::<Result<Vec<_>>>()?;
                    if values.iter().collect::<BTreeSet<_>>().len() != values.len() {
                        return Err(diagnostic(m, s.span.clone(), "Duplicate domain member"));
                    }
                    b.program.domains.insert(id, values);
                }
                Decl::Contract {
                    name,
                    assumption,
                    coverage,
                    relation,
                    columns,
                    message,
                } => {
                    let id = b.relation(m, relation)?;
                    let declaration = b.program.corpus.relation(id).unwrap();
                    let mut grouping = Vec::new();
                    for column in columns {
                        let index = declaration
                            .parameters
                            .iter()
                            .position(|p| p.name == column.text)
                            .ok_or_else(|| {
                                diagnostic(
                                    m,
                                    column.span.clone(),
                                    format!("Unknown grouping parameter {:?}", column.text),
                                )
                            })?;
                        if grouping.contains(&index) {
                            return Err(diagnostic(
                                m,
                                column.span.clone(),
                                "Duplicate grouping parameter",
                            ));
                        }
                        grouping.push(index);
                    }
                    if *assumption {
                        if *coverage {
                            return Err(diagnostic(
                                m,
                                s.span.clone(),
                                "at_least_one is supported only for obligations",
                            ));
                        }
                        if declaration.role != RelationRole::Input {
                            return Err(diagnostic(
                                m,
                                relation.span.clone(),
                                "Assumptions may constrain only input relations",
                            ));
                        }
                        let aid = ir_construction(
                            m,
                            s.span.clone(),
                            b.program.corpus.assume_at_most_one_in(
                                module,
                                &name.text,
                                id,
                                grouping.into_iter().map(Column::Index),
                            ),
                            &b.program.corpus,
                        )?;
                        construction(
                            m,
                            name.span.clone(),
                            b.program.keys.bind_assumption(
                                &b.program.corpus,
                                aid,
                                AssumptionKey(QualifiedKey::new(
                                    namespace_key(module),
                                    name.text.as_str(),
                                )),
                            ),
                        )?;
                        b.origin(m, aid, name.span.clone())?;
                    } else {
                        let oid = ir_construction(
                            m,
                            s.span.clone(),
                            if *coverage {
                                b.program.corpus.at_least_one_in(
                                    module,
                                    &name.text,
                                    id,
                                    grouping.into_iter().map(Column::Index),
                                    message,
                                )
                            } else {
                                b.program.corpus.at_most_one_in(
                                    module,
                                    &name.text,
                                    id,
                                    grouping.into_iter().map(Column::Index),
                                    message,
                                )
                            },
                            &b.program.corpus,
                        )?;
                        construction(
                            m,
                            name.span.clone(),
                            b.program.keys.bind_obligation(
                                &b.program.corpus,
                                oid,
                                ObligationKey(QualifiedKey::new(
                                    namespace_key(module),
                                    name.text.as_str(),
                                )),
                            ),
                        )?;
                        b.origin(m, oid, name.span.clone())?;
                    }
                }
                _ => (),
            }
        }
    }
    // Resolve only after every contract in the closure has been declared.
    let mut entries = b
        .program
        .corpus
        .assumptions()
        .map(|a| {
            (
                b.program.corpus.namespace(a.id).unwrap().clone(),
                a.name.clone(),
                crate::index::ContractKind::Assumption,
                Some(OccurrenceId::from(a.id)),
            )
        })
        .chain(b.program.corpus.obligations().map(|o| {
            (
                b.program.corpus.namespace(o.id).unwrap().clone(),
                o.name.clone(),
                crate::index::ContractKind::Obligation,
                Some(OccurrenceId::from(o.id)),
            )
        }))
        .collect::<Vec<_>>();
    // Include forward verification labels for the same wrong-kind diagnostics as the index.
    for m in &scopes {
        for s in &m.statements {
            if let Decl::Verification { name, .. } = &s.decl {
                entries.push((
                    m.namespace.clone(),
                    name.text.clone(),
                    crate::index::ContractKind::Verification,
                    None,
                ));
            }
        }
    }
    for m in &scopes {
        for s in &m.statements {
            if let Decl::Verification {
                name,
                assumptions,
                obligations,
            } = &s.decl
            {
                let scope = crate::index::Scope {
                    namespace: m.namespace.clone(),
                    imports: m.imports.iter().map(|(n, _)| n.clone()).collect(),
                };
                let resolve = |names: &[Name], kind| {
                    crate::index::resolve_contract_list(
                        &scope,
                        names.iter().map(|n| {
                            (
                                crate::index::Name {
                                    namespace: n.namespace.clone(),
                                    text: n.text.clone(),
                                    generated: n.generated,
                                },
                                n.span.clone(),
                            )
                        }),
                        kind,
                        &entries,
                    )
                    .map_err(|errors| {
                        errors
                            .into_iter()
                            .flat_map(|(span, msg)| diagnostic(m, span, msg))
                            .collect::<Vec<_>>()
                    })
                };
                let selected_a = resolve(assumptions, crate::index::ContractKind::Assumption)?;
                let selected_o = resolve(obligations, crate::index::ContractKind::Obligation)?;
                let a = selected_a
                    .iter()
                    .map(|id| {
                        b.program
                            .corpus
                            .assumptions()
                            .find(|a| Some(OccurrenceId::from(a.id)) == *id)
                            .unwrap()
                            .id
                    })
                    .collect::<Vec<_>>();
                let o = selected_o
                    .iter()
                    .map(|id| {
                        b.program
                            .corpus
                            .obligations()
                            .find(|o| Some(OccurrenceId::from(o.id)) == *id)
                            .unwrap()
                            .id
                    })
                    .collect::<Vec<_>>();
                let id = ir_construction(
                    m,
                    s.span.clone(),
                    b.program
                        .corpus
                        .verification_in(&m.namespace, &name.text, a, o),
                    &b.program.corpus,
                )?;
                construction(
                    m,
                    name.span.clone(),
                    b.program.keys.bind_verification(
                        &b.program.corpus,
                        id,
                        VerificationKey(QualifiedKey::new(
                            namespace_key(&m.namespace),
                            name.text.as_str(),
                        )),
                    ),
                )?;
                b.origin(m, id, name.span.clone())?;
            }
        }
    }
    // A declared but unused constant may be outside the explicit domain. A
    // constant actually used by a rule may not: report its current occurrence.
    for rule in b.program.corpus.rules() {
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            for t in atom.arguments() {
                if let Term::Constant(id) = t.value() {
                    let constant = b.program.corpus.constant(*id).unwrap();
                    if !b.program.domains[&constant.sort].contains(id) {
                        let span = b.program.provenance.origins(t.id())[0].span;
                        let source = b.program.sources.snapshot(span.snapshot()).unwrap();
                        return Err(vec![Diagnostic {
                            uri: source.uri.clone(),
                            range: span.byte_range(),
                            message: format!(
                                "Constant {:?} is outside its explicit domain",
                                constant.name
                            ),
                        }]);
                    }
                }
            }
        }
    }
    b.program.keys.validate(&b.program.corpus).map_err(|e| {
        vec![Diagnostic {
            uri: membership.root.clone(),
            range: 0..0,
            message: e.to_string(),
        }]
    })?;
    crate::locations::restore(&mut b.program, documents, resolver)?;
    Ok(b.program)
}
