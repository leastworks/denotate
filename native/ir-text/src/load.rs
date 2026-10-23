use crate::{
    Diagnostic, Result, SourceFile,
    ast::{self, Atom as AstAtom, Decl, Module, Name, Statement},
    error,
};
use denotate_check::{BackendIdentity, CheckRequest, Domains, InputAtMostOne, Limits};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub name: String,
    pub uri: String,
    pub revision: u64,
    pub ownership: String,
    pub imports: Vec<String>,
    pub snapshot: SnapshotId,
    /// Exact location syntax for step 2; it is not interpreted as DSL origins yet.
    pub location_syntax: Vec<SourceSpan>,
}
#[derive(Clone, Debug)]
pub struct Assumption {
    pub name: QualifiedKey,
    pub constraint: InputAtMostOne,
    pub location: SourceSpan,
}
#[derive(Debug)]
pub struct LoadedProgram {
    pub root: String,
    pub corpus: Corpus,
    pub keys: SemanticKeys,
    pub sources: Sources,
    pub provenance: Provenance,
    pub domains: Domains,
    pub assumptions: Vec<Assumption>,
    pub modules: Vec<ModuleInfo>,
    /// Presentation ownership is separate from provenance and semantic keys.
    pub owners: BTreeMap<OccurrenceId, String>,
}
impl LoadedProgram {
    pub fn request(
        &self,
        limits: &Limits,
        backend: BackendIdentity,
    ) -> std::result::Result<CheckRequest, denotate_check::CheckError> {
        let constraints = self
            .assumptions
            .iter()
            .map(|a| a.constraint.clone())
            .collect::<Vec<_>>();
        let mut request = CheckRequest::all_obligations(
            &self.corpus,
            &self.keys,
            &self.domains,
            &constraints,
            limits,
        )?;
        request.backend = backend;
        Ok(request)
    }
}

fn registry(documents: &[SourceFile]) -> BTreeMap<String, Vec<&SourceFile>> {
    let mut map = BTreeMap::<String, Vec<&SourceFile>>::new();
    for source in documents {
        if let Some(name) = ast::header(source) {
            map.entry(name).or_default().push(source);
        }
    }
    map
}
fn closure(root: &str, documents: &[SourceFile]) -> Result<BTreeMap<String, Module>> {
    let index = registry(documents);
    let fallback = SourceFile::new("denotate:workspace", 0, "");
    let mut pending = vec![(root.to_owned(), &fallback, 0..0)];
    let mut result = BTreeMap::new();
    // Pending sources must borrow the caller's immutable document list, not ASTs.
    while let Some((name, importer, span)) = pending.pop() {
        if result.contains_key(&name) {
            continue;
        }
        let candidates = index
            .get(&name)
            .ok_or_else(|| error(importer, span.clone(), format!("Unknown module {name:?}")))?;
        if candidates.len() != 1 {
            return Err(error(importer, span, format!("Ambiguous module {name:?}")));
        }
        let source = candidates[0];
        let module = ast::parse(source)?;
        for import in &module.imports {
            pending.push((import.text.clone(), source, import.span.clone()));
        }
        result.insert(name, module);
    }
    Ok(result)
}

/// Root discovery is a pure policy helper for the future LSP integration. Only
/// ownership=root modules designate export entry points. With no containing
/// export root the document is its own root; ambiguity requires explicit choice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActiveRoot {
    Selected(String),
    NeedsSelection(Vec<String>),
}
pub fn roots(documents: &[SourceFile]) -> Result<BTreeMap<String, ActiveRoot>> {
    let mut parsed = BTreeMap::new();
    for (name, candidates) in registry(documents) {
        if candidates.len() != 1 {
            return Err(error(
                candidates[0],
                0..0,
                format!("Ambiguous module {name:?}"),
            ));
        }
        parsed.insert(name, ast::parse(candidates[0])?);
    }
    let mut containing = BTreeMap::<String, Vec<String>>::new();
    for (root, m) in &parsed {
        if m.ownership != "root" {
            continue;
        }
        for name in closure(root, documents)?.keys() {
            containing
                .entry(name.clone())
                .or_default()
                .push(root.clone());
        }
    }
    Ok(parsed
        .into_iter()
        .map(|(name, m)| {
            let candidates = containing.remove(&name).unwrap_or_else(|| vec![name]);
            let choice = if candidates.len() == 1 {
                ActiveRoot::Selected(candidates[0].clone())
            } else {
                ActiveRoot::NeedsSelection(candidates)
            };
            (m.source.uri, choice)
        })
        .collect())
}

struct Builder {
    program: LoadedProgram,
    snapshots: BTreeMap<String, SnapshotId>,
    sorts: BTreeMap<(String, String), SortId>,
    relations: BTreeMap<(String, String, bool), RelationId>,
    constants: BTreeMap<(String, SortId, String), ConstantId>,
}
fn diagnostic(m: &Module, span: Range<usize>, message: impl Into<String>) -> Vec<Diagnostic> {
    error(&m.source, span, message)
}
fn construction<T>(
    m: &Module,
    span: Range<usize>,
    value: std::result::Result<T, impl std::fmt::Display>,
) -> Result<T> {
    value.map_err(|e| diagnostic(m, span, e.to_string()))
}

fn ir_construction<T>(
    m: &Module,
    span: Range<usize>,
    value: std::result::Result<T, ConstructionError>,
    corpus: &Corpus,
) -> Result<T> {
    let qualified = |id: OccurrenceId, name: &str| match corpus
        .declaration_namespace(id)
        .filter(|ns| !ns.is_global())
    {
        Some(ns) => format!("{}::{name}", ns.segments().join("::")),
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
        };
        diagnostic(m, span, message)
    })
}
fn visible<'a>(m: &'a Module, name: &Name) -> Result<Vec<&'a str>> {
    let all = std::iter::once(m.name.as_str())
        .chain(m.imports.iter().map(|n| n.text.as_str()))
        .collect::<BTreeSet<_>>();
    if let Some(module) = &name.module {
        if let Some(found) = all.into_iter().find(|n| *n == module) {
            return Ok(vec![found]);
        }
        return Err(diagnostic(
            m,
            name.span.clone(),
            format!("Module {module:?} is not directly imported"),
        ));
    }
    Ok(all.into_iter().collect())
}
fn one<T: Copy>(
    m: &Module,
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
                "Ambiguous {kind} {:?}; qualify it with its module",
                name.text
            ),
        )),
    }
}
impl Builder {
    fn sort(&self, m: &Module, n: &Name) -> Result<SortId> {
        one(
            m,
            n,
            "sort",
            visible(m, n)?
                .into_iter()
                .filter_map(|module| self.sorts.get(&(module.into(), n.text.clone())).copied()),
        )
    }
    fn relation(&self, m: &Module, n: &Name) -> Result<RelationId> {
        one(
            m,
            n,
            "relation",
            visible(m, n)?.into_iter().filter_map(|module| {
                self.relations
                    .get(&(module.into(), n.text.clone(), n.generated))
                    .copied()
            }),
        )
    }
    fn constant(&self, m: &Module, n: &Name, sort: SortId) -> Result<ConstantId> {
        one(
            m,
            n,
            "constant of the expected sort",
            visible(m, n)?.into_iter().filter_map(|module| {
                self.constants
                    .get(&(module.into(), sort, n.text.clone()))
                    .copied()
            }),
        )
    }
    fn span(&self, m: &Module, range: Range<usize>) -> Result<SourceSpan> {
        construction(
            m,
            range.clone(),
            self.program.sources.span(self.snapshots[&m.name], range),
        )
    }
    fn origin(
        &mut self,
        m: &Module,
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
        self.program.owners.insert(id, m.name.clone());
        Ok(())
    }
    fn atom(
        &mut self,
        m: &Module,
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
        m: &Module,
        statement: &Statement,
        head: &AstAtom,
        body: &[(bool, AstAtom)],
        duplicate: usize,
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
        let id = ir_construction(
            m,
            statement.span.clone(),
            self.program.corpus.add_rule_in(&m.name, h, b),
            &self.program.corpus,
        )?;
        let owner = OwnerKey::new(
            format!("denotate/rule/{}", m.name),
            format!("{}/{duplicate}", statement.semantic).into_bytes(),
        );
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

/// Load exactly one root's transitive closure. Declaration passes precede rule
/// installation, so import cycles and declaration order are safe. Name visibility
/// remains local + direct imports (matching B); qualify ambiguous references.
pub fn load(root: &str, documents: &[SourceFile]) -> Result<LoadedProgram> {
    let modules = closure(root, documents)?;
    let mut b = Builder {
        program: LoadedProgram {
            root: root.into(),
            corpus: Corpus::new(),
            keys: SemanticKeys::default(),
            sources: Sources::new(),
            provenance: Provenance::new(),
            domains: BTreeMap::new(),
            assumptions: Vec::new(),
            modules: Vec::new(),
            owners: BTreeMap::new(),
        },
        snapshots: BTreeMap::new(),
        sorts: BTreeMap::new(),
        relations: BTreeMap::new(),
        constants: BTreeMap::new(),
    };
    for (name, m) in &modules {
        let snapshot = construction(
            m,
            0..0,
            b.program.sources.add(
                &m.source.uri,
                m.source.revision,
                "denotate",
                m.source.text.clone(),
            ),
        )?;
        b.snapshots.insert(name.clone(), snapshot);
        let locations = m
            .locations
            .iter()
            .map(|r| construction(m, r.clone(), b.program.sources.span(snapshot, r.clone())))
            .collect::<Result<_>>()?;
        b.program.modules.push(ModuleInfo {
            name: name.clone(),
            uri: m.source.uri.clone(),
            revision: m.source.revision,
            ownership: m.ownership.clone(),
            imports: m.imports.iter().map(|n| n.text.clone()).collect(),
            snapshot,
            location_syntax: locations,
        });
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
                        SortKey(QualifiedKey::new(name.as_str(), n.text.as_str())),
                    ),
                )?;
                b.origin(m, id, n.span.clone())?;
            }
        }
    }
    // Install all signatures/constants before resolving rules across modules.
    for (module, m) in &modules {
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
                            name: format!("{:?}", (&module, &n.text)).into(),
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
                                format!("denotate/generated/{module}"),
                                n.text.as_bytes(),
                            ),
                            local: 0,
                        }
                    } else {
                        RelationKey::Named(QualifiedKey::new(module.as_str(), n.text.as_str()))
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
    for (module, m) in &modules {
        let mut duplicates = BTreeMap::<String, usize>::new();
        let mut assumption_names = BTreeSet::new();
        for s in &m.statements {
            match &s.decl {
                Decl::Rule(head, body) => {
                    let duplicate = duplicates.entry(s.semantic.clone()).or_default();
                    b.rule(m, s, head, body, *duplicate)?;
                    *duplicate += 1;
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
                        if declaration.role != RelationRole::Input {
                            return Err(diagnostic(
                                m,
                                relation.span.clone(),
                                "Assumptions may constrain only input relations",
                            ));
                        }
                        if !assumption_names.insert(name.text.clone()) {
                            return Err(diagnostic(
                                m,
                                name.span.clone(),
                                "Duplicate assumption name",
                            ));
                        }
                        b.program.assumptions.push(Assumption {
                            name: QualifiedKey::new(module.as_str(), name.text.as_str()),
                            constraint: InputAtMostOne {
                                relation: id,
                                group_by: grouping,
                            },
                            location: b.span(m, s.span.clone())?,
                        });
                    } else {
                        let oid = ir_construction(
                            m,
                            s.span.clone(),
                            b.program.corpus.at_most_one_in(
                                module,
                                &name.text,
                                id,
                                grouping.into_iter().map(Column::Index),
                                message,
                            ),
                            &b.program.corpus,
                        )?;
                        construction(
                            m,
                            name.span.clone(),
                            b.program.keys.bind_obligation(
                                &b.program.corpus,
                                oid,
                                ObligationKey(QualifiedKey::new(
                                    module.as_str(),
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
    let m = &modules[root];
    construction(m, 0..0, b.program.keys.validate(&b.program.corpus))?;
    Ok(b.program)
}
