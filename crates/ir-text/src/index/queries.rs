use super::*;
use crate::{ProgramMembership, SourceFile};
use denotate_analysis::{AtomEvidence, analyze_resolved_rule};
use salsa::Setter;
use std::{
    collections::{BTreeMap, HashMap},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    id: String,
    namespace: Namespace,
    name: Name,
}
#[salsa::input]
struct File {
    uri: String,
    sorts: Vec<Entry>,
    relations: Vec<Entry>,
    constants: Vec<Entry>,
    namespaces: Vec<Entry>,
    details: BTreeMap<String, DeclarationInput>,
}
#[salsa::input]
struct DeclarationInput {
    declaration: Declaration,
}
#[salsa::input]
struct Root {
    files: Vec<File>,
}
#[salsa::input]
struct RuleInput {
    rule: Rule,
}
#[salsa::db]
trait Db: salsa::Database {
    fn record(&self, kind: usize);
}
#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    counts: Arc<[AtomicU64; 8]>,
}
#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn record(&self, kind: usize) {
        self.counts[kind].fetch_add(1, Ordering::Relaxed);
    }
}

fn symbol(db: &dyn Db, file: File, entry: &Entry) -> Symbol {
    Symbol {
        uri: file.uri(db).clone(),
        id: entry.id.clone(),
        name: entry.name.text.clone(),
        module: Some(crate::ast::namespace_key(&entry.namespace)),
    }
}
#[salsa::tracked]
fn candidates(
    db: &dyn Db,
    root: Root,
    scope: Scope,
    name: Option<Name>,
    kind: Kind,
) -> Vec<Symbol> {
    db.record(match kind {
        Kind::Relation => 0,
        Kind::Sort => 1,
        Kind::Constant => 2,
        _ => 3,
    });
    let visible = visible_namespaces(
        &scope.namespace,
        &scope.imports,
        name.as_ref().and_then(|n| n.namespace.as_ref()),
    );
    let mut result = vec![];
    for file in root.files(db) {
        for entry in matching_entries(db, *file, visible.clone(), name.clone(), kind) {
            result.push(symbol(db, *file, entry));
        }
    }
    result.sort_by(|a, b| (&a.uri, &a.id).cmp(&(&b.uri, &b.id)));
    result
}
// Backdating this projection keeps unrelated name queries reusable after a
// declaration changes elsewhere in the same file or selected root.
#[salsa::tracked]
fn matching_entries(
    db: &dyn Db,
    file: File,
    visible: Vec<Namespace>,
    name: Option<Name>,
    kind: Kind,
) -> Vec<Entry> {
    let entries = match kind {
        Kind::Sort => file.sorts(db),
        Kind::Relation => file.relations(db),
        Kind::Constant => file.constants(db),
        Kind::Namespace => file.namespaces(db),
        _ => return vec![],
    };
    let keys = name.as_ref().map(|name| {
        candidate_keys(
            visible.clone(),
            &name.text,
            kind == Kind::Relation && name.generated,
        )
    });
    entries
        .iter()
        .filter(|entry| {
            if kind == Kind::Namespace {
                return name
                    .as_ref()
                    .is_none_or(|name| name.text == entry.name.text);
            }
            match &keys {
                Some(keys) => keys.contains(&(
                    entry.namespace.clone(),
                    entry.name.text.clone(),
                    kind == Kind::Relation && entry.name.generated,
                )),
                None => visible.contains(&entry.namespace),
            }
        })
        .cloned()
        .collect()
}
#[salsa::tracked]
fn declaration(db: &dyn Db, root: Root, uri: String, id: String) -> Option<Declaration> {
    db.record(7);
    let file = root.files(db).iter().find(|f| f.uri(db) == &uri)?;
    declaration_input(db, *file, id).map(|input| input.declaration(db).clone())
}
#[salsa::tracked]
fn declaration_input(db: &dyn Db, file: File, id: String) -> Option<DeclarationInput> {
    file.details(db).get(&id).copied()
}

fn unique(matches: &[Symbol]) -> Option<Symbol> {
    if matches.len() == 1 {
        matches.first().cloned()
    } else {
        None
    }
}
fn detail(db: &dyn Db, root: Root, target: &Symbol) -> Option<Declaration> {
    declaration(db, root, target.uri.clone(), target.id.clone()).clone()
}
#[salsa::tracked]
fn expected_sort(db: &dyn Db, root: Root, scope: Scope, expected: Expected) -> Option<Symbol> {
    db.record(5);
    let (scope, name) = match expected {
        Expected::Sort(name) => (scope, name),
        Expected::Argument(relation, index) => {
            let target = unique(candidates(db, root, scope, Some(relation), Kind::Relation))?;
            let d = detail(db, root, &target)?;
            (d.scope, d.parameters?.get(index)?.1.clone()?)
        }
    };
    unique(candidates(db, root, scope, Some(name), Kind::Sort))
}
#[salsa::tracked]
fn constants(
    db: &dyn Db,
    root: Root,
    scope: Scope,
    expected: Expected,
    name: Option<Name>,
) -> Vec<Symbol> {
    db.record(6);
    let Some(sort) = expected_sort(db, root, scope.clone(), expected) else {
        return vec![];
    };
    candidates(db, root, scope, name, Kind::Constant)
        .into_iter()
        .filter(|target| {
            let Some(d) = detail(db, root, target) else {
                return false;
            };
            d.sort
                .and_then(|name| expected_sort(db, root, d.scope, Expected::Sort(name)).clone())
                == Some(sort.clone())
        })
        .cloned()
        .collect()
}
#[salsa::tracked]
fn rule_analysis(db: &dyn Db, root: Root, input: RuleInput) -> RuleAnalysis {
    db.record(4);
    let rule = input.rule(db);
    let facts = rule
        .syntax
        .atoms
        .iter()
        .zip(&rule.relations)
        .map(|(atom, relation)| {
            let target = unique(candidates(
                db,
                root,
                rule.scope.clone(),
                Some(relation.clone()),
                Kind::Relation,
            ));
            let declaration = target.and_then(|s| detail(db, root, &s));
            let arity_error = declaration
                .as_ref()
                .and_then(|d| d.parameters.as_ref())
                .and_then(|p| {
                    let count = p.len();
                    let actual = atom.variables.len();
                    (count != actual).then(|| {
                        format!(
                            "Relation '{}' expects {count} argument{}, got {actual}.",
                            relation.spelling(),
                            if count == 1 { "" } else { "s" }
                        )
                    })
                });
            AtomEvidence {
                arity_error,
                input: declaration.is_some_and(|d| d.input),
                sorts: (0..atom.variables.len())
                    .map(|i| {
                        expected_sort(
                            db,
                            root,
                            rule.scope.clone(),
                            Expected::Argument(relation.clone(), i),
                        )
                        .clone()
                    })
                    .collect(),
            }
        })
        .collect::<Vec<_>>();
    analyze_resolved_rule(&rule.syntax, &facts)
}

/// Shared file projections, dependency-tracked root contexts, and current anchors.
/// Queries never capture source ranges in Salsa: trivia can move every range
/// without invalidating semantic answers.
#[derive(Default)]
pub struct Index {
    db: Database,
    inputs: BTreeMap<String, File>,
    roots: BTreeMap<String, Root>,
    rules: HashMap<(String, String), RuleInput>,
    pub files: BTreeMap<String, Arc<Projection>>,
    projections: u64,
}
impl Index {
    fn file(&mut self, uri: &str) -> File {
        *self.inputs.entry(uri.into()).or_insert_with(|| {
            File::new(
                &self.db,
                uri.to_owned(),
                vec![],
                vec![],
                vec![],
                vec![],
                BTreeMap::new(),
            )
        })
    }
    pub fn update(&mut self, source: SourceFile, tree: tree_sitter::Tree) {
        if let Some(previous) = self
            .files
            .get_mut(&source.uri)
            .filter(|p| p.source.text == source.text)
        {
            let projection = Arc::make_mut(previous);
            projection.source = source;
            return;
        }
        let previous = self.files.get(&source.uri).cloned();
        let projection = Projection::new(source, tree, previous.as_deref());
        self.install(projection);
    }
    fn install(&mut self, projection: Projection) {
        let uri = projection.source.uri.clone();
        let file = self.file(&uri);
        let entries = |kind| {
            projection
                .declarations
                .values()
                .filter(|d| d.kind == kind)
                .map(|d| Entry {
                    id: d.id.clone(),
                    namespace: d.scope.namespace.clone(),
                    name: d.name.clone(),
                })
                .collect::<Vec<_>>()
        };
        let sorts = entries(Kind::Sort);
        let relations = entries(Kind::Relation);
        let constants = entries(Kind::Constant);
        // A namespace exists through declarations and through explicit empty
        // blocks. Parents also exist, even if they have no direct declarations.
        let mut namespaces: BTreeMap<String, Vec<Entry>> = BTreeMap::new();
        for d in projection
            .declarations
            .values()
            .filter(|d| d.kind != Kind::Alias)
        {
            for length in 1..=d.scope.namespace.segments().len() {
                let ns =
                    Namespace::new(d.scope.namespace.segments()[..length].iter().cloned()).unwrap();
                let key = crate::ast::namespace_key(&ns);
                let entry = Entry {
                    id: d.id.clone(),
                    namespace: ns,
                    name: Name::bare(key.clone()),
                };
                let explicit =
                    d.kind == Kind::Namespace && length == d.scope.namespace.segments().len();
                let entries = namespaces.entry(key).or_default();
                if explicit {
                    entries.retain(|e| {
                        projection.declarations[&e.id].kind == Kind::Namespace
                            && projection.declarations[&e.id].scope.namespace == e.namespace
                    });
                    entries.push(entry);
                } else if entries.is_empty() {
                    entries.push(entry);
                }
            }
        }
        let namespaces = namespaces.into_values().flatten().collect::<Vec<_>>();
        if *file.sorts(&self.db) != sorts {
            file.set_sorts(&mut self.db).to(sorts);
        }
        if *file.relations(&self.db) != relations {
            file.set_relations(&mut self.db).to(relations);
        }
        if *file.constants(&self.db) != constants {
            file.set_constants(&mut self.db).to(constants);
        }
        if *file.namespaces(&self.db) != namespaces {
            file.set_namespaces(&mut self.db).to(namespaces);
        }
        let mut details = file.details(&self.db).clone();
        details.retain(|id, _| projection.declarations.contains_key(id));
        for (id, declaration) in &projection.declarations {
            let input = details
                .entry(id.clone())
                .or_insert_with(|| DeclarationInput::new(&self.db, declaration.clone()));
            if input.declaration(&self.db) != declaration {
                input.set_declaration(&mut self.db).to(declaration.clone());
            }
        }
        if file.details(&self.db) != &details {
            file.set_details(&mut self.db).to(details);
        }
        self.rules
            .retain(|(u, id), _| u != &uri || projection.rules.contains_key(id));
        for (id, rule) in &projection.rules {
            let input = self
                .rules
                .entry((uri.clone(), id.clone()))
                .or_insert_with(|| RuleInput::new(&self.db, rule.clone()));
            if *input.rule(&self.db) != *rule {
                input.set_rule(&mut self.db).to(rule.clone());
            }
        }
        self.projections += 1;
        self.files.insert(uri, Arc::new(projection));
    }
    pub fn remove(&mut self, uri: &str) {
        self.files.remove(uri);
        self.rules.retain(|(u, _), _| u != uri);
        if let Some(&file) = self.inputs.get(uri) {
            file.set_sorts(&mut self.db).to(vec![]);
            file.set_relations(&mut self.db).to(vec![]);
            file.set_constants(&mut self.db).to(vec![]);
            file.set_namespaces(&mut self.db).to(vec![]);
            file.set_details(&mut self.db).to(BTreeMap::new());
        }
    }
    pub fn set_membership(&mut self, membership: &ProgramMembership) -> crate::Result<()> {
        let files = membership
            .members()?
            .into_keys()
            .map(|uri| self.file(&uri))
            .collect::<Vec<_>>();
        if let Some(&root) = self.roots.get(&membership.root) {
            if *root.files(&self.db) != files {
                root.set_files(&mut self.db).to(files);
            }
        } else {
            self.roots
                .insert(membership.root.clone(), Root::new(&self.db, files));
        }
        Ok(())
    }
    pub fn candidates(
        &self,
        root: &str,
        uri: &str,
        scope: &Scope,
        lookup: &Lookup,
        name: Option<&Name>,
    ) -> Vec<Symbol> {
        let root_name = root;
        let Some(&root) = self.roots.get(root) else {
            return vec![];
        };
        match lookup {
            Lookup::Contract(kind) => {
                let entries = self.contract_entries(root_name);
                matching_contracts(scope, name, &entries)
                    .into_iter()
                    .filter(|e| e.2 == *kind)
                    .map(|e| Symbol {
                        uri: e.3.0.clone(),
                        id: e.3.1.clone(),
                        name: e.1.clone(),
                        module: Some(crate::ast::namespace_key(&e.0)),
                    })
                    .collect()
            }
            Lookup::Name(Kind::Alias) => self
                .files
                .get(uri)
                .into_iter()
                .flat_map(|p| p.declarations.values())
                .filter(|d| d.kind == Kind::Alias && name.is_none_or(|n| d.name == *n))
                .map(|d| Symbol {
                    uri: uri.into(),
                    id: d.id.clone(),
                    name: d.name.text.clone(),
                    module: None,
                })
                .collect(),
            Lookup::Name(kind) => {
                candidates(&self.db, root, scope.clone(), name.cloned(), *kind).clone()
            }
            Lookup::Constant(expected) => constants(
                &self.db,
                root,
                scope.clone(),
                expected.clone(),
                name.cloned(),
            )
            .clone(),
            Lookup::Parameter(relation) => {
                let Some(target) = unique(candidates(
                    &self.db,
                    root,
                    scope.clone(),
                    Some(relation.clone()),
                    Kind::Relation,
                )) else {
                    return vec![];
                };
                self.files
                    .get(&target.uri)
                    .into_iter()
                    .flat_map(|p| p.declarations.values())
                    .filter(|d| {
                        d.kind == Kind::Parameter
                            && d.parent.as_deref() == Some(&target.id)
                            && name.is_none_or(|n| d.name.text == n.text)
                    })
                    .map(|d| Symbol {
                        uri: target.uri.clone(),
                        id: d.id.clone(),
                        name: d.name.text.clone(),
                        module: target.module.clone(),
                    })
                    .collect()
            }
            Lookup::Declaration(id) => self
                .files
                .get(uri)
                .and_then(|f| f.declarations.get(id))
                .map(|d| Symbol {
                    uri: uri.into(),
                    id: id.clone(),
                    name: d.name.text.clone(),
                    module: Some(crate::ast::namespace_key(&d.scope.namespace)),
                })
                .into_iter()
                .collect(),
            _ => vec![],
        }
    }
    pub fn expected_sort(&self, root: &str, scope: &Scope, expected: &Expected) -> Option<Symbol> {
        expected_sort(
            &self.db,
            *self.roots.get(root)?,
            scope.clone(),
            expected.clone(),
        )
        .clone()
    }
    pub fn rule_analysis(&self, root: &str, uri: &str, id: &str) -> RuleAnalysis {
        match (
            self.roots.get(root),
            self.rules.get(&(uri.into(), id.into())),
        ) {
            (Some(&root), Some(&rule)) => rule_analysis(&self.db, root, rule).clone(),
            _ => RuleAnalysis::default(),
        }
    }
    pub fn declaration(&self, target: &Symbol) -> Option<&Declaration> {
        self.files.get(&target.uri)?.declarations.get(&target.id)
    }
    fn contract_entries(
        &self,
        root: &str,
    ) -> Vec<(Namespace, String, ContractKind, (String, String))> {
        if !self.roots.contains_key(root) {
            return vec![];
        }
        self.roots[root]
            .files(&self.db)
            .iter()
            .filter_map(|f| self.files.get(f.uri(&self.db)))
            .flat_map(|f| {
                f.declarations.values().filter_map(|d| {
                    d.contract.map(|kind| {
                        (
                            d.scope.namespace.clone(),
                            d.name.text.clone(),
                            kind,
                            (f.source.uri.clone(), d.id.clone()),
                        )
                    })
                })
            })
            .collect::<Vec<_>>()
    }

    pub fn diagnostics(&self, root: &str, uri: &str) -> Vec<Issue> {
        let Some(file) = self.files.get(uri) else {
            return vec![];
        };
        if !self.roots.contains_key(root) {
            return file.issues.clone();
        }
        let mut out = file.issues.clone();
        let contracts = self.contract_entries(root);
        for v in &file.verifications {
            for (kind, names) in [
                (ContractKind::Assumption, &v.assumptions),
                (ContractKind::Obligation, &v.obligations),
                (ContractKind::Notice, &v.notices),
            ] {
                if let Err(errors) =
                    resolve_contract_list(&v.scope, names.clone(), kind, &contracts)
                {
                    out.extend(errors.into_iter().map(|(span, message)| Issue {
                        span,
                        code: "verification-reference".into(),
                        message,
                        warning: false,
                    }));
                }
            }
        }
        let mut add = |span: Range<usize>, code: &str, message: String| {
            out.push(Issue {
                span,
                code: code.into(),
                message,
                warning: false,
            })
        };
        for d in file.declarations.values() {
            if let Some(kind) = d.contract {
                if contracts
                    .iter()
                    .filter(|(ns, name, k, _)| {
                        *ns == d.scope.namespace && *name == d.name.text && *k == kind
                    })
                    .count()
                    > 1
                {
                    add(
                        file.anchors[&d.id].clone(),
                        "duplicate-declaration",
                        format!("Duplicate {} name {:?}", kind.label(), d.name.text),
                    );
                }
            }
            if d.kind == Kind::Relation
                && d.name.generated
                && (d.input || d.parameters.as_ref().is_some_and(|p| !p.is_empty()))
            {
                add(
                    file.anchors[&d.id].clone(),
                    "generated-helper",
                    "Generated helpers must be zero-arity derived relations".into(),
                );
            }
            if matches!(
                d.kind,
                Kind::Sort | Kind::Relation | Kind::Constant | Kind::Alias
            ) {
                let name = Name {
                    namespace: Some(d.scope.namespace.clone()),
                    ..d.name.clone()
                };
                let lookup = if d.kind == Kind::Constant {
                    d.sort.clone().map(|s| Lookup::Constant(Expected::Sort(s)))
                } else {
                    Some(Lookup::Name(d.kind))
                };
                if let Some(lookup) = lookup {
                    let matches = self.candidates(
                        root,
                        uri,
                        &d.scope,
                        &lookup,
                        Some(if d.kind == Kind::Alias {
                            &d.name
                        } else {
                            &name
                        }),
                    );
                    if matches.len() > 1 {
                        add(
                            file.anchors[&d.id].clone(),
                            "duplicate-declaration",
                            format!("Duplicate declaration '{}'.", d.name.text),
                        );
                    }
                }
            }
        }
        for r in &file.references {
            if matches!(
                r.lookup,
                // Contract lists are diagnosed above, including duplicate selections.
                Lookup::Contract(_)
                    | Lookup::Declaration(_)
                    | Lookup::Variable { .. }
                    | Lookup::Anonymous(_)
            ) {
                continue;
            }
            let matches = self.candidates(root, uri, &r.scope, &r.lookup, Some(&r.name));
            if matches.len() == 1
                || (!matches.is_empty() && r.lookup == Lookup::Name(Kind::Namespace))
            {
                continue;
            }
            let label = match &r.lookup {
                Lookup::Name(k) => k.label(),
                Lookup::Constant(_) => "constant",
                Lookup::Parameter(_) => "parameter",
                _ => continue,
            };
            if let Lookup::Constant(expected) = &r.lookup {
                // A missing/ambiguous relation or damaged signature is not an
                // expected sort. Suppress the dependent constant diagnostic.
                if let Some(message) = self.constant_error(root, uri, r, expected) {
                    add(r.span.clone(), "resolution", message);
                }
                if matches.is_empty() {
                    continue;
                }
            }
            if let Lookup::Parameter(relation) = &r.lookup {
                let targets = self.candidates(
                    root,
                    uri,
                    &r.scope,
                    &Lookup::Name(Kind::Relation),
                    Some(relation),
                );
                if targets.len() != 1
                    || self
                        .declaration(&targets[0])
                        .is_none_or(|d| d.parameters.is_none())
                {
                    continue;
                }
            }
            let message = if matches.is_empty() {
                format!("Unknown {label} '{}'.", r.name.spelling())
            } else {
                let mut modules = matches
                    .iter()
                    .map(|s| {
                        s.module
                            .as_deref()
                            .filter(|s| !s.is_empty())
                            .unwrap_or("::")
                    })
                    .collect::<Vec<_>>();
                modules.sort();
                format!(
                    "Ambiguous name '{}': {} visible declarations ({}).",
                    r.name.spelling(),
                    matches.len(),
                    modules.join(", ")
                )
            };
            add(r.span.clone(), "resolution", message);
        }
        for id in file.rules.keys() {
            for issue in self.rule_analysis(root, uri, id).diagnostics {
                if let Some(span) = file.rule_anchors[id].get(&issue.id) {
                    out.push(Issue {
                        span: span.clone(),
                        code: issue.code,
                        message: issue.message,
                        warning: issue.warning,
                    });
                }
            }
        }
        out
    }
    fn constant_error(
        &self,
        root: &str,
        uri: &str,
        r: &Reference,
        expected: &Expected,
    ) -> Option<String> {
        let all = self.candidates(
            root,
            uri,
            &r.scope,
            &Lookup::Name(Kind::Constant),
            Some(&r.name),
        );
        if let Expected::Argument(relation, index) = expected {
            let targets = self.candidates(
                root,
                uri,
                &r.scope,
                &Lookup::Name(Kind::Relation),
                Some(relation),
            );
            let [target] = targets.as_slice() else {
                return None;
            };
            let parameters = self.declaration(target)?.parameters.as_ref()?;
            if *index >= parameters.len() {
                return Some(if all.is_empty() {
                    format!(
                        "Unknown constant '{}' (no visible declaration); argument {} is beyond relation '{}'s signature.",
                        r.name.spelling(),
                        index + 1,
                        relation.spelling()
                    )
                } else {
                    format!(
                        "Extra argument '{}' to relation '{}': no parameter {} supplies an expected sort for constant lookup.",
                        r.name.spelling(),
                        relation.spelling(),
                        index + 1
                    )
                });
            }
        }
        let expected = self.expected_sort(root, &r.scope, expected)?;
        if !self
            .candidates(root, uri, &r.scope, &r.lookup, Some(&r.name))
            .is_empty()
        {
            return None;
        }
        let sorts = all
            .iter()
            .map(|s| {
                self.declaration(s).and_then(|d| {
                    self.expected_sort(root, &d.scope, &Expected::Sort(d.sort.clone()?))
                })
            })
            .collect::<Vec<_>>();
        let qualify = sorts
            .iter()
            .flatten()
            .any(|s| s != &expected && s.name == expected.name);
        let label = |s: &Symbol| {
            if qualify {
                format!(
                    "{}::{}",
                    s.module.as_deref().unwrap_or("?"),
                    super::quote(&s.name)
                )
            } else {
                s.name.clone()
            }
        };
        let mut found = sorts
            .iter()
            .map(|s| {
                s.as_ref()
                    .map(&label)
                    .unwrap_or_else(|| "unresolved sort".into())
            })
            .collect::<Vec<_>>();
        found.sort();
        found.dedup();
        Some(format!(
            "No constant '{}' of sort {} ({}).",
            r.name.spelling(),
            label(&expected),
            if found.is_empty() {
                "no visible declaration".into()
            } else {
                format!("found: {}", found.join(", "))
            }
        ))
    }
    pub fn query_counts(&self) -> [u64; 8] {
        std::array::from_fn(|i| self.db.counts[i].load(Ordering::Relaxed))
    }
    pub fn projections(&self) -> u64 {
        self.projections
    }
}
