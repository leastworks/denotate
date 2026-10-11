use salsa::Setter;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

mod arguments;
mod declarations;
mod rules;
pub use arguments::ConstantDiagnostic;
pub use declarations::{DeclarationDiagnostic, NameKind};
pub use rules::{RuleAnalysis, RuleSyntax};

/// Partial syntax projection: identity and semantic fields only, never spans.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedDeclaration {
    pub id: String,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Signature {
    pub id: String,
    // None means recovery did not preserve a reliable parameter list.
    pub parameters: Option<Vec<Option<String>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Constant {
    pub id: String,
    pub name: String,
    pub sort: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Document {
    pub uri: String,
    pub directory: String,
    pub filename: String,
    pub module: Option<String>,
    pub imports: Vec<Option<String>>,
    pub relations: Vec<NamedDeclaration>,
    pub sorts: Vec<NamedDeclaration>,
    pub signatures: Vec<Signature>,
    pub constants: Vec<Constant>,
    #[serde(default)]
    pub input_relations: Vec<String>,
    #[serde(default)]
    pub rules: Vec<RuleSyntax>,
}

#[salsa::input]
struct File {
    uri: String,
    directory: String,
    filename: String,
    module: Option<String>,
    imports: Vec<Option<String>>,
    relations: Vec<NamedDeclaration>,
    sorts: Vec<NamedDeclaration>,
    signatures: Vec<Signature>,
    constants: Vec<Constant>,
    input_relations: Vec<String>,
    present: bool,
}

#[salsa::input]
struct Catalog {
    files: Vec<File>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Symbol {
    pub uri: String,
    pub id: String,
    pub module: Option<String>,
    pub name: String,
}

#[salsa::db]
trait Db: salsa::Database {
    fn record_query(&self, kind: QueryKind);
}

enum QueryKind {
    Relations,
    Sorts,
    ExpectedSorts,
    Constants,
    Rules,
    ConstantDiagnostics,
    SortLabels,
    Modules,
    Declarations,
    NameDiagnostics,
}

#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    executions: Arc<[AtomicU32; 10]>,
}

#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn record_query(&self, kind: QueryKind) {
        self.executions[kind as usize].fetch_add(1, Ordering::Relaxed);
    }
}

#[salsa::tracked]
fn visible_files(db: &dyn Db, catalog: Catalog, file: File) -> Vec<File> {
    if !file.present(db) {
        return vec![];
    }
    let imports = file.imports(db);
    let mut visible = vec![file];
    for &candidate in declarations::importable_files(db, catalog, file) {
        if candidate == file {
            continue;
        }
        let Some(module) = candidate.module(db) else {
            continue;
        };
        if imports.iter().any(|item| item.as_ref() == Some(module)) {
            visible.push(candidate);
        }
    }
    visible
}

fn symbol(db: &dyn Db, file: File, id: &str, name: &str) -> Symbol {
    Symbol {
        uri: file.uri(db).clone(),
        id: id.into(),
        module: file.module(db).clone(),
        name: name.into(),
    }
}

#[salsa::tracked]
fn visible_relations(db: &dyn Db, catalog: Catalog, file: File) -> Vec<Symbol> {
    db.record_query(QueryKind::Relations);
    let mut result = vec![];
    for &owner in visible_files(db, catalog, file) {
        for relation in owner.relations(db) {
            result.push(symbol(db, owner, &relation.id, &relation.name));
        }
    }
    result.sort_by(|a, b| (&a.uri, &a.id).cmp(&(&b.uri, &b.id)));
    result
}

#[salsa::tracked]
fn visible_sorts(db: &dyn Db, catalog: Catalog, file: File) -> Vec<Symbol> {
    db.record_query(QueryKind::Sorts);
    visible_files(db, catalog, file)
        .iter()
        .flat_map(|&owner| {
            owner
                .sorts(db)
                .iter()
                .map(move |sort| symbol(db, owner, &sort.id, &sort.name))
        })
        .collect()
}

#[salsa::tracked]
fn resolve_sort(db: &dyn Db, catalog: Catalog, file: File, name: String) -> Option<Symbol> {
    let mut matches = visible_sorts(db, catalog, file)
        .iter()
        .filter(|sort| sort.name == name);
    let first = matches.next()?;
    // Same spelling in two modules is ambiguity, never first-match selection.
    if matches.next().is_some() {
        return None;
    }
    Some(first.clone())
}

#[salsa::tracked]
fn resolved_signature(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: String,
) -> Option<(File, Signature)> {
    let mut matches = visible_relations(db, catalog, file)
        .iter()
        .filter(|item| item.name == relation);
    let target = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let &owner = visible_files(db, catalog, file)
        .iter()
        .find(|owner| owner.uri(db) == &target.uri)?;
    let signature = owner
        .signatures(db)
        .iter()
        .find(|item| item.id == target.id)?;
    Some((owner, signature.clone()))
}

#[salsa::tracked]
fn expected_argument_sort(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: String,
    index: usize,
) -> Option<Symbol> {
    db.record_query(QueryKind::ExpectedSorts);
    let (owner, signature) = resolved_signature(db, catalog, file, relation).as_ref()?;
    let sort = signature.parameters.as_ref()?.get(index)?.as_ref()?;
    // A signature's names resolve in its declaring module, not its caller.
    resolve_sort(db, catalog, *owner, sort.clone()).clone()
}

#[salsa::tracked]
fn constant_candidates(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: String,
    index: usize,
) -> Vec<Symbol> {
    db.record_query(QueryKind::Constants);
    let Some(expected) = expected_argument_sort(db, catalog, file, relation, index) else {
        return vec![];
    };
    let mut result = vec![];
    for &owner in visible_files(db, catalog, file) {
        for constant in owner.constants(db) {
            let Some(sort) = &constant.sort else {
                continue;
            };
            if resolve_sort(db, catalog, owner, sort.clone()).as_ref() == Some(expected) {
                result.push(symbol(db, owner, &constant.id, &constant.name));
            }
        }
    }
    result
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct QueryCounts {
    relations: u32,
    sorts: u32,
    expected_sorts: u32,
    constants: u32,
    rules: u32,
    constant_diagnostics: u32,
    sort_labels: u32,
    modules: u32,
    declarations: u32,
    name_diagnostics: u32,
}

pub struct Analysis {
    db: Database,
    catalog: Catalog,
    files: HashMap<String, File>,
    rules: HashMap<String, HashMap<String, rules::RuleInput>>,
}

impl Default for Analysis {
    fn default() -> Self {
        let db = Database::default();
        let catalog = Catalog::new(&db, vec![]);
        Self {
            db,
            catalog,
            files: HashMap::new(),
            rules: HashMap::new(),
        }
    }
}

impl Analysis {
    // Updates arrive synchronously in caller order. Add revision validation
    // when the boundary introduces asynchronous work, not before.
    pub fn update(&mut self, mut doc: Document) {
        let uri = doc.uri.clone();
        let rules = std::mem::take(&mut doc.rules);
        if let Some(&file) = self.files.get(&doc.uri) {
            // Salsa setters mark changes; compare first so identical projections
            // do not invalidate semantic queries.
            if file.directory(&self.db) != &doc.directory {
                file.set_directory(&mut self.db).to(doc.directory);
            }
            if file.filename(&self.db) != &doc.filename {
                file.set_filename(&mut self.db).to(doc.filename);
            }
            if file.module(&self.db) != &doc.module {
                file.set_module(&mut self.db).to(doc.module);
            }
            if file.imports(&self.db) != &doc.imports {
                file.set_imports(&mut self.db).to(doc.imports);
            }
            if file.relations(&self.db) != &doc.relations {
                file.set_relations(&mut self.db).to(doc.relations);
            }
            if file.sorts(&self.db) != &doc.sorts {
                file.set_sorts(&mut self.db).to(doc.sorts);
            }
            if file.signatures(&self.db) != &doc.signatures {
                file.set_signatures(&mut self.db).to(doc.signatures);
            }
            if file.constants(&self.db) != &doc.constants {
                file.set_constants(&mut self.db).to(doc.constants);
            }
            if file.input_relations(&self.db) != &doc.input_relations {
                file.set_input_relations(&mut self.db)
                    .to(doc.input_relations);
            }
            if !file.present(&self.db) {
                file.set_present(&mut self.db).to(true);
            }
        } else {
            let file = File::new(
                &self.db,
                doc.uri.clone(),
                doc.directory,
                doc.filename,
                doc.module,
                doc.imports,
                doc.relations,
                doc.sorts,
                doc.signatures,
                doc.constants,
                doc.input_relations,
                true,
            );
            self.files.insert(doc.uri, file);
            let mut files = self.catalog.files(&self.db).clone();
            files.push(file);
            self.catalog.set_files(&mut self.db).to(files);
        }
        let current: std::collections::HashSet<_> = rules.iter().map(|rule| &rule.id).collect();
        let file_rules = self.rules.entry(uri).or_default();
        file_rules.retain(|id, _| current.contains(id));
        for rule in rules {
            if let Some(&input) = file_rules.get(&rule.id) {
                if input.syntax(&self.db) != &rule {
                    input.set_syntax(&mut self.db).to(rule);
                }
            } else {
                file_rules.insert(rule.id.clone(), rules::RuleInput::new(&self.db, rule));
            }
        }
    }

    pub fn remove(&mut self, uri: &str) {
        if let Some(file) = self.files.get(uri) {
            file.set_present(&mut self.db).to(false);
        }
        self.rules.remove(uri);
    }

    pub fn rule_analysis(&self, uri: &str, id: &str) -> RuleAnalysis {
        match (
            self.files.get(uri),
            self.rules.get(uri).and_then(|rules| rules.get(id)),
        ) {
            (Some(&file), Some(&rule)) => {
                rules::analyze_rule(&self.db, self.catalog, file, rule).clone()
            }
            _ => RuleAnalysis::default(),
        }
    }

    pub fn constant_diagnostic(
        &self,
        uri: &str,
        relation: String,
        index: usize,
        name: String,
    ) -> ConstantDiagnostic {
        self.files
            .get(uri)
            .map(|&file| {
                arguments::constant_diagnostic(&self.db, self.catalog, file, relation, index, name)
                    .clone()
            })
            .unwrap_or(ConstantDiagnostic::Suppressed)
    }

    pub fn sort_label(&self, uri: &str, owner_uri: &str, id: String) -> Option<String> {
        let &file = self.files.get(uri)?;
        let &owner = self.files.get(owner_uri)?;
        arguments::sort_label(&self.db, self.catalog, file, owner, id).clone()
    }

    pub fn visible_relations(&self, uri: &str) -> Vec<Symbol> {
        self.files
            .get(uri)
            .map(|file| visible_relations(&self.db, self.catalog, *file).clone())
            .unwrap_or_default()
    }

    pub fn module_candidates(&self, uri: &str) -> Vec<Symbol> {
        self.files
            .get(uri)
            .map(|&file| declarations::module_candidates(&self.db, self.catalog, file).clone())
            .unwrap_or_default()
    }

    pub fn declaration_diagnostics(&self, uri: &str) -> Vec<DeclarationDiagnostic> {
        self.files
            .get(uri)
            .map(|&file| {
                declarations::declaration_diagnostics(&self.db, self.catalog, file).clone()
            })
            .unwrap_or_default()
    }

    pub fn name_diagnostic(
        &self,
        uri: &str,
        kind: NameKind,
        name: String,
        relation: String,
        index: usize,
    ) -> Option<String> {
        self.files.get(uri).and_then(|&file| {
            declarations::name_diagnostic(&self.db, self.catalog, file, kind, name, relation, index)
                .clone()
        })
    }

    pub fn visible_sorts(&self, uri: &str) -> Vec<Symbol> {
        self.files
            .get(uri)
            .map(|file| visible_sorts(&self.db, self.catalog, *file).clone())
            .unwrap_or_default()
    }

    pub fn constant_candidates(
        &self,
        uri: &str,
        relation: String,
        index: usize,
        name: Option<&str>,
    ) -> Vec<Symbol> {
        self.files
            .get(uri)
            .map(|file| {
                // Filter borrowed cached results before cloning/serialization.
                // The tracked query stays keyed by file/relation/argument, not
                // by each reference spelling. Completion requests the full list.
                constant_candidates(&self.db, self.catalog, *file, relation, index)
                    .iter()
                    .filter(|symbol| name.is_none_or(|name| symbol.name == name))
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn query_counts(&self) -> QueryCounts {
        let [
            relations,
            sorts,
            expected_sorts,
            constants,
            rules,
            constant_diagnostics,
            sort_labels,
            modules,
            declarations,
            name_diagnostics,
        ] = self
            .db
            .executions
            .each_ref()
            .map(|n| n.load(Ordering::Relaxed));
        QueryCounts {
            relations,
            sorts,
            expected_sorts,
            constants,
            rules,
            constant_diagnostics,
            sort_labels,
            modules,
            declarations,
            name_diagnostics,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_lookup_and_diagnostics_track_create_rename_delete_and_ignore_signature_edits() {
        let mut core = Analysis::default();
        let caller = doc("caller", "caller", &["lib"], &[]);
        core.update(caller.clone());
        let error = |core: &Analysis| {
            core.name_diagnostic("caller", NameKind::Module, "lib".into(), "".into(), 0)
        };
        let found = |core: &Analysis| {
            core.module_candidates("caller")
                .iter()
                .any(|s| s.name == "lib")
        };
        assert!(!found(&core));
        assert_eq!(error(&core), None);
        let mut lib = typed_doc("lib", "lib", &[], &["Source"]);
        core.update(lib.clone());
        assert!(found(&core));
        assert_eq!(error(&core), None);
        assert_eq!(
            core.module_candidates("caller")
                .iter()
                .find(|s| s.name == "lib")
                .unwrap()
                .id,
            ""
        );
        let before = core.query_counts();
        lib.signatures[0].parameters = None;
        core.update(lib.clone());
        core.update(caller);
        assert_eq!(error(&core), None);
        assert_eq!(core.query_counts().modules, before.modules);
        assert_eq!(
            core.query_counts().name_diagnostics,
            before.name_diagnostics
        );
        lib.module = Some("renamed".into());
        core.update(lib.clone());
        assert!(!found(&core));
        assert_eq!(
            core.declaration_diagnostics("lib")[0].code,
            "module-filename"
        );
        lib.module = Some("lib".into());
        core.update(lib.clone());
        assert!(found(&core));
        assert_eq!(error(&core), None);
        core.remove("lib");
        assert!(!found(&core));
        assert!(core.declaration_diagnostics("lib").is_empty());
        core.update(lib.clone());
        assert!(found(&core));
        assert_eq!(error(&core), None);
        lib.directory = "elsewhere".into();
        core.update(lib);
        assert!(
            !found(&core),
            "same name outside the directory is not importable"
        );
    }

    #[test]
    fn missing_module_relation_and_sort_leave_generic_wording_to_the_frontend() {
        let mut core = Analysis::default();
        core.update(doc("caller", "caller", &[], &[]));
        for kind in [NameKind::Module, NameKind::Relation, NameKind::Sort] {
            assert_eq!(
                core.name_diagnostic("caller", kind, "missing".into(), "".into(), 0),
                None
            );
        }
    }

    #[test]
    fn duplicate_checks_use_namespaces_sort_identity_and_cache_reuse() {
        let mut core = Analysis::default();
        let mut file = typed_doc("lib", "lib", &[], &["Source", "Slot"]);
        file.constants = vec![
            constant("a", "same", "Source"),
            constant("b", "same", "Slot"),
            constant("c", "same", "Source"),
            constant("d", "same", "Missing"),
        ];
        file.relations.push(NamedDeclaration {
            id: "duplicate".into(),
            name: "r".into(),
        });
        core.update(file.clone());
        let diagnostics = core.declaration_diagnostics("lib");
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.id.as_str())
                .collect::<Vec<_>>(),
            ["duplicate", "c"]
        );
        let before = core.query_counts().declarations;
        file.signatures[0].parameters = None;
        core.update(file.clone());
        assert_eq!(core.declaration_diagnostics("lib"), diagnostics);
        assert_eq!(core.query_counts().declarations, before);
        file.sorts.push(NamedDeclaration {
            id: "duplicate-sort".into(),
            name: "Source".into(),
        });
        core.update(file);
        assert_eq!(
            core.declaration_diagnostics("lib")
                .iter()
                .map(|d| d.id.as_str())
                .collect::<Vec<_>>(),
            ["duplicate-sort", "duplicate"],
            "ambiguous sort must not invent constant duplicates"
        );
    }

    #[test]
    fn native_name_diagnostics_report_all_ambiguous_modules_and_clear_after_deletion() {
        let mut core = Analysis::default();
        core.update(typed_doc("left", "left", &[], &["Source"]));
        core.update(typed_doc("right", "right", &[], &["Source"]));
        core.update(doc("caller", "caller", &["right", "left", "left"], &[]));
        assert_eq!(
            core.name_diagnostic("caller", NameKind::Relation, "r".into(), "".into(), 0)
                .as_deref(),
            Some("Ambiguous name 'r': 2 visible declarations (left, right).")
        );
        assert_eq!(
            core.name_diagnostic("caller", NameKind::Sort, "Source".into(), "".into(), 0)
                .as_deref(),
            Some("Ambiguous name 'Source': 2 visible declarations (left, right).")
        );
        core.remove("right");
        assert_eq!(
            core.name_diagnostic("caller", NameKind::Relation, "r".into(), "".into(), 0),
            None
        );
    }

    fn error_message(diagnostic: ConstantDiagnostic) -> String {
        match diagnostic {
            ConstantDiagnostic::Error { message } => message,
            other => panic!("Expected error, got {other:?}"),
        }
    }

    #[test]
    fn constant_diagnostics_distinguish_resolution_errors_and_missing_context() {
        let mut core = Analysis::default();
        let mut lib = typed_doc("lib", "lib", &[], &["Source", "Slot"]);
        lib.constants = vec![
            constant("good", "good", "Source"),
            constant("wrong", "wrong", "Slot"),
            constant("unknown", "unknown", "Missing"),
        ];
        core.update(lib.clone());
        assert_eq!(
            core.constant_diagnostic("lib", "r".into(), 0, "good".into()),
            ConstantDiagnostic::Resolved
        );
        assert_eq!(
            error_message(core.constant_diagnostic("lib", "r".into(), 0, "wrong".into())),
            "No constant 'wrong' of sort Source (found: Slot)."
        );
        assert_eq!(
            error_message(core.constant_diagnostic("lib", "r".into(), 0, "absent".into())),
            "No constant 'absent' of sort Source (no visible declaration)."
        );
        assert_eq!(
            error_message(core.constant_diagnostic("lib", "r".into(), 0, "unknown".into())),
            "No constant 'unknown' of sort Source (found: unresolved sort)."
        );
        assert!(
            error_message(core.constant_diagnostic("lib", "r".into(), 1, "good".into()))
                .contains("Extra argument 'good'")
        );
        assert!(
            error_message(core.constant_diagnostic("lib", "r".into(), 1, "absent".into()))
                .contains("Unknown constant 'absent'")
        );
        lib.constants.push(constant("duplicate", "good", "Source"));
        core.update(lib.clone());
        assert_eq!(
            core.constant_diagnostic("lib", "r".into(), 0, "good".into()),
            ConstantDiagnostic::Ambiguous
        );
        lib.signatures[0].parameters = None;
        core.update(lib.clone());
        assert_eq!(
            core.constant_diagnostic("lib", "r".into(), 1, "absent".into()),
            ConstantDiagnostic::Suppressed
        );
        lib.signatures[0].parameters = Some(vec![Some("Missing".into())]);
        core.update(lib);
        assert_eq!(
            core.constant_diagnostic("lib", "r".into(), 0, "absent".into()),
            ConstantDiagnostic::Suppressed
        );
        assert!(
            matches!(
                core.constant_diagnostic("lib", "r".into(), 1, "absent".into()),
                ConstantDiagnostic::Error { .. }
            ),
            "out-of-range is not an unknown parameter sort"
        );
        assert_eq!(
            core.constant_diagnostic("lib", "missing_relation".into(), 0, "absent".into()),
            ConstantDiagnostic::Suppressed
        );
    }

    #[test]
    fn diagnostic_labels_use_sort_identity_and_reuse_queries_until_visibility_changes() {
        let mut core = Analysis::default();
        let left = typed_doc("left", "left", &[], &["Source"]);
        let mut right = typed_doc("right", "right", &[], &["Source"]);
        right.relations.clear();
        right.constants.push(constant("c", "c", "Source"));
        let mut caller = doc("caller", "caller", &["left", "right"], &[]);
        core.update(left);
        core.update(right);
        core.update(caller.clone());
        let error = core.constant_diagnostic("caller", "r".into(), 0, "c".into());
        assert_eq!(
            error_message(error.clone()),
            "No constant 'c' of sort left.Source (found: right.Source)."
        );
        assert_eq!(
            core.sort_label("caller", "left", "sort0".into()).as_deref(),
            Some("left.Source")
        );
        let before = core.query_counts();
        core.update(caller.clone());
        assert_eq!(
            core.constant_diagnostic("caller", "r".into(), 0, "c".into()),
            error
        );
        core.sort_label("caller", "left", "sort0".into());
        assert_eq!(
            core.query_counts().constant_diagnostics,
            before.constant_diagnostics
        );
        assert_eq!(core.query_counts().sort_labels, before.sort_labels);
        caller.imports.pop();
        core.update(caller);
        assert_eq!(
            error_message(core.constant_diagnostic("caller", "r".into(), 0, "c".into())),
            "No constant 'c' of sort Source (no visible declaration)."
        );
        assert_eq!(
            core.sort_label("caller", "left", "sort0".into()).as_deref(),
            Some("Source")
        );
        core.remove("left");
        assert_eq!(core.sort_label("caller", "left", "sort0".into()), None);
        assert_eq!(
            core.constant_diagnostic("caller", "r".into(), 0, "c".into()),
            ConstantDiagnostic::Suppressed
        );
    }

    #[test]
    fn arity_checks_require_an_unambiguous_reliable_signature() {
        let mut core = Analysis::default();
        let mut lib = typed_doc("lib", "lib", &[], &["Source"]);
        core.update(lib.clone());
        let check = |core: &Analysis, count| {
            arguments::arity_error(&core.db, core.catalog, core.files["lib"], "r", count)
        };
        assert!(check(&core, 1).is_none());
        assert_eq!(
            check(&core, 0).as_deref(),
            Some("Relation 'r' expects 1 argument, got 0.")
        );
        assert_eq!(
            check(&core, 2).as_deref(),
            Some("Relation 'r' expects 1 argument, got 2.")
        );
        lib.signatures[0].parameters = None;
        core.update(lib.clone());
        assert!(check(&core, 2).is_none());
        lib.signatures[0].parameters = Some(vec![Some("Missing".into()), None]);
        core.update(lib.clone());
        assert_eq!(
            check(&core, 1).as_deref(),
            Some("Relation 'r' expects 2 arguments, got 1.")
        );
        lib.relations.push(NamedDeclaration {
            id: "duplicate".into(),
            name: "r".into(),
        });
        core.update(lib);
        assert!(check(&core, 1).is_none());
    }

    fn typed_doc(uri: &str, module: &str, imports: &[&str], sort_names: &[&str]) -> Document {
        let mut document = doc(uri, module, imports, &["r"]);
        document.sorts = sort_names
            .iter()
            .enumerate()
            .map(|(i, name)| NamedDeclaration {
                id: format!("sort{i}"),
                name: (*name).into(),
            })
            .collect();
        document.signatures = vec![Signature {
            id: "0".into(),
            parameters: Some(vec![Some("Source".into())]),
        }];
        document
    }

    fn constant(id: &str, name: &str, sort: &str) -> Constant {
        Constant {
            id: id.into(),
            name: name.into(),
            sort: Some(sort.into()),
        }
    }
    fn doc(uri: &str, module: &str, imports: &[&str], names: &[&str]) -> Document {
        Document {
            uri: uri.into(),
            directory: "root".into(),
            filename: format!("{module}.den"),
            module: Some(module.into()),
            imports: imports.iter().map(|s| Some((*s).into())).collect(),
            sorts: vec![],
            signatures: vec![],
            constants: vec![],
            input_relations: vec![],
            rules: vec![],
            relations: names
                .iter()
                .enumerate()
                .map(|(i, s)| NamedDeclaration {
                    id: i.to_string(),
                    name: (*s).into(),
                })
                .collect(),
        }
    }
    #[test]
    fn persistent_cache_reuses_semantics_but_tracks_edits_ambiguity_and_deletion() {
        let mut core = Analysis::default();
        let mut a = doc("a", "a", &["lib", "lib"], &[]);
        let mut lib = doc("lib", "lib", &[], &["r"]);
        core.update(a.clone());
        core.update(lib.clone());
        assert_eq!(core.visible_relations("a")[0].name, "r");
        let executions = core.query_counts().relations;
        core.update(a.clone());
        assert_eq!(core.visible_relations("a").len(), 1);
        assert_eq!(core.query_counts().relations, executions);
        lib.relations[0].name = "s".into();
        core.update(lib.clone());
        let visible = core.visible_relations("a");
        assert_eq!(visible.len(), 1);
        assert_eq!(visible[0].name, "s");
        core.remove("lib");
        assert!(core.visible_relations("a").is_empty());
        core.update(lib);
        a.relations = doc("x", "x", &[], &["s"]).relations;
        core.update(a);
        let visible = core.visible_relations("a");
        assert_eq!(visible.len(), 2);
        assert!(visible.iter().all(|symbol| symbol.name == "s"));
    }
    #[test]
    fn imports_are_direct_and_mismatched_modules_are_invisible() {
        let mut core = Analysis::default();
        core.update(doc("a", "a", &["b"], &[]));
        core.update(doc("b", "b", &["c"], &[]));
        core.update(doc("c", "c", &[], &["r"]));
        assert!(core.visible_relations("a").is_empty());
        assert_eq!(core.visible_relations("b").len(), 1);
        let mut c = doc("c", "renamed", &[], &["r"]);
        c.filename = "c.den".into();
        core.update(c);
        assert!(core.visible_relations("b").is_empty());
    }

    #[test]
    fn unrelated_relation_edit_does_not_reexecute_importer_query() {
        let mut core = Analysis::default();
        core.update(doc("a", "a", &["lib"], &[]));
        core.update(doc("lib", "lib", &[], &["r"]));
        let mut other = doc("other", "other", &[], &["r"]);
        core.update(other.clone());
        assert_eq!(core.visible_relations("a").len(), 1);
        let count = core.query_counts().relations;
        other.relations[0].name = "changed".into();
        core.update(other);
        assert_eq!(core.visible_relations("a").len(), 1);
        assert_eq!(core.query_counts().relations, count);
    }

    #[test]
    fn typed_candidates_follow_signatures_without_invalidating_visibility() {
        let mut core = Analysis::default();
        let mut lib = typed_doc("lib", "lib", &[], &["Source", "Slot"]);
        let mut caller = doc("caller", "caller", &["lib"], &[]);
        caller.constants = vec![
            constant("source", "shared", "Source"),
            constant("slot", "shared", "Slot"),
        ];
        core.update(lib.clone());
        core.update(caller.clone());
        assert_eq!(
            core.constant_candidates("caller", "r".into(), 0, None)[0].id,
            "source"
        );
        let before = core.query_counts();
        core.update(caller);
        assert_eq!(
            core.constant_candidates("caller", "r".into(), 0, None)[0].id,
            "source"
        );
        assert_eq!(core.query_counts().constants, before.constants);
        lib.signatures[0].parameters = Some(vec![Some("Slot".into())]);
        core.update(lib.clone());
        assert_eq!(
            core.constant_candidates("caller", "r".into(), 0, None)[0].id,
            "slot"
        );
        assert_eq!(core.query_counts().relations, before.relations);
        assert_eq!(core.query_counts().sorts, before.sorts);
        assert!(core.query_counts().constants > before.constants);
        assert!(
            core.constant_candidates("caller", "r".into(), 1, None)
                .is_empty()
        );
        lib.signatures[0].parameters = None;
        core.update(lib.clone());
        assert!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .is_empty()
        );
        lib.signatures[0].parameters = Some(vec![Some("Unknown".into())]);
        core.update(lib);
        assert!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .is_empty()
        );
    }

    #[test]
    fn signatures_and_constants_resolve_in_their_own_modules_by_sort_identity() {
        let mut core = Analysis::default();
        let mut lib = typed_doc("lib", "lib", &[], &["Source"]);
        lib.constants = vec![constant("library", "shared", "Source")];
        let mut caller = doc("caller", "caller", &["lib"], &[]);
        caller.sorts = vec![NamedDeclaration {
            id: "local".into(),
            name: "Source".into(),
        }];
        caller.constants = vec![constant("ambiguous", "shared", "Source")];
        core.update(lib.clone());
        core.update(caller);
        let candidates = core.constant_candidates("caller", "r".into(), 0, None);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].uri, "lib");
        assert_eq!(candidates[0].id, "library");
        // Adding a same-named sort in the signature's own visibility makes it
        // ambiguous too; a formerly valid target must disappear.
        core.update(typed_doc("other", "other", &[], &["Source"]));
        lib.imports = vec![Some("other".into())];
        core.update(lib);
        assert!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .is_empty()
        );
    }

    #[test]
    fn relation_ambiguity_and_deletion_leave_no_typed_candidates() {
        let mut core = Analysis::default();
        core.update(typed_doc("left", "left", &[], &["Source"]));
        core.update(typed_doc("right", "right", &[], &["Source"]));
        let mut caller = doc("caller", "caller", &["left", "right"], &[]);
        caller.constants = vec![constant("c", "c", "Source")];
        core.update(caller);
        assert!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .is_empty()
        );
        core.remove("right");
        assert_eq!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .len(),
            1
        );
        core.remove("left");
        assert!(
            core.constant_candidates("caller", "r".into(), 0, None)
                .is_empty()
        );
    }

    #[test]
    fn name_filter_reuses_the_typed_query_and_preserves_ambiguity() {
        let mut core = Analysis::default();
        let mut lib = typed_doc("lib", "lib", &[], &["Source"]);
        lib.constants = (0..1000)
            .map(|i| constant(&format!("id{i}"), &format!("c{i}"), "Source"))
            .collect();
        lib.constants.push(constant("duplicate", "c999", "Source"));
        core.update(lib);
        assert_eq!(
            core.constant_candidates("lib", "r".into(), 0, None).len(),
            1001
        );
        let before = core.query_counts().constants;
        assert_eq!(
            core.constant_candidates("lib", "r".into(), 0, Some("c0"))
                .len(),
            1
        );
        assert_eq!(
            core.constant_candidates("lib", "r".into(), 0, Some("c999"))
                .len(),
            2
        );
        assert!(
            core.constant_candidates("lib", "r".into(), 0, Some("missing"))
                .is_empty()
        );
        assert!(
            core.constant_candidates("lib", "r".into(), 0, Some(""))
                .is_empty()
        );
        assert_eq!(
            core.query_counts().constants,
            before,
            "names must not become tracked-query keys"
        );
    }
}
