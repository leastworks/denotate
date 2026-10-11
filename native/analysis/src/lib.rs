use salsa::Setter;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

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
}

#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    executions: Arc<[AtomicU32; 4]>,
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
    let directory = file.directory(db);
    let mut visible = vec![file];
    for &candidate in catalog.files(db) {
        if candidate == file || !candidate.present(db) || candidate.directory(db) != directory {
            continue;
        }
        let Some(module) = candidate.module(db) else {
            continue;
        };
        if candidate.filename(db) == &format!("{module}.den")
            && imports.iter().any(|item| item.as_ref() == Some(module))
        {
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
fn expected_argument_sort(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: String,
    index: usize,
) -> Option<Symbol> {
    db.record_query(QueryKind::ExpectedSorts);
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
    let sort = signature.parameters.as_ref()?.get(index)?.as_ref()?;
    // A signature's names resolve in its declaring module, not its caller.
    resolve_sort(db, catalog, owner, sort.clone()).clone()
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
}

pub struct Analysis {
    db: Database,
    catalog: Catalog,
    files: HashMap<String, File>,
}

impl Default for Analysis {
    fn default() -> Self {
        let db = Database::default();
        let catalog = Catalog::new(&db, vec![]);
        Self {
            db,
            catalog,
            files: HashMap::new(),
        }
    }
}

impl Analysis {
    // Updates arrive synchronously in caller order. Add revision validation
    // when the boundary introduces asynchronous work, not before.
    pub fn update(&mut self, doc: Document) {
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
                true,
            );
            self.files.insert(doc.uri, file);
            let mut files = self.catalog.files(&self.db).clone();
            files.push(file);
            self.catalog.set_files(&mut self.db).to(files);
        }
    }

    pub fn remove(&mut self, uri: &str) {
        if let Some(file) = self.files.get(uri) {
            file.set_present(&mut self.db).to(false);
        }
    }

    pub fn visible_relations(&self, uri: &str) -> Vec<Symbol> {
        self.files
            .get(uri)
            .map(|file| visible_relations(&self.db, self.catalog, *file).clone())
            .unwrap_or_default()
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
        let [relations, sorts, expected_sorts, constants] = self
            .db
            .executions
            .each_ref()
            .map(|n| n.load(Ordering::Relaxed));
        QueryCounts {
            relations,
            sorts,
            expected_sorts,
            constants,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
