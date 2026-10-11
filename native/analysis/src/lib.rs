use salsa::Setter;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    },
};

/// Partial syntax projection: identity and semantic fields only, never spans.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Relation {
    pub id: String,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Document {
    pub uri: String,
    pub directory: String,
    pub filename: String,
    pub module: Option<String>,
    pub imports: Vec<Option<String>>,
    pub relations: Vec<Relation>,
}

#[salsa::input]
struct File {
    uri: String,
    directory: String,
    filename: String,
    module: Option<String>,
    imports: Vec<Option<String>>,
    relations: Vec<Relation>,
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
    fn record_resolution(&self);
}

#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    executions: Arc<AtomicU32>,
}

#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn record_resolution(&self) {
        self.executions.fetch_add(1, Ordering::Relaxed);
    }
}

#[salsa::tracked]
fn visible_relations(db: &dyn Db, catalog: Catalog, file: File) -> Vec<Symbol> {
    db.record_resolution();
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
    let mut result = vec![];
    for owner in visible {
        for relation in owner.relations(db) {
            result.push(Symbol {
                uri: owner.uri(db).clone(),
                id: relation.id.clone(),
                module: owner.module(db).clone(),
                name: relation.name.clone(),
            });
        }
    }
    result.sort_by(|a, b| (&a.uri, &a.id).cmp(&(&b.uri, &b.id)));
    result
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
            // updates do not invalidate semantic queries.
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

    pub fn executions(&self) -> u32 {
        self.db.executions.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn doc(uri: &str, module: &str, imports: &[&str], names: &[&str]) -> Document {
        Document {
            uri: uri.into(),
            directory: "root".into(),
            filename: format!("{module}.den"),
            module: Some(module.into()),
            imports: imports.iter().map(|s| Some((*s).into())).collect(),
            relations: names
                .iter()
                .enumerate()
                .map(|(i, s)| Relation {
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
        let executions = core.executions();
        core.update(a.clone());
        assert_eq!(core.visible_relations("a").len(), 1);
        assert_eq!(core.executions(), executions);
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
        let count = core.executions();
        other.relations[0].name = "changed".into();
        core.update(other);
        assert_eq!(core.visible_relations("a").len(), 1);
        assert_eq!(core.executions(), count);
    }
}
