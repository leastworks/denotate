//! Editor-owned root catalog. Disk membership and open snapshots have one identity;
//! failures retain graph edges and block only their transitive consumers.
use denotate_ir_text::{filesystem::manifest_libraries, ProgramMembership, RootInfo};
use lsp_types::Url;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
};

pub fn identity(path: &Path) -> PathBuf {
    if let Ok(path) = path.canonicalize() {
        return path;
    }
    // Resolve existing prefixes before `..`: lexical normalization first would
    // change the meaning of a path containing a symlink followed by `..`.
    match (path.parent(), path.components().next_back()) {
        (Some(parent), Some(Component::Normal(name))) => identity(parent).join(name),
        (Some(parent), Some(Component::ParentDir)) => {
            let mut result = identity(parent);
            result.pop();
            result
        }
        (Some(parent), Some(Component::CurDir)) => identity(parent),
        _ => path.to_owned(),
    }
}
pub fn uri(path: &Path) -> String {
    Url::from_file_path(identity(path)).unwrap().to_string()
}
#[derive(Clone)]
pub struct Manifest {
    pub text: String,
    pub version: i64,
}
#[derive(Clone, Default)]
pub struct Node {
    pub info: RootInfo,
    pub errors: Vec<String>,
    pub snapshot: Option<Manifest>,
}
#[derive(Default)]
pub struct Catalog {
    pub open: BTreeMap<PathBuf, Manifest>,
    pub nodes: BTreeMap<String, Node>,
    pub programs: BTreeMap<String, ProgramMembership>,
    pub errors: BTreeMap<String, Vec<String>>,
    // Syntax blocks checked-corpus construction, but reliable partial index
    // evidence remains available for completion/navigation during ordinary edits.
    pub syntax_errors: BTreeMap<String, Vec<String>>,
    pub resolution_errors: BTreeMap<String, Vec<String>>,
    pub files: BTreeSet<PathBuf>,
    pub discovery_errors: BTreeMap<PathBuf, String>,
}
impl Catalog {
    fn marker(&self, folder: &Path) -> bool {
        let p = folder.join("den.root");
        p.try_exists().unwrap_or(true) || self.open.contains_key(&identity(&p))
    }
    fn scan(
        &mut self,
        folder: &Path,
        roots: &mut BTreeSet<PathBuf>,
        members: &mut BTreeSet<String>,
        stop_nested: bool,
    ) {
        let entries = match fs::read_dir(folder) {
            Ok(e) => e,
            Err(e) => {
                self.discovery_errors
                    .insert(identity(folder), e.to_string());
                return;
            }
        };
        for entry in entries {
            let entry = match entry {
                Ok(e) => e,
                Err(e) => {
                    self.discovery_errors
                        .insert(identity(folder), e.to_string());
                    continue;
                }
            };
            let path = entry.path();
            match entry.file_type() {
                Ok(kind) if kind.is_dir() => {
                    let marker = self.marker(&path);
                    if marker {
                        roots.insert(identity(&path.join("den.root")));
                    }
                    if !stop_nested || !marker {
                        self.scan(&path, roots, members, stop_nested);
                    }
                }
                Ok(_) if path.extension().is_some_and(|s| s == "den") && !path.is_dir() => {
                    self.files.insert(identity(&path));
                    members.insert(uri(&path));
                }
                Err(e) => {
                    self.discovery_errors.insert(identity(&path), e.to_string());
                }
                _ => {}
            }
        }
    }
    pub fn refresh(&mut self, workspaces: &[PathBuf], documents: impl Iterator<Item = PathBuf>) {
        let previous = std::mem::take(&mut self.nodes);
        self.programs.clear();
        self.errors.clear();
        self.syntax_errors.clear();
        self.resolution_errors.clear();
        self.files.clear();
        self.discovery_errors.clear();
        let mut pending = BTreeSet::new();
        for folder in workspaces {
            if self.marker(folder) {
                pending.insert(identity(&folder.join("den.root")));
            }
            self.scan(folder, &mut pending, &mut BTreeSet::new(), false);
        }
        let documents: Vec<_> = documents.map(|p| identity(&p)).collect();
        for path in documents.iter().chain(self.open.keys()) {
            for parent in path.ancestors().skip(1) {
                if self.marker(parent) {
                    pending.insert(identity(&parent.join("den.root")));
                    break;
                }
            }
        }
        while let Some(path) = pending.pop_first() {
            let key = uri(&path);
            if self.nodes.contains_key(&key) {
                continue;
            }
            let mut node = Node::default();
            let snapshot = self.open.get(&path).cloned().map(Ok).unwrap_or_else(|| {
                fs::read_to_string(&path).map(|text| Manifest { text, version: 0 })
            });
            match snapshot {
                Ok(snapshot) => {
                    match manifest_libraries(&snapshot.text) {
                        Ok(paths) => {
                            for relative in paths {
                                let target = identity(&path.parent().unwrap().join(relative));
                                node.info.libraries.insert(uri(&target));
                                pending.insert(target);
                            }
                        }
                        Err(e) => {
                            node.errors.push(format!("{key}: {e}"));
                        }
                    }
                    node.snapshot = Some(snapshot);
                }
                Err(e) => node.errors.push(format!("{key}: {e}")),
            }
            // Missing/unreadable manifests preserve the same recovery graph as
            // incomplete JSON. Their retained links never make the root valid.
            if !node.errors.is_empty() {
                if let Some(old) = previous.get(&key) {
                    node.info.libraries = old.info.libraries.clone();
                    pending.extend(
                        old.info
                            .libraries
                            .iter()
                            .filter_map(|s| Url::parse(s).ok()?.to_file_path().ok()),
                    );
                }
            }
            let folder = path.parent().unwrap();
            self.scan(folder, &mut pending, &mut node.info.files, true);
            // New, unsaved .den files belong to the same explicit folder root.
            for document in &documents {
                if document.starts_with(folder)
                    && document
                        .ancestors()
                        .skip(1)
                        .take_while(|p| *p != folder)
                        .all(|p| !self.marker(p))
                {
                    node.info.files.insert(uri(document));
                }
            }
            for (failed, error) in &self.discovery_errors {
                if failed == folder
                    || (failed.starts_with(folder)
                        && !self.marker(failed)
                        && failed
                            .ancestors()
                            .skip(1)
                            .take_while(|p| *p != folder)
                            .all(|p| !self.marker(p)))
                {
                    node.errors.push(format!("{}: {error}", failed.display()));
                }
            }
            self.nodes.insert(key, node);
        }
        for root in self.nodes.keys() {
            let mut roots = BTreeMap::new();
            let mut errors = vec![];
            let mut pending = vec![root.clone()];
            while let Some(key) = pending.pop() {
                if roots.contains_key(&key) {
                    continue;
                }
                let node = &self.nodes[&key];
                pending.extend(node.info.libraries.iter().cloned());
                errors.extend(node.errors.iter().cloned());
                roots.insert(key, node.info.clone());
            }
            self.programs.insert(
                root.clone(),
                ProgramMembership {
                    root: root.clone(),
                    roots,
                },
            );
            self.errors.insert(root.clone(), errors);
        }
    }
    fn containing(&self, document: &str) -> Vec<String> {
        self.programs
            .iter()
            .filter(|(_, p)| p.roots.values().any(|r| r.files.contains(document)))
            .map(|(r, _)| r.clone())
            .collect()
    }
    pub fn home(&self, document: &str) -> Option<String> {
        // User ownership is direct membership, independent of every consumer.
        let mut owners = self.programs.iter().filter(|(root, program)| {
            program
                .roots
                .get(*root)
                .is_some_and(|r| r.files.contains(document))
        });
        let (owner, _) = owners.next()?;
        owners.next().is_none().then(|| owner.clone())
    }
    pub fn context(&self, document: &str) -> Option<String> {
        self.home(document).filter(|r| self.errors[r].is_empty())
    }
    pub fn program_status(&self, root: &str) -> Value {
        let errors = self.errors[root]
            .iter()
            .chain(self.syntax_errors.get(root).into_iter().flatten())
            .chain(self.resolution_errors.get(root).into_iter().flatten())
            .collect::<Vec<_>>();
        json!({"program":root, "state":if errors.is_empty() {"ready"} else {"invalid"},
            "errors":errors})
    }
    pub fn status(&self, document: &str) -> Value {
        let home = self.home(document);
        let mut status = if let Some(root) = &home {
            self.program_status(root)
        } else {
            let path = Url::parse(document)
                .ok()
                .and_then(|u| u.to_file_path().ok());
            let mut errors = self
                .discovery_errors
                .iter()
                .filter(|(p, _)| path.as_ref().is_some_and(|d| d.starts_with(p)))
                .map(|(p, e)| format!("{}: {e}", p.display()))
                .collect::<Vec<_>>();
            if !self.containing(document).is_empty() {
                errors.push("Membership does not establish a unique home program".into());
            }
            json!({"state":if errors.is_empty() {"standalone"} else {"invalid"},
                "errors":errors})
        };
        status.as_object_mut().unwrap().remove("program");
        status["uri"] = json!(document);
        status["homeProgram"] = json!(home);
        status
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn home_requires_unique_ownership_and_never_changes_to_a_consumer() {
        let document = "file:///shared.den";
        let library = ProgramMembership::single("library", [document.into()]);
        let mut consumer = library.clone();
        consumer.root = "consumer".into();
        consumer.roots.insert(
            "consumer".into(),
            RootInfo {
                files: BTreeSet::new(),
                libraries: BTreeSet::from(["library".into()]),
            },
        );
        let mut catalog = Catalog::default();
        catalog.programs.insert("consumer".into(), consumer);
        catalog.errors.insert("consumer".into(), vec![]);
        assert_eq!(catalog.status(document)["state"], "invalid");
        catalog.programs.insert("library".into(), library);
        catalog.errors.insert("library".into(), vec![]);
        assert_eq!(catalog.context(document).as_deref(), Some("library"));
        catalog
            .errors
            .insert("library".into(), vec!["unavailable".into()]);
        assert_eq!(catalog.status(document)["state"], "invalid");
        assert_eq!(catalog.home(document).as_deref(), Some("library"));
        assert_eq!(catalog.context(document), None);
        catalog.programs.insert(
            "second-owner".into(),
            ProgramMembership::single("second-owner", [document.into()]),
        );
        catalog.errors.insert("second-owner".into(), vec![]);
        assert_eq!(catalog.status(document)["state"], "invalid");
    }

    #[test]
    fn disk_catalog_matches_cli_membership_and_open_manifests_define_boundaries() {
        let folder = std::env::temp_dir().join(format!("denotate-catalog-{}", std::process::id()));
        fs::create_dir_all(folder.join("nested")).unwrap();
        fs::create_dir_all(folder.join("lib")).unwrap();
        for (file, text) in [
            ("den.root", r#"{"libraries":["lib/den.root"]}"#),
            ("a.den", "relation a();"),
            ("lib/den.root", r#"{"libraries":["../den.root"]}"#),
            ("lib/b.den", "relation b();"),
            ("nested/c.den", "relation c();"),
        ] {
            fs::write(folder.join(file), text).unwrap();
        }
        let mut catalog = Catalog::default();
        catalog.refresh(&[folder.clone()], std::iter::empty());
        let (disk, _) = denotate_ir_text::filesystem::discover(&folder).unwrap();
        assert_eq!(catalog.programs[&disk.root], disk);
        assert!(catalog.errors[&disk.root].is_empty());
        let library = uri(&folder.join("lib/den.root"));
        fs::remove_file(folder.join("lib/den.root")).unwrap();
        catalog.refresh(&[folder.clone()], std::iter::empty());
        assert!(catalog.nodes[&library].info.libraries.contains(&disk.root));
        assert!(!catalog.errors[&disk.root].is_empty());
        fs::write(
            folder.join("lib/den.root"),
            r#"{"libraries":["../den.root"]}"#,
        )
        .unwrap();
        catalog.refresh(&[folder.clone()], std::iter::empty());
        assert_eq!(catalog.programs[&disk.root], disk);
        assert!(catalog.errors[&disk.root].is_empty());
        let marker = identity(&folder.join("nested/den.root"));
        catalog.open.insert(
            marker.clone(),
            Manifest {
                text: "{}".into(),
                version: 1,
            },
        );
        catalog.refresh(&[folder.clone()], std::iter::empty());
        assert!(!catalog.programs[&disk.root]
            .members()
            .unwrap()
            .contains_key(&uri(&folder.join("nested/c.den"))));
        assert_eq!(
            catalog.home(&uri(&folder.join("nested/c.den"))),
            Some(uri(&marker))
        );
        fs::write(&marker, "{}").unwrap();
        let (disk, _) = denotate_ir_text::filesystem::discover(&folder).unwrap();
        assert_eq!(catalog.programs[&disk.root], disk);
        #[cfg(unix)]
        {
            fs::create_dir_all(folder.join("alpha/beta")).unwrap();
            fs::write(folder.join("alpha/den.root"), "{}").unwrap();
            std::os::unix::fs::symlink(folder.join("alpha/beta"), folder.join("alias")).unwrap();
            assert_eq!(
                identity(&folder.join("alias/../missing/den.root")),
                folder
                    .canonicalize()
                    .unwrap()
                    .join("alpha/missing/den.root")
            );
        }
        fs::remove_dir_all(folder).unwrap();
    }
}
