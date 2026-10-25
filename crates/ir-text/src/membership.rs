use crate::{Diagnostic, Result};
use std::collections::{BTreeMap, BTreeSet};

/// Resolved membership and dependency edges, supplied by the caller. Identities
/// are canonical URIs; an editor can supply authoritative buffer snapshots.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RootInfo {
    pub files: BTreeSet<String>,
    pub libraries: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramMembership {
    pub root: String,
    pub roots: BTreeMap<String, RootInfo>,
}
impl ProgramMembership {
    pub fn single(root: impl Into<String>, files: impl IntoIterator<Item = String>) -> Self {
        let root = root.into();
        Self {
            root: root.clone(),
            roots: BTreeMap::from([(
                root,
                RootInfo {
                    files: files.into_iter().collect(),
                    libraries: BTreeSet::new(),
                },
            )]),
        }
    }

    /// URI -> user/library classification. Membership is a set, including when
    /// roots form diamonds or cycles. The selected root's own files take priority.
    pub fn members(&self) -> Result<BTreeMap<String, String>> {
        let mut pending = vec![self.root.clone()];
        let mut visited = BTreeSet::new();
        let mut files = BTreeMap::new();
        while let Some(root) = pending.pop() {
            if !visited.insert(root.clone()) {
                continue;
            }
            let info = self.roots.get(&root).ok_or_else(|| {
                vec![Diagnostic {
                    uri: root.clone(),
                    range: 0..0,
                    message: "Missing root membership descriptor".into(),
                }]
            })?;
            pending.extend(info.libraries.iter().cloned());
            for file in &info.files {
                let ownership = if self.roots[&self.root].files.contains(file) {
                    "user"
                } else {
                    "library"
                };
                files.insert(file.clone(), ownership.to_owned());
            }
        }
        Ok(files)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActiveRoot {
    Selected(String),
    NeedsSelection(Vec<String>),
}

/// Present choices from explicit root membership without parsing source text or
/// silently selecting one of several containing programs.
pub fn roots(programs: &[ProgramMembership]) -> Result<BTreeMap<String, ActiveRoot>> {
    let mut containing = BTreeMap::<String, BTreeSet<String>>::new();
    for program in programs {
        for file in program.members()?.into_keys() {
            containing
                .entry(file)
                .or_default()
                .insert(program.root.clone());
        }
    }
    Ok(containing
        .into_iter()
        .map(|(file, roots)| {
            let mut roots = roots.into_iter().collect::<Vec<_>>();
            let choice = if roots.len() == 1 {
                ActiveRoot::Selected(roots.remove(0))
            } else {
                ActiveRoot::NeedsSelection(roots)
            };
            (file, choice)
        })
        .collect())
}
