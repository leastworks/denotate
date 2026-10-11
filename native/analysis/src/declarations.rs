use super::*;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DeclarationDiagnostic {
    pub id: String,
    pub code: String,
    pub message: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum NameKind {
    Module,
    Relation,
    Sort,
    Constant,
}

#[salsa::tracked]
pub(super) fn importable_files(db: &dyn Db, catalog: Catalog, file: File) -> Vec<File> {
    db.record_query(QueryKind::Modules);
    if !file.present(db) {
        return vec![];
    }
    catalog
        .files(db)
        .iter()
        .copied()
        .filter(|candidate| {
            *candidate.present(db)
                && candidate.directory(db) == file.directory(db)
                && candidate
                    .module(db)
                    .as_ref()
                    .is_some_and(|name| candidate.filename(db) == &format!("{name}.den"))
        })
        .collect()
}

#[salsa::tracked]
pub(super) fn module_candidates(db: &dyn Db, catalog: Catalog, file: File) -> Vec<Symbol> {
    importable_files(db, catalog, file)
        .iter()
        .filter_map(|&owner| {
            owner
                .module(db)
                .as_ref()
                .map(|name| symbol(db, owner, "", name))
        })
        .collect()
}

#[salsa::tracked]
pub(super) fn declaration_diagnostics(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
) -> Vec<DeclarationDiagnostic> {
    db.record_query(QueryKind::Declarations);
    if !file.present(db) {
        return vec![];
    }
    let mut result = vec![];
    if let Some(name) = file.module(db) {
        if file.filename(db) != &format!("{name}.den") {
            result.push(DeclarationDiagnostic {
                id: "".into(),
                code: "module-filename".into(),
                message: format!(
                    "Module '{name}' must match filename '{}'.",
                    file.filename(db)
                ),
            });
        }
    }
    // Sorts and relations have separate namespaces. Constants are keyed by
    // resolved sort identity, not its spelling; unknown sorts add no guess.
    for declarations in [file.sorts(db), file.relations(db)] {
        let mut seen = HashSet::new();
        for declaration in declarations {
            if !seen.insert(&declaration.name) {
                result.push(duplicate(&declaration.id, &declaration.name));
            }
        }
    }
    let mut seen = HashSet::new();
    for constant in file.constants(db) {
        let Some(sort) = constant
            .sort
            .as_ref()
            .and_then(|name| resolve_sort(db, catalog, file, name.clone()).as_ref())
        else {
            continue;
        };
        if !seen.insert((&sort.uri, &sort.id, &constant.name)) {
            result.push(duplicate(&constant.id, &constant.name));
        }
    }
    result
}

fn duplicate(id: &str, name: &str) -> DeclarationDiagnostic {
    DeclarationDiagnostic {
        id: id.into(),
        code: "duplicate-declaration".into(),
        message: format!("Duplicate declaration '{name}'."),
    }
}

// Queried only for failed/ambiguous links. Successful linking does not pay for
// another boundary call or a per-spelling query entry.
#[salsa::tracked]
pub(super) fn name_diagnostic(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    kind: NameKind,
    name: String,
    relation: String,
    index: usize,
) -> Option<String> {
    db.record_query(QueryKind::NameDiagnostics);
    let candidates = match kind {
        NameKind::Module => module_candidates(db, catalog, file),
        NameKind::Relation => visible_relations(db, catalog, file),
        NameKind::Sort => visible_sorts(db, catalog, file),
        NameKind::Constant => constant_candidates(db, catalog, file, relation.clone(), index),
    };
    let matching: Vec<_> = candidates
        .iter()
        .filter(|target| target.name == name)
        .collect();
    if matching.len() > 1 {
        let mut modules: Vec<_> = matching
            .iter()
            .map(|target| target.module.as_deref().unwrap_or("<unnamed>"))
            .collect();
        modules.sort();
        return Some(format!(
            "Ambiguous name '{name}': {} visible declarations ({}).",
            matching.len(),
            modules.join(", ")
        ));
    }
    if !matching.is_empty() {
        return None;
    }
    if kind == NameKind::Constant {
        return match arguments::constant_diagnostic(db, catalog, file, relation, index, name) {
            ConstantDiagnostic::Error { message } => Some(message.clone()),
            _ => None,
        };
    }
    // Empty candidates already express failed resolution. The frontend supplies
    // generic not-found wording without leaking its AST type names into the core.
    None
}
