use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "lowercase")]
pub enum ConstantDiagnostic {
    Resolved,
    Ambiguous,
    Suppressed,
    Error { message: String },
}

pub(super) fn arity_error(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: &str,
    actual: usize,
) -> Option<String> {
    let (_, signature) = resolved_signature(db, catalog, file, relation.into()).as_ref()?;
    let count = signature.parameters.as_ref()?.len();
    (actual != count).then(|| {
        format!(
            "Relation '{relation}' expects {count} argument{}, got {actual}.",
            if count == 1 { "" } else { "s" }
        )
    })
}

fn label(sort: &Symbol, qualified: bool) -> String {
    if qualified {
        format!("{}.{}", sort.module.as_deref().unwrap_or("?"), sort.name)
    } else {
        sort.name.clone()
    }
}

#[salsa::tracked]
pub(super) fn sort_label(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    owner: File,
    id: String,
) -> Option<String> {
    db.record_query(QueryKind::SortLabels);
    if !file.present(db) || !owner.present(db) {
        return None;
    }
    let declaration = owner.sorts(db).iter().find(|sort| sort.id == id)?;
    let target = symbol(db, owner, &id, &declaration.name);
    let ambiguous = visible_sorts(db, catalog, file)
        .iter()
        .any(|other| other.name == target.name && other != &target);
    Some(label(&target, ambiguous))
}

#[salsa::tracked]
pub(super) fn constant_diagnostic(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    relation: String,
    index: usize,
    name: String,
) -> ConstantDiagnostic {
    db.record_query(QueryKind::ConstantDiagnostics);
    let Some((_, signature)) = resolved_signature(db, catalog, file, relation.clone()) else {
        return ConstantDiagnostic::Suppressed;
    };
    let Some(parameters) = &signature.parameters else {
        return ConstantDiagnostic::Suppressed;
    };
    if index >= parameters.len() {
        let declared = visible_files(db, catalog, file).iter().any(|owner| {
            owner
                .constants(db)
                .iter()
                .any(|constant| constant.name == name)
        });
        return ConstantDiagnostic::Error {
            message: if declared {
                format!(
                    "Extra argument '{name}' to relation '{relation}': no parameter {} supplies an expected sort for constant lookup.",
                    index + 1
                )
            } else {
                format!(
                    "Unknown constant '{name}' (no visible declaration); argument {} is beyond relation '{relation}'s signature.",
                    index + 1
                )
            },
        };
    }
    // Missing type context must not scan a large constant domain for every
    // unresolved use while a declaration is being edited.
    let Some(expected) = expected_argument_sort(db, catalog, file, relation.clone(), index) else {
        return ConstantDiagnostic::Suppressed;
    };
    match constant_candidates(db, catalog, file, relation.clone(), index)
        .iter()
        .filter(|symbol| symbol.name == name)
        .take(2)
        .count()
    {
        1 => return ConstantDiagnostic::Resolved,
        2 => return ConstantDiagnostic::Ambiguous,
        _ => {}
    }
    let declarations: Vec<_> = visible_files(db, catalog, file)
        .iter()
        .flat_map(|&owner| {
            owner
                .constants(db)
                .iter()
                .filter(|constant| constant.name == name)
                .map(move |constant| (owner, constant))
        })
        .collect();
    let sorts: Vec<_> = declarations
        .iter()
        .map(|(owner, constant)| {
            constant
                .sort
                .as_ref()
                .and_then(|name| resolve_sort(db, catalog, *owner, name.clone()).clone())
        })
        .collect();
    let qualify = sorts
        .iter()
        .flatten()
        .any(|sort| sort != expected && sort.name == expected.name);
    let mut found: Vec<_> = sorts
        .iter()
        .map(|sort| {
            sort.as_ref()
                .map(|sort| label(sort, qualify))
                .unwrap_or("unresolved sort".into())
        })
        .collect();
    found.sort();
    found.dedup();
    ConstantDiagnostic::Error {
        message: format!(
            "No constant '{name}' of sort {} ({}).",
            label(expected, qualify),
            if found.is_empty() {
                "no visible declaration".into()
            } else {
                format!("found: {}", found.join(", "))
            }
        ),
    }
}
