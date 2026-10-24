//! Conservative refactoring over resolved identities, never text substitution.
use crate::{
    projection::{reserved, Lookup},
    semantic::{Semantics, Target},
    syntax::Document,
};
use lsp_types::{Position, Range, Url};
use serde_json::{json, Value};
use std::{
    collections::{BTreeSet, HashMap},
    path::{Path, PathBuf},
};

fn protected(path: &Path) -> bool {
    path.components().any(|part| {
        matches!(
            part.as_os_str().to_str(),
            Some("generated" | "node_modules" | "dist" | ".git")
        )
    })
}

fn editable(uri: &Url, roots: &[PathBuf]) -> Result<(), String> {
    let visible = uri
        .to_file_path()
        .map_err(|_| "Rename requires editable workspace files.")?;
    let path = visible
        .canonicalize()
        .map_err(|_| "Cannot establish that rename target is editable.")?;
    let mut inside = false;
    for root in roots {
        let Ok(canonical) = root.canonicalize() else {
            continue;
        };
        if let Ok(relative) = path.strip_prefix(&canonical) {
            if relative.as_os_str().is_empty() {
                continue;
            }
            inside = true;
            if protected(relative) || visible.strip_prefix(root).is_ok_and(protected) {
                return Err("Rename cannot edit generated or dependency files.".into());
            }
        }
    }
    if !inside {
        return Err("Rename cannot edit files outside the workspace.".into());
    }
    let permissions = path
        .metadata()
        .map_err(|_| "Cannot read file permissions.")?
        .permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if permissions.mode() & 0o222 == 0 {
            return Err("Rename cannot edit a read-only file.".into());
        }
    }
    if permissions.readonly() {
        return Err("Rename cannot edit a read-only file.".into());
    }
    // Check actual access too (ACLs can be stricter than mode bits); never truncate.
    std::fs::OpenOptions::new()
        .write(true)
        .open(&path)
        .map_err(|_| "Rename cannot edit a read-only file.")?;
    Ok(())
}

fn constant_sort(semantics: &Semantics, target: &Target) -> Option<denotate_analysis::Symbol> {
    let name = semantics
        .files
        .get(&target.uri)?
        .input
        .constants
        .iter()
        .find(|c| c.id == target.id)?
        .sort
        .as_ref()?;
    semantics
        .core
        .resolve_sort(target.uri.as_str(), name.clone())
}

/// Until step 3 projects every reference, even a rename initiated in a legacy
/// file can miss uses in a different file. Gate the whole indexed workspace.
fn has_unprojected_syntax(node: tree_sitter::Node<'_>) -> bool {
    matches!(
        node.kind(),
        "namespace"
            | "integer"
            | "quoted_identifier"
            | "qualified_name"
            | "generated_identifier"
            | "domain"
            | "obligation"
            | "assumption"
            | "source_location"
            | "location_alias"
            | "location"
    ) || (node.kind() == "source_file"
        && node
            .named_children(&mut node.walk())
            .filter(|n| n.kind() == "module")
            .count()
            != 1)
        || node.children(&mut node.walk()).any(has_unprojected_syntax)
}

pub fn rename(
    semantics: &Semantics,
    documents: &HashMap<Url, Document>,
    diagnostics: &HashMap<Url, Vec<lsp_types::Diagnostic>>,
    roots: &[PathBuf],
    uri: &Url,
    position: Position,
    name: Option<&str>,
) -> Result<Value, String> {
    if documents
        .values()
        .any(|doc| has_unprojected_syntax(doc.tree.root_node()))
    {
        return Err("Rename is unavailable while the workspace contains IR text syntax that the editor does not yet understand (authoring step 3).".into());
    }
    let doc = documents.get(uri).ok_or("No document.")?;
    let byte = doc.offset(position).ok_or("No rename target here.")?;
    let reference = semantics
        .reference_at(uri, byte)
        .ok_or("Rename requires one resolved, unambiguous target.")?;
    match &reference.lookup {
        Lookup::Anonymous { .. } => return Err("_ has no rename target.".into()),
        Lookup::Parameter => return Err("Parameter rename is not supported.".into()),
        _ => {}
    }
    let target = semantics
        .target(uri, reference)
        .ok_or("Rename requires one resolved, unambiguous target.")?;
    let kind = if target.rule.is_some() {
        "variable"
    } else {
        semantics
            .files
            .get(&target.uri)
            .and_then(|f| f.declarations.get(&target.id))
            .map(|d| d.kind.as_str())
            .ok_or("Unknown declaration.")?
    };
    if !matches!(
        kind,
        "variable" | "sort" | "constants" | "relation" | "input"
    ) {
        return Err("Only sorts, relations, constants and variables support rename; module rename needs file operations.".into());
    }
    // Do not widen this gate to unrelated validation errors (arity, duplicates,
    // module/filename checks). Incomplete or unresolved occurrences are unsafe.
    for diagnostics in diagnostics.values() {
        if diagnostics.iter().any(|d| {
            d.source.as_deref() == Some("denotate-syntax")
                || d.code == Some(lsp_types::NumberOrString::String("resolution".into()))
        }) {
            return Err("Rename requires a workspace without syntax or resolution errors. Repair diagnostics first.".into());
        }
    }
    let occurrences = semantics.occurrences(&target, true);
    if occurrences.is_empty() {
        return Err("No reliable rename locations.".into());
    }
    // Filesystem permissions belong to files, not individual occurrences.
    // Recheck each file on every request; do not cache access across edits.
    let files: BTreeSet<_> = std::iter::once(&target.uri)
        .chain(occurrences.iter().map(|(uri, _)| uri))
        .collect();
    for uri in files {
        editable(uri, roots)?;
    }
    let Some(name) = name else {
        return Ok(json!(Range::new(
            doc.position(reference.span.start),
            doc.position(reference.span.end)
        )));
    };
    let mut bytes = name.bytes();
    let initial = bytes.next().is_some_and(|b| match kind {
        "variable" => b.is_ascii_uppercase(),
        "constants" => b.is_ascii_lowercase(),
        _ => b.is_ascii_alphabetic(),
    });
    if !initial || !bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_') || reserved(name) {
        return Err(
            "Invalid rename: preserve the identifier lexical class and avoid reserved words and _."
                .into(),
        );
    }
    let collision = if let Some(rule) = &target.rule {
        semantics
            .core
            .rule_analysis(target.uri.as_str(), rule)
            .variables
            .iter()
            .any(|v| v.name == name && v.occurrences.first() != Some(&target.id))
    } else {
        let sort = constant_sort(semantics, &target);
        semantics.files.iter().any(|(uri, file)| {
            file.declarations.iter().any(|(id, declaration)| {
                if uri == &target.uri && id == &target.id {
                    return false;
                }
                let same_kind = match kind {
                    "relation" | "input" => {
                        matches!(declaration.kind.as_str(), "relation" | "input")
                    }
                    _ => declaration.kind == kind,
                };
                same_kind
                    && declaration.name == name
                    && (kind != "constants"
                        || constant_sort(
                            semantics,
                            &Target {
                                uri: uri.clone(),
                                rule: None,
                                id: id.clone(),
                            },
                        ) == sort)
            })
        })
    };
    if collision {
        return Err("Rename would collide with or capture another symbol. Conservatively checking the workspace namespace.".into());
    }
    let mut changes: Vec<Value> = vec![];
    for (uri, span) in occurrences {
        let doc = documents
            .get(&uri)
            .ok_or("Missing source for required rename edit.")?;
        let edit = json!({"range": Range::new(doc.position(span.start), doc.position(span.end)), "newText": name});
        if let Some(change) = changes
            .last_mut()
            .filter(|c| c["textDocument"]["uri"] == uri.as_str())
        {
            change["edits"].as_array_mut().unwrap().push(edit);
        } else {
            changes.push(json!({"textDocument": {"uri": uri, "version": doc.open.then_some(doc.version)}, "edits": [edit]}));
        }
    }
    Ok(json!({"documentChanges": changes}))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_ir_syntax_blocks_prepare_and_rename_even_from_a_legacy_file() {
        let library = Url::parse("file:///workspace/library.den").unwrap();
        let usage = Url::parse("file:///workspace/usage.den").unwrap();
        for suffix in [
            "const 1:S; r(1);",
            "relation 'other'(); 'other'();",
            "library::r(a);",
            "relation $condition_1(); $condition_1();",
            "domain S=[a];",
            "obligation unique: at_most_one(r, group_by: ());",
            "input p(x:S); assumption unique: at_most_one(p, group_by: ());",
            "r(a) loc(#origin);",
            "#s = source(\"file:///x\", view: \"dsl\", hash: \"sha256:0000000000000000000000000000000000000000000000000000000000000000\");",
            "#origin = loc(#s 1:1 to 1:2);",
        ] {
            let mut parser = crate::syntax::parser();
            let documents = HashMap::from([
                (
                    library.clone(),
                    Document::new(
                        &mut parser,
                        "module library; sort S; const a:S; relation r(x:S);".into(),
                        1,
                        true,
                    ),
                ),
                (
                    usage.clone(),
                    Document::new(
                        &mut parser,
                        format!("module usage; use library; {suffix}"),
                        1,
                        false,
                    ),
                ),
            ]);
            let mut semantics = Semantics::default();
            for (uri, doc) in &documents {
                assert!(
                    doc.diagnostics().is_empty(),
                    "{suffix}: {:?}",
                    doc.diagnostics()
                );
                semantics.update(uri, doc);
            }
            for uri in [&library, &usage] {
                for name in [None, Some("renamed")] {
                    let error = rename(
                        &semantics,
                        &documents,
                        &HashMap::new(),
                        &[],
                        uri,
                        Position::new(0, 42),
                        name,
                    )
                    .unwrap_err();
                    assert!(
                        error.contains("does not yet understand"),
                        "{suffix}: {error}"
                    );
                }
            }
        }
    }

    #[test]
    fn syntax_gate_handles_namespaces_and_global_files_but_ignores_comments() {
        let mut parser = crate::syntax::parser();
        for (text, blocked) in [
            ("namespace m;", true),
            ("namespace a { namespace b { relation r(); } }", true),
            ("relation r(); r();", true),
            ("module m; // domain obligation loc(1) 'quoted' module::name\n sort S; const a:S; relation source_value(x:S); source_value(X) :- source_value(X);", false),
        ] {
            let doc = Document::new(&mut parser, text.into(), 1, true);
            assert!(doc.diagnostics().is_empty());
            assert_eq!(has_unprojected_syntax(doc.tree.root_node()), blocked);
        }
    }
}
