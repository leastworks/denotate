//! Refactoring uses source-anchor correspondence, never arena or name-derived IDs.
use crate::Server;
use denotate_editor::workspace_edit::{self, Edit, EditabilityError, FileEdits};
use denotate_ir_text::{
    index::{self, Index, Kind, Lookup, Projection},
    spelling, NameKind, ProgramMembership, SourceFile,
};
use lsp_types::{Position, Range, Url};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range as Span,
    path::PathBuf,
};

fn editable(uri: &Url, roots: &[PathBuf]) -> Result<(), String> {
    workspace_edit::editable(uri, roots, workspace_edit::DEFAULT_PROTECTED_FOLDERS).map_err(
        |error| {
            match error {
                EditabilityError::NotFile => "Rename requires editable workspace files.",
                EditabilityError::Unavailable => "Cannot establish that rename target is editable.",
                EditabilityError::Protected => "Rename cannot edit generated or dependency files.",
                EditabilityError::OutsideWorkspace => {
                    "Rename cannot edit files outside the workspace."
                }
                EditabilityError::PermissionsUnavailable => "Cannot read file permissions.",
                EditabilityError::ReadOnly => "Rename cannot edit a read-only file.",
            }
            .into()
        },
    )
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Anchor {
    uri: String,
    start: usize,
    end: usize,
    kind: Option<Kind>, // None denotes a rule-local variable's first occurrence.
    generated: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Identity {
    Symbol(Anchor),
    Namespace(Vec<String>),
    Anonymous,
}
#[derive(Clone, Debug)]
struct Binding {
    span: Span<usize>,
    identity: Identity,
}
type Edits = BTreeMap<String, Vec<Edit>>;
struct Program {
    membership: ProgramMembership,
    members: BTreeSet<String>,
    error: Option<String>,
}
fn symbol(index: &Index, uri: &str, id: &str) -> Result<Identity, String> {
    let file = &index.files[uri];
    let declaration = file.declarations.get(id).ok_or("Missing declaration")?;
    let span = &file.anchors[id];
    Ok(Identity::Symbol(Anchor {
        uri: uri.into(),
        start: span.start,
        end: span.end,
        kind: Some(declaration.kind),
        generated: declaration.name.generated,
    }))
}
fn namespace_bindings(
    out: &mut Vec<Binding>,
    spans: &[Span<usize>],
    path: &[String],
) -> Result<(), String> {
    let base = path
        .len()
        .checked_sub(spans.len())
        .ok_or("Incomplete namespace reference")?;
    for (i, span) in spans.iter().enumerate() {
        out.push(Binding {
            span: span.clone(),
            identity: Identity::Namespace(path[..base + i + 1].to_vec()),
        });
    }
    Ok(())
}
fn bindings(index: &Index, root: &str, uri: &str) -> Result<Vec<Binding>, String> {
    let file = index.files.get(uri).ok_or("Missing member snapshot")?;
    let mut out = vec![];
    for r in &file.references {
        let raw = &file.source.text[r.span.clone()];
        let spans = index::name_segments(raw)
            .into_iter()
            .map(|s| r.span.start + s.start..r.span.start + s.end)
            .collect::<Vec<_>>();
        let namespace = match &r.lookup {
            Lookup::Declaration(id) if file.declarations[id].kind == Kind::Namespace => {
                Some(file.declarations[id].scope.namespace.segments().to_vec())
            }
            Lookup::Name(Kind::Namespace) => {
                let node = file
                    .tree
                    .root_node()
                    .descendant_for_byte_range(r.span.start, r.span.end)
                    .ok_or("Missing namespace path")?;
                Some(
                    index::namespace_path(&file.source, node)
                        .map_err(|_| "Invalid namespace path")?
                        .segments()
                        .to_vec(),
                )
            }
            _ => None,
        };
        if let Some(path) = namespace {
            namespace_bindings(&mut out, &spans, &path)?;
            continue;
        }
        if let Some(namespace) = &r.name.namespace {
            namespace_bindings(&mut out, &spans[..spans.len() - 1], namespace.segments())?;
        }
        let identity = match &r.lookup {
            Lookup::Anonymous(_) => Identity::Anonymous,
            Lookup::Variable { rule, occurrence } => {
                let analysis = index.rule_analysis(root, uri, rule);
                let first = analysis
                    .variables
                    .iter()
                    .find(|v| v.occurrences.contains(occurrence))
                    .and_then(|v| v.occurrences.first())
                    .ok_or("Incomplete variable binding")?;
                let span = &file.rule_anchors[rule][first];
                Identity::Symbol(Anchor {
                    uri: uri.into(),
                    start: span.start,
                    end: span.end,
                    kind: None,
                    generated: false,
                })
            }
            _ => {
                let candidates = index.candidates(root, uri, &r.scope, &r.lookup, Some(&r.name));
                let [target] = candidates.as_slice() else {
                    return Err(format!("Rename requires resolved, unambiguous references in {root}. Repair diagnostics first ({uri}: {}).", r.name.spelling()));
                };
                symbol(index, &target.uri, &target.id)?
            }
        };
        out.push(Binding {
            span: spans.last().cloned().ok_or("Missing reference segment")?,
            identity,
        });
    }
    out.sort_by_key(|b| (b.span.start, b.span.end));
    Ok(out)
}
fn renamed_namespace(path: &[String], target: &Identity, name: &str) -> Vec<String> {
    let mut path = path.to_vec();
    if let Identity::Namespace(prefix) = target {
        if path.starts_with(prefix) {
            path[prefix.len() - 1] = name.into();
        }
    }
    path
}
fn mapped_span(span: &Span<usize>, edits: &[Edit]) -> Result<Span<usize>, String> {
    workspace_edit::mapped_span(span, edits)
        .map_err(|_| "Rename edits overlap an unrelated source anchor".into())
}
fn mapped_identity(
    identity: &Identity,
    edits: &Edits,
    target: &Identity,
    name: &str,
) -> Result<Identity, String> {
    Ok(match identity {
        Identity::Namespace(path) => Identity::Namespace(renamed_namespace(path, target, name)),
        Identity::Symbol(anchor) => {
            let span = mapped_span(
                &(anchor.start..anchor.end),
                edits.get(&anchor.uri).map_or(&[], Vec::as_slice),
            )?;
            Identity::Symbol(Anchor {
                start: span.start,
                end: span.end,
                ..anchor.clone()
            })
        }
        Identity::Anonymous => Identity::Anonymous,
    })
}
fn replacement(target: &Identity, name: &str) -> Result<String, String> {
    if name.is_empty() {
        return Err("Rename requires a nonempty name".into());
    }
    let kind = match target {
        Identity::Namespace(_) => NameKind::Identifier,
        Identity::Anonymous => return Err("_ has no rename target.".into()),
        Identity::Symbol(a) => match a.kind {
            None => NameKind::Variable,
            Some(Kind::Constant) => NameKind::Constant,
            Some(Kind::Parameter) => NameKind::Parameter,
            Some(Kind::Alias) => {
                let name = name.strip_prefix('#').unwrap_or(name);
                let text = spelling(name, NameKind::Parameter);
                if text != name {
                    return Err("A location alias requires an ASCII identifier after #".into());
                }
                return Ok(format!("#{text}"));
            }
            _ if a.generated => {
                let name = name.strip_prefix('$').unwrap_or(name);
                let text = spelling(name, NameKind::Parameter);
                if text != name {
                    return Err("A generated helper requires an ASCII identifier after $".into());
                }
                return Ok(format!("${text}"));
            }
            _ => NameKind::Identifier,
        },
    };
    Ok(spelling(name, kind))
}
fn namespace_inventory(index: &Index, members: &BTreeSet<String>) -> BTreeSet<Vec<String>> {
    let mut result = BTreeSet::new();
    for uri in members {
        for declaration in index.files[uri].declarations.values() {
            let path = declaration.scope.namespace.segments();
            for n in 1..=path.len() {
                result.insert(path[..n].to_vec());
            }
        }
    }
    result
}
fn checked_bindings(
    index: &Index,
    program: &Program,
) -> Result<BTreeMap<String, Vec<Binding>>, String> {
    if let Some(error) = &program.error {
        return Err(format!(
            "Cannot validate affected program {}: {error}. Repair diagnostics first.",
            program.membership.root
        ));
    }
    let namespaces = namespace_inventory(index, &program.members);
    let mut result = BTreeMap::new();
    for uri in &program.members {
        let file = &index.files[uri];
        if file.tree.root_node().has_error() || !file.issues.is_empty() {
            return Err(format!(
                "Rename requires complete syntax in {uri}. Repair diagnostics first."
            ));
        }
        let refs = bindings(index, &program.membership.root, uri)?;
        for r in &refs {
            if let Identity::Namespace(path) = &r.identity {
                if !namespaces.contains(path) {
                    return Err(format!(
                        "Rename cannot resolve namespace in {uri}. Repair diagnostics first."
                    ));
                }
            }
        }
        result.insert(uri.clone(), refs);
    }
    Ok(result)
}
fn validate(
    before: &Index,
    after: &Index,
    programs: &[&Program],
    edits: &Edits,
    target: &Identity,
    name: &str,
) -> Result<(), String> {
    for program in programs {
        let root = &program.membership.root;
        let old = checked_bindings(before, program)?;
        let new = checked_bindings(after, program)
            .map_err(|e| format!("Rename would collide, capture or invalidate a reference: {e}"))?;
        let namespaces = namespace_inventory(before, &program.members);
        let mapped = namespaces
            .iter()
            .map(|p| renamed_namespace(p, target, name))
            .collect::<BTreeSet<_>>();
        if mapped.len() != namespaces.len() {
            return Err(format!(
                "Rename would collide with another namespace in {root}"
            ));
        }
        for uri in &program.members {
            let file_edits: &[Edit] = edits.get(uri).map_or(&[], Vec::as_slice);
            let issues = |index: &Index| {
                let mut issues = index
                    .diagnostics(root, uri)
                    .into_iter()
                    .filter(|d| !d.warning)
                    .map(|d| (d.code, d.span))
                    .collect::<Vec<_>>();
                let file = &index.files[uri];
                // Parameter names and contract labels are local identities too.
                // Do not let an earlier, unrelated strict-load failure conceal a
                // newly introduced duplicate in one of these declarations.
                for d in file
                    .declarations
                    .values()
                    .filter(|d| matches!(d.kind, Kind::Parameter | Kind::Contract))
                {
                    let form = |id: &String| {
                        let span = &file.anchors[id];
                        file.tree
                            .root_node()
                            .descendant_for_byte_range(span.start, span.end)
                            .and_then(|n| n.parent())
                            .map(|n| n.kind().to_string())
                    };
                    if file.declarations.values().any(|other| {
                        other.id != d.id
                            && other.kind == d.kind
                            && other.name == d.name
                            && other.scope.namespace == d.scope.namespace
                            && other.parent == d.parent
                            && form(&other.id) == form(&d.id)
                    }) {
                        issues.push(("duplicate-declaration".into(), file.anchors[&d.id].clone()));
                    }
                }
                issues
            };
            let old_issues = issues(before)
                .into_iter()
                .map(|(code, span)| {
                    let span = mapped_span(&span, file_edits)?;
                    Ok((code, span.start, span.end))
                })
                .collect::<Result<BTreeSet<_>, String>>()?;
            for (code, span) in issues(after) {
                if !old_issues.contains(&(code.clone(), span.start, span.end)) {
                    return Err(format!(
                        "Rename would collide or invalidate {uri} in {root}: {code}"
                    ));
                }
            }
            let expected = old[uri]
                .iter()
                .map(|b| {
                    Ok(Binding {
                        span: mapped_span(&b.span, file_edits)?,
                        identity: mapped_identity(&b.identity, edits, target, name)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            if expected.len() != new[uri].len()
                || expected
                    .iter()
                    .zip(&new[uri])
                    .any(|(a, b)| a.span != b.span || a.identity != b.identity)
            {
                return Err(format!(
                    "Rename would collide with or capture a reference in {uri} (program {root})"
                ));
            }
            // Declaration correspondence includes unreferenced declarations and
            // their generated/frontend kind. IDs are used only to read anchors.
            let declarations =
                |file: &Projection, transform: bool| -> Result<BTreeSet<_>, String> {
                    file.declarations
                        .values()
                        .map(|d| {
                            let span = &file.anchors[&d.id];
                            let span = if transform {
                                mapped_span(span, file_edits)?
                            } else {
                                span.clone()
                            };
                            Ok((span.start, span.end, d.kind, d.name.generated))
                        })
                        .collect()
                };
            if declarations(&before.files[uri], true)? != declarations(&after.files[uri], false)? {
                return Err(format!("Rename changed declaration structure in {uri}"));
            }
        }
        // The strict loader catches duplicate parameters/contracts, alias cycles
        // and sort constraints as well as parser/index errors. Existing unrelated
        // errors may remain, but no new error may appear after the rename.
        let errors = |index: &Index| {
            let files = program
                .members
                .iter()
                .map(|u| index.files[u].source.clone())
                .collect::<Vec<_>>();
            denotate_ir_text::load(&program.membership, &files)
                .err()
                .unwrap_or_default()
        };
        let old_errors = errors(before)
            .into_iter()
            .map(|d| {
                let span = mapped_span(&d.range, edits.get(&d.uri).map_or(&[], Vec::as_slice))?;
                Ok((d.uri, span.start, span.end, d.message))
            })
            .collect::<Result<BTreeSet<_>, String>>()?;
        for d in errors(after) {
            if !old_errors.contains(&(d.uri.clone(), d.range.start, d.range.end, d.message.clone()))
            {
                return Err(format!(
                    "Rename would collide or invalidate program {root}: {} ({})",
                    d.message, d.uri
                ));
            }
        }
    }
    Ok(())
}
impl Server {
    fn rename_programs(&self) -> Result<Vec<Program>, String> {
        // A broken manifest can conceal a consumer edge; never guess that its
        // absence makes a shared-library rename safe.
        if !self.catalog.discovery_errors.is_empty()
            || self.catalog.nodes.values().any(|n| !n.errors.is_empty())
        {
            return Err("Cannot establish every affected root while discovery or a manifest is invalid. Repair diagnostics first.".into());
        }
        let aliases = self
            .documents
            .keys()
            .map(|u| (Self::canonical_document(u), u.to_string()))
            .collect::<BTreeMap<_, _>>();
        let mut memberships = self.catalog.programs.values().cloned().collect::<Vec<_>>();
        for uri in self.documents.keys() {
            if self.catalog.status(&Self::canonical_document(uri))["state"] == "standalone" {
                memberships.push(ProgramMembership::single(uri.as_str(), [uri.to_string()]));
            }
        }
        memberships
            .into_iter()
            .map(|mut membership| {
                for node in membership.roots.values_mut() {
                    node.files = node
                        .files
                        .iter()
                        .map(|u| aliases.get(u).unwrap_or(u).clone())
                        .collect();
                }
                let members = membership
                    .members()
                    .map_err(|_| "Cannot establish program membership")?
                    .into_keys()
                    .collect::<BTreeSet<_>>();
                let error = self
                    .catalog
                    .errors
                    .get(&membership.root)
                    .filter(|e| !e.is_empty())
                    .map(|e| e.join("; "))
                    .or_else(|| {
                        members.iter().find_map(|u| {
                            let uri = Url::parse(u).ok()?;
                            if self.documents.rejected_version(&uri).is_some() {
                                Some(format!("{u} is out of sync"))
                            } else if !self.documents.contains_key(&uri) {
                                Some(format!("{u} has no authoritative snapshot"))
                            } else {
                                None
                            }
                        })
                    });
                Ok(Program {
                    membership,
                    members,
                    error,
                })
            })
            .collect()
    }
    fn rename_stamp(&self) -> Value {
        json!({"observations":self.observations.iter().map(|(u,o)|(u.as_str(),o)).collect::<BTreeMap<_,_>>(),
            "members":self.catalog.programs.iter().map(|(r,p)|(r,p.roots.iter().map(|(k,n)|(k,json!({"files":n.files,"libraries":n.libraries}))).collect::<BTreeMap<_,_>>())).collect::<BTreeMap<_,_>>(),
            "manifests":self.catalog.nodes.iter().map(|(r,n)|(r,n.snapshot.as_ref().map(|s|(&s.text,s.version)))).collect::<BTreeMap<_,_>>()})
    }
    pub fn rename_at(
        &self,
        uri: &Url,
        position: Position,
        name: Option<&str>,
    ) -> Result<Value, String> {
        // The owner handles requests serially; this immutable borrow spans the
        // complete dry run and final snapshot check. No worker or disk fallback
        // can replace a buffer in the middle of a rename.
        let stamp = self.rename_stamp();
        let programs = self.rename_programs()?;
        let core = &self.semantics.core;
        let home = self
            .semantics
            .root(uri)
            .ok_or("No valid home program for rename")?;
        let doc = self.documents.get(uri).ok_or("Missing document")?;
        let byte = doc.offset(position).ok_or("No rename target")?;
        let here = bindings(core, home, uri.as_str())?;
        let selected = here
            .iter()
            .find(|r| r.span.contains(&byte))
            .or_else(|| {
                here.iter()
                    .find(|r| !r.span.is_empty() && r.span.end == byte)
            })
            .ok_or("No resolved, unambiguous rename target here")?;
        let target = &selected.identity;
        if target == &Identity::Anonymous {
            return Err("_ has no rename target.".into());
        }
        let mut files = BTreeSet::from([uri.to_string()]);
        if let Identity::Symbol(a) = target {
            files.insert(a.uri.clone());
        }
        let text = name.map(|n| replacement(target, n)).transpose()?;
        let mut edits: Edits = BTreeMap::new();
        let mut affected = BTreeSet::new();
        loop {
            let pending = programs
                .iter()
                .filter(|p| {
                    !affected.contains(&p.membership.root) && !p.members.is_disjoint(&files)
                })
                .collect::<Vec<_>>();
            if pending.is_empty() {
                break;
            }
            for program in pending {
                affected.insert(program.membership.root.clone());
                for (uri, refs) in checked_bindings(core, program)? {
                    for r in refs.into_iter().filter(|r| &r.identity == target) {
                        files.insert(uri.clone());
                        let text = text
                            .clone()
                            .unwrap_or_else(|| core.files[&uri].source.text[r.span.clone()].into());
                        let list = edits.entry(uri.clone()).or_default();
                        if !list.iter().any(|e| e.span == r.span) {
                            list.push(Edit { span: r.span, text });
                        }
                    }
                }
            }
        }
        if edits.is_empty() {
            return Err("No reliable rename locations".into());
        }
        for (uri, list) in &mut edits {
            editable(&Url::parse(uri).map_err(|e| e.to_string())?, &self.roots)?;
            list.sort_by_key(|e| e.span.start);
            if list.windows(2).any(|e| e[0].span.end > e[1].span.start) {
                return Err("Rename locations overlap".into());
            }
        }
        // A duplicate declaration selected directly must not bypass resolution.
        if let Identity::Symbol(a) = target {
            for program in programs
                .iter()
                .filter(|p| affected.contains(&p.membership.root) && p.members.contains(&a.uri))
            {
                if core
                    .diagnostics(&program.membership.root, &a.uri)
                    .iter()
                    .any(|d| d.code == "duplicate-declaration" && d.span == (a.start..a.end))
                {
                    return Err("Rename target is not unambiguous: duplicate declaration".into());
                }
            }
        }
        let Some(name) = name else {
            let range = Range::new(
                doc.position(selected.span.start),
                doc.position(selected.span.end),
            );
            let logical = match target {
                Identity::Namespace(path) => path.last().map(String::as_str),
                _ => core.files[uri.as_str()]
                    .references
                    .iter()
                    .find(|r| {
                        r.span.start <= selected.span.start && r.span.end == selected.span.end
                    })
                    .map(|r| r.name.text.as_str()),
            };
            // A quoted name's syntax is not its logical replacement name. Give
            // the rename box decoded text so accepting/editing it cannot add an
            // unintended layer of quotes or turn a variable into a constant.
            return Ok(match logical {
                Some(placeholder) if placeholder != &doc.text[selected.span.clone()] => {
                    json!({"range":range,"placeholder":placeholder})
                }
                _ => json!(range),
            });
        };
        let mut after = Index::default();
        let mut parser = crate::syntax::parser();
        for (uri, file) in &core.files {
            let mut text = file.source.text.to_string();
            for edit in edits.get(uri).into_iter().flatten().rev() {
                text.replace_range(edit.span.clone(), &edit.text);
            }
            let tree = parser.parse(&text, None).ok_or("Rename parsing failed")?;
            after.update(SourceFile::new(uri, file.source.revision, text), tree);
        }
        for program in &programs {
            after
                .set_membership(&program.membership)
                .map_err(|_| "Rename membership changed")?;
        }
        let affected = programs
            .iter()
            .filter(|p| affected.contains(&p.membership.root))
            .collect::<Vec<_>>();
        validate(core, &after, &affected, &edits, target, name)?;
        workspace_edit::assemble(
            edits.iter().map(|(uri, edits)| {
                let doc = &self.documents[&Url::parse(uri).unwrap()];
                FileEdits::new(uri, doc, edits)
            }),
            &stamp,
            || self.rename_stamp(),
        )
        .map_err(|_| "Rename snapshots changed; try again".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn index(text: &str) -> (Index, Program) {
        let uri = "file:///program.den";
        let mut index = Index::default();
        let tree = crate::syntax::parser().parse(text, None).unwrap();
        index.update(SourceFile::new(uri, 1, text), tree);
        let membership = ProgramMembership::single("root", [uri.into()]);
        index.set_membership(&membership).unwrap();
        (
            index,
            Program {
                membership,
                members: BTreeSet::from([uri.into()]),
                error: None,
            },
        )
    }
    #[test]
    fn correspondence_rejects_a_missing_reference_edit_even_if_after_resolves_uniquely() {
        // The untouched r() changes binding from a's renamed declaration to b's
        // declaration. A validator checking only edited occurrences misses it.
        let text = "namespace a { relation r(); } namespace b { relation r(); } namespace app { use a; a::r(); }";
        let (before, program) = index(text);
        let uri = "file:///program.den";
        let decl = text.find("r();").unwrap();
        let target = bindings(&before, "root", uri)
            .unwrap()
            .into_iter()
            .find(|b| b.span.start == decl)
            .unwrap()
            .identity;
        // Deliberately malformed proposal: edits a's declaration and replaces
        // the reference's namespace with b instead of renaming its member.
        let prefix = text.find("a::r()").unwrap();
        let edits = BTreeMap::from([(
            uri.into(),
            vec![
                Edit {
                    span: decl..decl + 1,
                    text: "q".into(),
                },
                Edit {
                    span: prefix..prefix + 1,
                    text: "b".into(),
                },
            ],
        )]);
        let mut changed = text.to_string();
        for e in edits[uri].iter().rev() {
            changed.replace_range(e.span.clone(), &e.text);
        }
        let (after, _) = index(&changed);
        assert!(validate(&before, &after, &[&program], &edits, &target, "q")
            .unwrap_err()
            .contains("capture"));
    }
    #[test]
    fn new_duplicate_cannot_hide_behind_an_existing_strict_loader_failure() {
        let text = "sort Unrelated; sort Unrelated; sort A; sort B;";
        let (before, program) = index(text);
        let uri = "file:///program.den";
        let start = text.find("A;").unwrap();
        let target = bindings(&before, "root", uri)
            .unwrap()
            .into_iter()
            .find(|b| b.span.start == start)
            .unwrap()
            .identity;
        let edits = BTreeMap::from([(
            uri.into(),
            vec![Edit {
                span: start..start + 1,
                text: "B".into(),
            }],
        )]);
        let (after, _) = index(&text.replace("A;", "B;"));
        assert!(validate(&before, &after, &[&program], &edits, &target, "B")
            .unwrap_err()
            .contains("collide"));
    }
    #[test]
    fn segments_and_spelling_preserve_lexical_kinds_and_quoted_separators() {
        let raw = "::'a::b'::'c\\'d'::007";
        let segments = index::name_segments(raw)
            .into_iter()
            .map(|r| &raw[r])
            .collect::<Vec<_>>();
        assert_eq!(segments, ["'a::b'", "'c\\'d'", "007"]);
        let anchor = Anchor {
            uri: String::new(),
            start: 0,
            end: 1,
            kind: Some(Kind::Constant),
            generated: false,
        };
        assert_eq!(
            replacement(&Identity::Symbol(anchor.clone()), "I").unwrap(),
            "'I'"
        );
        assert_eq!(
            replacement(&Identity::Symbol(anchor), "007").unwrap(),
            "'007'"
        );
    }
}
