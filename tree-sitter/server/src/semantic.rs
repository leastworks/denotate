//! LSP presentation over ir-text's shared, root-scoped index.
use crate::syntax::Document;
use denotate_ir_text::{
    index::{
        self, Declaration, Expected, Index, Kind, Lookup, Name, Projection, Reference, Scope,
        Symbol,
    },
    ProgramMembership, SourceFile,
};
use lsp_types::{Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range, Url};
use serde_json::{json, Value};
use std::{collections::HashMap, ops::Range as ByteRange, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Target {
    pub uri: Url,
    pub rule: Option<String>,
    pub id: String,
}
#[derive(Default)]
pub struct Semantics {
    pub core: Index,
    pub files: HashMap<Url, Arc<Projection>>,
    selected: HashMap<Url, Option<String>>,
}
impl Semantics {
    pub fn update(&mut self, uri: &Url, doc: &Document) {
        let _projection = crate::timing::interval("projection");
        let _update = crate::timing::interval("update");
        self.core.update(
            SourceFile::new(uri.as_str(), doc.version as u64, doc.text.as_str()),
            doc.tree.clone(),
        );
        self.files
            .insert(uri.clone(), self.core.files[uri.as_str()].clone());
        self.core
            .set_membership(&ProgramMembership::single(uri.as_str(), [uri.to_string()]))
            .unwrap();
    }
    /// Stage 1 consumes explicit memberships. Stage 2 owns the active-root
    /// catalog and selection protocol; ambiguous contexts already fail closed.
    pub fn memberships(&mut self, programs: &[ProgramMembership]) {
        self.selected.clear();
        for program in programs {
            if let Ok(members) = program.members() {
                self.core.set_membership(program).unwrap();
                for uri in members.keys().filter_map(|u| Url::parse(u).ok()) {
                    self.selected
                        .entry(uri)
                        .and_modify(|selected| {
                            if selected.as_ref() != Some(&program.root) {
                                *selected = None;
                            }
                        })
                        .or_insert(Some(program.root.clone()));
                }
            }
        }
    }
    pub fn block_context(&mut self, uri: &Url) {
        self.selected.insert(uri.clone(), None);
    }
    pub fn root<'a>(&'a self, uri: &'a Url) -> Option<&'a str> {
        self.selected
            .get(uri)
            .map_or(Some(uri.as_str()), |s| s.as_deref())
    }
    pub fn remove(&mut self, uri: &Url) {
        self.core.remove(uri.as_str());
        self.files.remove(uri);
    }
    pub fn candidates(
        &self,
        uri: &Url,
        scope: &Scope,
        lookup: &Lookup,
        name: Option<&Name>,
    ) -> Vec<Symbol> {
        let _timer = crate::timing::interval("query");
        self.root(uri).map_or_else(Vec::new, |root| {
            self.core
                .candidates(root, uri.as_str(), scope, lookup, name)
        })
    }
    pub fn rule_analysis(&self, uri: &Url, rule: &str) -> index::RuleAnalysis {
        self.root(uri).map_or_else(Default::default, |root| {
            self.core.rule_analysis(root, uri.as_str(), rule)
        })
    }
    pub fn reference_at(&self, uri: &Url, byte: usize) -> Option<&Reference> {
        self.files.get(uri)?.reference_at(byte)
    }
    pub fn target(&self, uri: &Url, r: &Reference) -> Option<Target> {
        if let Lookup::Variable { rule, occurrence } = &r.lookup {
            return self
                .rule_analysis(uri, rule)
                .variables
                .iter()
                .find(|v| v.occurrences.contains(occurrence))
                .and_then(|v| v.occurrences.first())
                .map(|id| Target {
                    uri: uri.clone(),
                    rule: Some(rule.clone()),
                    id: id.clone(),
                });
        }
        let matches = self.candidates(uri, &r.scope, &r.lookup, Some(&r.name));
        let [symbol] = matches.as_slice() else {
            return None;
        };
        Some(Target {
            uri: Url::parse(&symbol.uri).ok()?,
            rule: None,
            id: symbol.id.clone(),
        })
    }
    pub fn target_span(&self, target: &Target) -> Option<&ByteRange<usize>> {
        let _timer = crate::timing::interval("sourceLookup");
        let file = self.files.get(&target.uri)?;
        if let Some(rule) = &target.rule {
            file.rule_anchors.get(rule)?.get(&target.id)
        } else {
            file.anchors.get(&target.id)
        }
    }
    pub fn declaration(&self, target: &Target) -> Option<&Declaration> {
        self.files.get(&target.uri)?.declarations.get(&target.id)
    }
    pub fn constant_sort(&self, context: &Url, target: &Target) -> Option<Symbol> {
        let d = self.declaration(target)?;
        self.core.expected_sort(
            self.root(context)?,
            &d.scope,
            &Expected::Sort(d.sort.clone()?),
        )
    }
    pub fn occurrences(
        &self,
        target: &Target,
        include_declaration: bool,
    ) -> Vec<(Url, ByteRange<usize>)> {
        let _timer = crate::timing::interval("references");
        let mut out = vec![];
        for (uri, file) in &self.files {
            if target.rule.is_some() && uri != &target.uri {
                continue;
            }
            for r in &file.references {
                if self.target(uri, r).as_ref() == Some(target)
                    && (include_declaration
                        || uri != &target.uri
                        || self.target_span(target) != Some(&r.span))
                {
                    out.push((uri.clone(), r.span.clone()));
                }
            }
        }
        out.sort_by(|a, b| (&a.0, a.1.start).cmp(&(&b.0, b.1.start)));
        out
    }
    fn namespace_name(&self, uri: &Url, reference: &Reference) -> Option<Name> {
        match &reference.lookup {
            Lookup::Name(Kind::Namespace) => Some(reference.name.clone()),
            Lookup::Declaration(id) => self
                .files
                .get(uri)?
                .declarations
                .get(id)
                .filter(|d| d.kind == Kind::Namespace)
                .map(|d| d.name.clone()),
            _ => None,
        }
    }
    pub fn references(
        &self,
        uri: &Url,
        doc: &Document,
        position: Position,
        include: bool,
        documents: &HashMap<Url, Document>,
    ) -> Value {
        if let Some(name) = doc
            .offset(position)
            .and_then(|b| self.reference_at(uri, b))
            .and_then(|r| self.namespace_name(uri, r))
        {
            let mut locations = vec![];
            for (owner, file) in &self.files {
                if self.root(owner) != self.root(uri) {
                    continue;
                }
                for r in &file.references {
                    if self.namespace_name(owner, r).as_ref() == Some(&name)
                        && (include || !matches!(r.lookup, Lookup::Declaration(_)))
                    {
                        if let Some(doc) = documents.get(owner) {
                            locations.push(json!({"uri":owner,"range":range(doc,&r.span)}));
                        }
                    }
                }
            }
            locations.sort_by_key(Value::to_string);
            return json!(locations);
        }
        let target = doc
            .offset(position)
            .and_then(|b| self.reference_at(uri, b))
            .and_then(|r| self.target(uri, r));
        let Some(target) = target else {
            return json!([]);
        };
        json!(self
            .occurrences(&target, include)
            .into_iter()
            .filter_map(|(uri, span)| Some(
                json!({"uri":uri,"range":range(documents.get(&uri)?, &span)})
            ))
            .collect::<Vec<_>>())
    }
    fn signature(&self, context: &Url, target: &Target) -> Option<(String, Vec<String>)> {
        let d = self.declaration(target)?;
        let parameters = d
            .parameters
            .as_ref()?
            .iter()
            .map(|(name, sort)| {
                let label = sort
                    .as_ref()
                    .and_then(|s| {
                        self.core.expected_sort(
                            self.root(context)?,
                            &d.scope,
                            &Expected::Sort(s.clone()),
                        )
                    })
                    .map(|s| s.name)
                    .unwrap_or_else(|| {
                        format!(
                            "{} (unresolved)",
                            sort.as_ref().map_or("?".into(), Name::spelling)
                        )
                    });
                format!("{name}: {label}")
            })
            .collect::<Vec<_>>();
        Some((
            format!("{}({})", d.name.spelling(), parameters.join(", ")),
            parameters,
        ))
    }
    pub fn signature_help(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let result = (|| {
            let (Lookup::Constant(Expected::Argument(relation, index)), scope, _) = self
                .files
                .get(uri)?
                .completion_context(doc.offset(position)?)?
            else {
                return None;
            };
            let matches =
                self.candidates(uri, &scope, &Lookup::Name(Kind::Relation), Some(&relation));
            let [symbol] = matches.as_slice() else {
                return None;
            };
            let (label, params) = self.signature(
                uri,
                &Target {
                    uri: Url::parse(&symbol.uri).ok()?,
                    rule: None,
                    id: symbol.id.clone(),
                },
            )?;
            Some(
                json!({"signatures":[{"label":label,"parameters":params.iter().map(|label|json!({"label":label})).collect::<Vec<_>>()}],"activeSignature":0,"activeParameter":(index < params.len()).then_some(index)}),
            )
        })();
        result.unwrap_or(Value::Null)
    }
    fn sort_label(&self, uri: &Url, scope: &Scope, sort: Symbol) -> String {
        let ambiguous = self
            .candidates(
                uri,
                scope,
                &Lookup::Name(Kind::Sort),
                Some(&Name::bare(&sort.name)),
            )
            .iter()
            .any(|s| s != &sort);
        if ambiguous {
            format!("{}.{}", sort.module.as_deref().unwrap_or(""), sort.name)
        } else {
            sort.name
        }
    }
    pub fn hover(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let result = (|| {
            let r = self.reference_at(uri, doc.offset(position)?)?;
            if let Some(name) = self.namespace_name(uri, r) {
                let matches =
                    self.candidates(uri, &r.scope, &Lookup::Name(Kind::Namespace), Some(&name));
                if matches.is_empty() {
                    return None;
                }
                return Some(
                    json!({"contents":{"kind":"plaintext","value":format!("namespace {}",name.text)},"range":range(doc,&r.span)}),
                );
            }
            let text = match &r.lookup {
                Lookup::Anonymous(expected) => {
                    let sort = self.core.expected_sort(self.root(uri)?, &r.scope, expected);
                    format!(
                        "_: {}\n\nAnonymous argument; each _ is independent.",
                        sort.as_ref().map_or("unknown sort", |s| s.name.as_str())
                    )
                }
                Lookup::Variable { rule, occurrence } => {
                    let analysis = self.rule_analysis(uri, rule);
                    let v = analysis
                        .variables
                        .iter()
                        .find(|v| v.occurrences.contains(occurrence))?;
                    if v.sorts.len() > 1 {
                        let mut labels = v
                            .sorts
                            .iter()
                            .map(|s| format!("{}.{}", s.module.as_deref().unwrap_or("?"), s.name))
                            .collect::<Vec<_>>();
                        labels.sort();
                        format!(
                            "variable {}\nConflicting expected sorts: {}",
                            v.name,
                            labels.join(", ")
                        )
                    } else {
                        format!(
                            "variable {}: {}{}",
                            v.name,
                            v.sorts.first().map_or("unknown sort", |s| s.name.as_str()),
                            if v.unknown && !v.sorts.is_empty() {
                                "\nSome occurrences have unknown argument sorts."
                            } else {
                                ""
                            }
                        )
                    }
                }
                _ => {
                    let target = self.target(uri, r)?;
                    let d = self.declaration(&target)?;
                    match d.kind {
                        Kind::Relation => {
                            let kind = if d.input { "input" } else { "relation" };
                            self.signature(uri, &target).map_or_else(
                                || {
                                    format!(
                                        "{kind} {}\nSignature incomplete or damaged.",
                                        d.name.spelling()
                                    )
                                },
                                |(label, _)| format!("{kind} {label}"),
                            )
                        }
                        Kind::Constant => {
                            let label = self
                                .constant_sort(uri, &target)
                                .map(|s| self.sort_label(uri, &r.scope, s))
                                .unwrap_or_else(|| "unknown sort".into());
                            format!("const {}: {label}", d.name.spelling())
                        }
                        _ => format!("{} {}", d.kind.label(), d.name.spelling()),
                    }
                }
            };
            Some(json!({"contents":{"kind":"plaintext","value":text},"range":range(doc,&r.span)}))
        })();
        result.unwrap_or(Value::Null)
    }
    pub fn diagnostics(&self, uri: &Url, doc: &Document) -> Vec<Diagnostic> {
        let _timer = crate::timing::interval("diagnostics");
        let _query = crate::timing::interval("query");
        let Some(root) = self.root(uri) else {
            return vec![];
        };
        self.core
            .diagnostics(root, uri.as_str())
            .into_iter()
            .map(|d| Diagnostic {
                range: range(doc, &d.span),
                severity: Some(if d.warning {
                    DiagnosticSeverity::WARNING
                } else {
                    DiagnosticSeverity::ERROR
                }),
                source: Some("denotate".into()),
                code: Some(NumberOrString::String(d.code)),
                message: d.message,
                ..Default::default()
            })
            .collect()
    }
    pub fn definition(
        &self,
        uri: &Url,
        doc: &Document,
        position: Position,
        documents: &HashMap<Url, Document>,
    ) -> Value {
        let result = (|| {
            let b = doc.offset(position)?;
            let r = self
                .reference_at(uri, b)
                .or_else(|| self.reference_at(uri, b.saturating_sub(1)))?;
            if let Some(name) = self.namespace_name(uri, r) {
                let matches =
                    self.candidates(uri, &r.scope, &Lookup::Name(Kind::Namespace), Some(&name));
                return Some(json!(matches.into_iter().filter_map(|s| {
                    let target=Target { uri:Url::parse(&s.uri).ok()?,rule:None,id:s.id };
                    let target_doc=documents.get(&target.uri)?;
                    let span=self.target_span(&target)?;
                    Some(json!({"targetUri":target.uri,"targetRange":range(target_doc,span),"targetSelectionRange":range(target_doc,span),"originSelectionRange":range(doc,&r.span)}))
                }).collect::<Vec<_>>()));
            }
            let target = self.target(uri, r)?;
            let target_doc = documents.get(&target.uri)?;
            let span = self.target_span(&target)?;
            Some(
                json!([{"targetUri":target.uri,"targetRange":range(target_doc,span),"targetSelectionRange":range(target_doc,span),"originSelectionRange":range(doc,&r.span)}]),
            )
        })();
        result.unwrap_or_else(|| json!([]))
    }
    pub fn completion(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let result = (|| {
            let byte = doc.offset(position)?;
            let file = self.files.get(uri)?;
            let (lookup, scope, span) = file.completion_context(byte)?;
            let prefix = &doc.text[span.start..byte];
            // Preserve explicit qualification in replacement text. A qualified
            // reference is an absolute namespace path in the text format.
            let qualified = file
                .reference_at(span.start)
                .and_then(|r| r.name.namespace.clone());
            let mut values = self.candidates(uri, &scope, &lookup, None);
            if let Some(ns) = &qualified {
                values = self.core.candidates(
                    self.root(uri)?,
                    uri.as_str(),
                    &Scope {
                        namespace: ns.clone(),
                        imports: vec![],
                    },
                    &lookup,
                    None,
                );
                values.retain(|s| s.module.as_deref() == Some(&denotate_ir_text_namespace(ns)));
            }
            values.sort_by(|a, b| (&a.name, &a.uri, &a.id).cmp(&(&b.name, &b.uri, &b.id)));
            let mut items = values.into_iter().filter_map(|s| {
                let d = self.core.declaration(&s)?;
                let mut name = d.name.clone();
                name.namespace = qualified.clone();
                if qualified.is_none() && !matches!(lookup, Lookup::Name(Kind::Namespace | Kind::Alias) | Lookup::Parameter(_)) {
                    let matches = self.candidates(uri, &scope, &lookup, Some(&name));
                    if matches.len() != 1 || matches[0] != s { name.namespace = Some(d.scope.namespace.clone()); }
                }
                let spelling = if matches!(lookup, Lookup::Name(Kind::Namespace | Kind::Alias)) {
                    // Namespace keys already encode segment boundaries; aliases
                    // are grammar tokens, not quoted declaration identifiers.
                    s.name.clone()
                } else if matches!(lookup, Lookup::Constant(_)) && name.namespace.is_none()
                    && d.name.text.as_bytes().first().is_some_and(u8::is_ascii_uppercase) {
                    index::quoted(&d.name.text)
                } else { name.spelling() };
                if !spelling.starts_with(prefix) { return None; }
                let kind = match lookup { Lookup::Name(Kind::Namespace) => Kind::Namespace, _ => d.kind };
                Some(json!({"label": s.name, "detail": s.module,
                    "kind": match kind { Kind::Namespace => 9, Kind::Sort => 7, Kind::Relation => 3, Kind::Parameter => 5, _ => 21 },
                    "textEdit": {"range": range(doc, &span), "newText": spelling}}))
            }).collect::<Vec<_>>();
            if lookup == Lookup::Name(Kind::Relation) {
                for keyword in [
                    "use",
                    "sort",
                    "const",
                    "relation",
                    "input",
                    "namespace",
                    "domain",
                    "obligation",
                    "assumption",
                ] {
                    if keyword.starts_with(prefix) {
                        items.push(json!({"label":keyword,"kind":14,"textEdit":{"range":range(doc,&span),"newText":keyword}}));
                    }
                }
            }
            Some(json!({"isIncomplete":false,"items":items}))
        })();
        result.unwrap_or_else(|| json!({"isIncomplete":false,"items":[]}))
    }
    pub fn semantic_tokens(&self, uri: &Url, doc: &Document) -> Value {
        let Some(file) = self.files.get(uri) else {
            return json!({"data":[]});
        };
        let mut items = file
            .references
            .iter()
            .filter_map(|r| {
                let kind = match &r.lookup {
                    Lookup::Name(k) => *k,
                    Lookup::Constant(_) => Kind::Constant,
                    Lookup::Variable { .. } => return Some((r.span.clone(), 1, 0)),
                    Lookup::Parameter(_) => Kind::Parameter,
                    Lookup::Declaration(id) => file.declarations.get(id)?.kind,
                    _ => return None,
                };
                let token = match kind {
                    Kind::Namespace => 3,
                    Kind::Sort => 0,
                    Kind::Relation => 2,
                    Kind::Parameter => 4,
                    Kind::Constant => 1,
                    _ => return None,
                };
                Some((r.span.clone(), token, u32::from(kind == Kind::Constant)))
            })
            .collect::<Vec<_>>();
        let tokens = file
            .tokens
            .iter()
            .filter(|t| !t.comment)
            .collect::<Vec<_>>();
        for pair in tokens.windows(2) {
            if pair[0].text == ":"
                && pair[1]
                    .text
                    .bytes()
                    .next()
                    .is_some_and(|b| b.is_ascii_alphabetic())
                && !items.iter().any(|(span, _, _)| *span == pair[1].span)
            {
                items.push((pair[1].span.clone(), 0, 0));
            }
        }
        items.sort_by_key(|(span, _, _)| span.start);
        let mut data = vec![];
        let mut previous = Position::new(0, 0);
        for (span, kind, modifiers) in items {
            let at = doc.position(span.start);
            let end = doc.position(span.end);
            if end.line != at.line {
                continue;
            }
            data.extend([
                at.line - previous.line,
                if at.line == previous.line {
                    at.character - previous.character
                } else {
                    at.character
                },
                end.character - at.character,
                kind,
                modifiers,
            ]);
            previous = at;
        }
        json!({"data":data})
    }
    pub fn stats(&self) -> Value {
        let c = self.core.query_counts();
        json!({"backend":"rust","frontend":"tree-sitter","projections":self.core.projections(),"relationQueryExecutions":c[0],"sortQueryExecutions":c[1],"constantCandidateQueryExecutions":c[2],"constantQueryExecutions":c[6],"moduleQueryExecutions":c[3],"ruleQueryExecutions":c[4],"expectedSortQueryExecutions":c[5],"declarationQueryExecutions":c[7]})
    }
}
fn range(doc: &Document, span: &ByteRange<usize>) -> Range {
    Range::new(doc.position(span.start), doc.position(span.end))
}
fn denotate_ir_text_namespace(ns: &denotate_ir::Namespace) -> String {
    ns.segments()
        .iter()
        .map(|s| index::quote(s))
        .collect::<Vec<_>>()
        .join("::")
}
