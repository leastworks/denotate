//! Editor answers from the shared core; only source mapping/presentation live here.
use crate::{
    projection::{Lookup, Projection, Reference},
    syntax::Document,
};
use denotate_analysis::{Analysis, NameKind, Symbol};
use lsp_types::{Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range, Url};
use serde_json::{json, Value};
use std::{collections::HashMap, ops::Range as ByteRange, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Target {
    pub uri: Url,
    pub rule: Option<Arc<str>>,
    pub id: String,
}

#[derive(Default)]
pub struct Semantics {
    pub core: Analysis,
    pub files: HashMap<Url, Projection>,
    projections: u64,
}

impl Semantics {
    pub fn update(&mut self, uri: &Url, doc: &Document) {
        let projection = Projection::new(doc, uri);
        self.core.update(projection.input.clone());
        self.files.insert(uri.clone(), projection);
        self.projections += 1;
    }

    pub fn remove(&mut self, uri: &Url) {
        self.core.remove(uri.as_str());
        self.files.remove(uri);
    }

    pub(crate) fn candidates(&self, uri: &Url, lookup: &Lookup, name: Option<&str>) -> Vec<Symbol> {
        let symbols = match lookup {
            Lookup::Module => self.core.module_candidates(uri.as_str()),
            Lookup::Sort => self.core.visible_sorts(uri.as_str()),
            Lookup::Relation => self.core.visible_relations(uri.as_str()),
            Lookup::Constant { relation, index } => {
                return self
                    .core
                    .constant_candidates(uri.as_str(), relation.clone(), *index, name)
            }
            _ => return vec![],
        };
        symbols
            .into_iter()
            .filter(|s| name.is_none_or(|name| s.name == name))
            .collect()
    }

    pub fn reference_at(&self, uri: &Url, byte: usize) -> Option<&Reference> {
        self.files
            .get(uri)?
            .references
            .iter()
            .find(|r| r.span.start <= byte && byte < r.span.end)
    }

    pub fn target(&self, uri: &Url, reference: &Reference) -> Option<Target> {
        match &reference.lookup {
            Lookup::Declaration(id) => Some(Target {
                uri: uri.clone(),
                rule: None,
                id: id.clone(),
            }),
            Lookup::Variable { rule, occurrence } => self
                .core
                .rule_analysis(uri.as_str(), rule)
                .variables
                .iter()
                .find(|v| v.occurrences.contains(occurrence))
                .and_then(|v| v.occurrences.first())
                .map(|id| Target {
                    uri: uri.clone(),
                    rule: Some(rule.clone()),
                    id: id.clone(),
                }),
            lookup => match self
                .candidates(uri, lookup, Some(&reference.name))
                .as_slice()
            {
                [symbol] => Some(Target {
                    uri: Url::parse(&symbol.uri).ok()?,
                    rule: None,
                    id: symbol.id.clone(),
                }),
                _ => None,
            },
        }
    }

    pub fn target_span(&self, target: &Target) -> Option<&ByteRange<usize>> {
        let file = self.files.get(&target.uri)?;
        match &target.rule {
            Some(rule) => file.rule_anchors.get(rule.as_ref())?.get(&target.id),
            None => file.anchors.get(&target.id),
        }
    }

    pub fn occurrences(
        &self,
        target: &Target,
        include_declaration: bool,
    ) -> Vec<(Url, ByteRange<usize>)> {
        let mut result = vec![];
        for (uri, file) in &self.files {
            if target.rule.is_some() && uri != &target.uri {
                continue;
            }
            for reference in &file.references {
                if self.target(uri, reference).as_ref() == Some(target) {
                    let declaration =
                        uri == &target.uri && self.target_span(target) == Some(&reference.span);
                    if include_declaration || !declaration {
                        result.push((uri.clone(), reference.span.clone()));
                    }
                }
            }
        }
        result.sort_by(|a, b| (&a.0, a.1.start).cmp(&(&b.0, b.1.start)));
        result
    }

    pub fn references(
        &self,
        uri: &Url,
        doc: &Document,
        position: Position,
        include_declaration: bool,
        documents: &HashMap<Url, Document>,
    ) -> Value {
        let target = doc
            .offset(position)
            .and_then(|byte| self.reference_at(uri, byte))
            .and_then(|r| self.target(uri, r));
        let Some(target) = target else {
            return json!([]);
        };
        json!(self.occurrences(&target, include_declaration).into_iter().filter_map(|(uri, span)| {
            let doc = documents.get(&uri)?;
            Some(json!({"uri": uri, "range": Range::new(doc.position(span.start), doc.position(span.end))}))
        }).collect::<Vec<_>>())
    }

    fn signature(&self, target: &Target) -> Option<(String, Vec<String>)> {
        let info = self.files.get(&target.uri)?.declarations.get(&target.id)?;
        let parameters = info.parameters.as_ref()?;
        let labels: Vec<_> = parameters
            .iter()
            .map(|(name, sort)| {
                let label = sort
                    .as_ref()
                    .and_then(|s| self.core.resolve_sort(target.uri.as_str(), s.clone()))
                    .map(|s| s.name)
                    .unwrap_or_else(|| format!("{} (unresolved)", sort.as_deref().unwrap_or("?")));
                format!("{name}: {label}")
            })
            .collect();
        Some((format!("{}({})", info.name, labels.join(", ")), labels))
    }

    pub fn signature_help(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let result = (|| {
            let byte = doc.offset(position)?;
            let (Lookup::Constant { relation, index }, _) =
                self.files.get(uri)?.completion_context(byte)?
            else {
                return None;
            };
            let symbols = self.core.visible_relations(uri.as_str());
            let matches: Vec<_> = symbols.iter().filter(|s| s.name == relation).collect();
            let [symbol] = matches.as_slice() else {
                return None;
            };
            let target = Target {
                uri: Url::parse(&symbol.uri).ok()?,
                rule: None,
                id: symbol.id.clone(),
            };
            let (label, parameters) = self.signature(&target)?;
            Some(
                json!({"signatures": [{"label": label, "parameters": parameters.iter().map(|label| json!({"label": label})).collect::<Vec<_>>()}],
                "activeSignature": 0, "activeParameter": (index < parameters.len()).then_some(index)}),
            )
        })();
        result.unwrap_or(Value::Null)
    }

    pub fn hover(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let result = (|| {
            let reference = self.reference_at(uri, doc.offset(position)?)?;
            let description = match &reference.lookup {
                Lookup::Anonymous { relation, index } => {
                    let sort = self
                        .core
                        .expected_sort(uri.as_str(), relation.clone(), *index);
                    format!(
                        "_: {}\n\nAnonymous argument; each _ is independent.",
                        sort.as_ref().map_or("unknown sort", |s| s.name.as_str())
                    )
                }
                Lookup::Variable { rule, occurrence } => {
                    let analysis = self.core.rule_analysis(uri.as_str(), rule);
                    let variable = analysis
                        .variables
                        .iter()
                        .find(|v| v.occurrences.contains(occurrence))?;
                    if variable.sorts.len() > 1 {
                        let mut sorts: Vec<_> = variable
                            .sorts
                            .iter()
                            .map(|s| format!("{}.{}", s.module.as_deref().unwrap_or("?"), s.name))
                            .collect();
                        sorts.sort();
                        format!(
                            "variable {}\nConflicting expected sorts: {}",
                            variable.name,
                            sorts.join(", ")
                        )
                    } else {
                        format!(
                            "variable {}: {}{}",
                            variable.name,
                            variable
                                .sorts
                                .first()
                                .map_or("unknown sort", |s| s.name.as_str()),
                            if !variable.sorts.is_empty() && variable.unknown {
                                "\nSome occurrences have unknown argument sorts."
                            } else {
                                ""
                            }
                        )
                    }
                }
                _ => {
                    let target = self.target(uri, reference)?;
                    let file = self.files.get(&target.uri)?;
                    let info = file.declarations.get(&target.id)?;
                    match info.kind.as_str() {
                        "module" | "sort" => format!("{} {}", info.kind, info.name),
                        "relation" | "input" => match self.signature(&target) {
                            Some((label, _)) => format!("{} {label}", info.kind),
                            None => format!(
                                "{} {}\nSignature incomplete or damaged.",
                                info.kind, info.name
                            ),
                        },
                        "constants" => {
                            let sort = file
                                .input
                                .constants
                                .iter()
                                .find(|c| c.id == target.id)?
                                .sort
                                .as_ref()
                                .and_then(|name| {
                                    self.core.resolve_sort(target.uri.as_str(), name.clone())
                                });
                            let label = sort
                                .and_then(|s| self.core.sort_label(uri.as_str(), &s.uri, s.id))
                                .unwrap_or_else(|| "unknown sort".into());
                            format!("const {}: {label}", info.name)
                        }
                        _ => return None,
                    }
                }
            };
            Some(
                json!({"contents": {"kind": "plaintext", "value": description},
                "range": Range::new(doc.position(reference.span.start), doc.position(reference.span.end))}),
            )
        })();
        result.unwrap_or(Value::Null)
    }

    pub fn semantic_tokens(&self, uri: &Url, doc: &Document) -> Value {
        let Some(file) = self.files.get(uri) else {
            return json!({"data": []});
        };
        let mut items: Vec<(ByteRange<usize>, u32, u32)> = file
            .references
            .iter()
            .filter_map(|r| {
                let (kind, modifiers) = match &r.lookup {
                    Lookup::Module => (3, 0),
                    Lookup::Sort => (0, 0),
                    Lookup::Relation => (2, 0),
                    Lookup::Constant { .. } => (1, 1),
                    Lookup::Variable { .. } => (1, 0),
                    Lookup::Parameter => (4, 0),
                    Lookup::Declaration(id) => match file.declarations.get(id)?.kind.as_str() {
                        "module" => (3, 0),
                        "sort" => (0, 0),
                        "relation" | "input" => (2, 0),
                        "constants" => (1, 1),
                        _ => return None,
                    },
                    _ => return None,
                };
                Some((r.span.clone(), kind, modifiers))
            })
            .collect();
        // Recovery may retain only leaf tokens. A ':' still establishes a sort
        // position; uppercase alone is never evidence that a token is a variable.
        let tokens: Vec<_> = file.tokens.iter().filter(|t| !t.comment).collect();
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
        json!({"data": data})
    }

    pub fn diagnostics(&self, uri: &Url, doc: &Document) -> Vec<Diagnostic> {
        let Some(file) = self.files.get(uri) else {
            return vec![];
        };
        let mut result = vec![];
        let mut add =
            |span: &std::ops::Range<usize>, code: &str, message: String, warning: bool| {
                result.push(Diagnostic {
                    range: Range::new(doc.position(span.start), doc.position(span.end)),
                    severity: Some(if warning {
                        DiagnosticSeverity::WARNING
                    } else {
                        DiagnosticSeverity::ERROR
                    }),
                    source: Some("denotate".into()),
                    code: Some(NumberOrString::String(code.into())),
                    message,
                    ..Diagnostic::default()
                });
            };
        for diagnostic in self.core.declaration_diagnostics(uri.as_str()) {
            if let Some(span) = file.anchors.get(&diagnostic.id) {
                add(span, &diagnostic.code, diagnostic.message, false);
            }
        }
        for reference in &file.references {
            let (kind, relation, index, label) = match &reference.lookup {
                Lookup::Module => (NameKind::Module, String::new(), 0, "module"),
                Lookup::Sort => (NameKind::Sort, String::new(), 0, "sort"),
                Lookup::Relation => (NameKind::Relation, String::new(), 0, "relation"),
                Lookup::Constant { relation, index } => {
                    (NameKind::Constant, relation.clone(), *index, "constant")
                }
                _ => continue,
            };
            let matches = self.candidates(uri, &reference.lookup, Some(&reference.name));
            if matches.len() == 1 {
                continue;
            }
            let message = self.core.name_diagnostic(
                uri.as_str(),
                kind,
                reference.name.clone(),
                relation.clone(),
                index,
            );
            if let Some(message) = message {
                add(&reference.span, "resolution", message, false);
            } else if matches.is_empty() && kind != NameKind::Constant {
                add(
                    &reference.span,
                    "resolution",
                    format!("Unknown {label} '{}'.", reference.name),
                    false,
                );
            }
        }
        for rule in &file.input.rules {
            for diagnostic in self.core.rule_analysis(uri.as_str(), &rule.id).diagnostics {
                if let Some(span) = file
                    .rule_anchors
                    .get(&rule.id)
                    .and_then(|anchors| anchors.get(&diagnostic.id))
                {
                    add(
                        span,
                        &diagnostic.code,
                        diagnostic.message,
                        diagnostic.warning,
                    );
                }
            }
        }
        result
    }

    pub fn definition(
        &self,
        uri: &Url,
        doc: &Document,
        position: Position,
        documents: &HashMap<Url, Document>,
    ) -> Value {
        let Some(byte) = doc.offset(position) else {
            return json!([]);
        };
        let Some(file) = self.files.get(uri) else {
            return json!([]);
        };
        let Some(reference) = file
            .references
            .iter()
            .find(|r| r.span.start <= byte && byte <= r.span.end)
        else {
            return json!([]);
        };
        let target = match &reference.lookup {
            Lookup::Declaration(id) => Some((uri.clone(), None, id.clone())),
            Lookup::Variable { rule, occurrence } => self
                .core
                .rule_analysis(uri.as_str(), rule)
                .variables
                .iter()
                .find(|v| v.occurrences.contains(occurrence))
                .and_then(|v| v.occurrences.first())
                .map(|id| (uri.clone(), Some(rule.as_ref()), id.clone())),
            lookup => {
                let candidates = self.candidates(uri, lookup, Some(&reference.name));
                match candidates.as_slice() {
                    [symbol] => Url::parse(&symbol.uri)
                        .ok()
                        .map(|uri| (uri, None, symbol.id.clone())),
                    _ => None, // Never choose an arbitrary ambiguous declaration.
                }
            }
        };
        let Some((target_uri, rule, id)) = target else {
            return json!([]);
        };
        let Some(target_file) = self.files.get(&target_uri) else {
            return json!([]);
        };
        let Some(target_doc) = documents.get(&target_uri) else {
            return json!([]);
        };
        let anchors = match rule {
            Some(rule) => target_file.rule_anchors.get(rule),
            None => Some(&target_file.anchors),
        };
        let Some(span) = anchors.and_then(|anchors| anchors.get(&id)) else {
            return json!([]);
        };
        let range = Range::new(
            target_doc.position(span.start),
            target_doc.position(span.end),
        );
        json!([{"targetUri": target_uri, "targetRange": range, "targetSelectionRange": range,
            "originSelectionRange": Range::new(doc.position(reference.span.start), doc.position(reference.span.end))}])
    }

    pub fn completion(&self, uri: &Url, doc: &Document, position: Position) -> Value {
        let Some(byte) = doc.offset(position) else {
            return json!({"isIncomplete": false, "items": []});
        };
        let Some(file) = self.files.get(uri) else {
            return json!({"isIncomplete": false, "items": []});
        };
        let Some((lookup, span)) = file.completion_context(byte) else {
            return json!({"isIncomplete": false, "items": []});
        };
        let prefix = &doc.text[span.start..byte];
        let mut candidates = self.candidates(uri, &lookup, None);
        candidates.sort_by(|a, b| (&a.name, &a.uri, &a.id).cmp(&(&b.name, &b.uri, &b.id)));
        let mut items: Vec<_> = candidates.into_iter().filter(|s| s.name.starts_with(prefix)).map(|s| json!({
            "label": s.name, "detail": s.module, "kind": match lookup { Lookup::Module => 9, Lookup::Sort => 7, Lookup::Relation => 3, _ => 21 },
            "textEdit": {"range": Range::new(doc.position(span.start), doc.position(span.end)), "newText": s.name}
        })).collect();
        if matches!(lookup, Lookup::Relation) {
            for keyword in ["use", "sort", "const", "relation", "input"] {
                if keyword.starts_with(prefix) {
                    items.push(json!({"label": keyword, "kind": 14, "textEdit": {"range": Range::new(doc.position(span.start), doc.position(span.end)), "newText": keyword}}));
                }
            }
        }
        json!({"isIncomplete": false, "items": items})
    }

    pub fn stats(&self) -> Value {
        let counts = serde_json::to_value(self.core.query_counts()).unwrap();
        json!({"backend": "rust", "frontend": "tree-sitter", "projections": self.projections,
            "relationQueryExecutions": counts["relations"], "sortQueryExecutions": counts["sorts"],
            "expectedSortQueryExecutions": counts["expectedSorts"], "constantQueryExecutions": counts["constants"],
            "ruleQueryExecutions": counts["rules"], "constantDiagnosticQueryExecutions": counts["constantDiagnostics"],
            "sortLabelQueryExecutions": counts["sortLabels"], "moduleQueryExecutions": counts["modules"],
            "declarationQueryExecutions": counts["declarations"], "nameDiagnosticQueryExecutions": counts["nameDiagnostics"]})
    }
}
