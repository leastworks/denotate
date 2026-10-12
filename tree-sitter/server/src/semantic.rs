//! Editor answers from the shared core; only source mapping/presentation live here.
use crate::{
    projection::{Lookup, Projection},
    syntax::Document,
};
use denotate_analysis::{Analysis, NameKind, Symbol};
use lsp_types::{Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range, Url};
use serde_json::{json, Value};
use std::collections::HashMap;

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

    fn candidates(&self, uri: &Url, lookup: &Lookup, name: Option<&str>) -> Vec<Symbol> {
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
        let items: Vec<_> = candidates.into_iter().filter(|s| s.name.starts_with(prefix)).map(|s| json!({
            "label": s.name, "detail": s.module, "kind": match lookup { Lookup::Module => 9, Lookup::Sort => 7, Lookup::Relation => 3, _ => 21 },
            "textEdit": {"range": Range::new(doc.position(span.start), doc.position(span.end)), "newText": s.name}
        })).collect();
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
