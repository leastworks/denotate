//! Tree-sitter syntax -> shared semantic inputs. Source anchors never enter Salsa.
use crate::syntax::Document;
use denotate_analysis::{
    Constant, Document as Input, NamedDeclaration, Role, RuleAtom, RuleSyntax, Signature,
};
use lsp_types::Url;
use std::{collections::HashMap, ops::Range, sync::Arc};
use tree_sitter::Node;

#[derive(Clone, Debug)]
pub enum Lookup {
    Module,
    Sort,
    Relation,
    Constant { relation: String, index: usize },
    Variable { rule: Arc<str>, occurrence: String },
    Anonymous { relation: String, index: usize },
    Parameter,
    Declaration(String),
}

pub struct DeclarationInfo {
    pub kind: String,
    pub name: String,
    pub parameters: Option<Vec<(String, Option<String>)>>,
}

#[derive(Clone, Debug)]
pub struct Reference {
    pub name: String,
    pub span: Range<usize>,
    pub lookup: Lookup,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub text: String,
    pub span: Range<usize>,
    pub comment: bool,
}

pub struct Projection {
    pub input: Input,
    pub anchors: HashMap<String, Range<usize>>,
    pub rule_anchors: HashMap<String, HashMap<String, Range<usize>>>,
    pub references: Vec<Reference>,
    pub declarations: HashMap<String, DeclarationInfo>,
    pub tokens: Vec<Token>,
    counts: HashMap<String, usize>,
}

fn text<'a>(doc: &'a Document, node: Node<'_>) -> &'a str {
    &doc.text[node.byte_range()]
}

fn field<'a>(node: Node<'a>, name: &str) -> Option<Node<'a>> {
    node.child_by_field_name(name)
        .filter(|n| !n.is_missing() && !n.is_error())
}

pub fn tokens(doc: &Document, node: Node<'_>, out: &mut Vec<Token>) {
    if node.is_missing() {
        return;
    }
    if node.child_count() == 0 {
        if node.start_byte() != node.end_byte() {
            out.push(Token {
                text: text(doc, node).into(),
                span: node.byte_range(),
                comment: node.kind() == "comment",
            });
        }
    } else {
        for child in node.children(&mut node.walk()) {
            tokens(doc, child, out);
        }
    }
}

impl Projection {
    pub fn new(doc: &Document, uri: &Url) -> Self {
        let path = uri.to_file_path().ok();
        let mut result = Self {
            input: Input {
                uri: uri.to_string(),
                directory: path
                    .as_ref()
                    .and_then(|p| p.parent())
                    .map(|p| p.to_string_lossy().into_owned())
                    .unwrap_or_default(),
                filename: path
                    .as_ref()
                    .and_then(|p| p.file_name())
                    .map(|p| p.to_string_lossy().into_owned())
                    .unwrap_or_default(),
                module: None,
                imports: vec![],
                relations: vec![],
                sorts: vec![],
                signatures: vec![],
                constants: vec![],
                input_relations: vec![],
                rules: vec![],
            },
            anchors: HashMap::new(),
            rule_anchors: HashMap::new(),
            references: vec![],
            declarations: HashMap::new(),
            tokens: vec![],
            counts: HashMap::new(),
        };
        tokens(doc, doc.tree.root_node(), &mut result.tokens);
        result.declarations(doc, doc.tree.root_node());
        // Source order is for presentation, not visibility. Canonical order avoids
        // invalidating every client when independent declarations are reordered.
        result.input.relations.sort_by(|a, b| a.id.cmp(&b.id));
        result.input.sorts.sort_by(|a, b| a.id.cmp(&b.id));
        result.input.constants.sort_by(|a, b| a.id.cmp(&b.id));
        result.input.signatures.sort_by(|a, b| a.id.cmp(&b.id));
        result.input.input_relations.sort();
        result.input.imports.sort();
        result.input.rules.sort_by(|a, b| a.id.cmp(&b.id));
        result
    }

    fn identity(&mut self, key: String) -> String {
        let count = self.counts.entry(key.clone()).or_default();
        let id = format!("{key}#{count}");
        *count += 1;
        id
    }

    fn reference(&mut self, doc: &Document, node: Node<'_>, lookup: Lookup) {
        if !node.is_missing() && !node.is_error() {
            self.references.push(Reference {
                name: text(doc, node).into(),
                span: node.byte_range(),
                lookup,
            });
        }
    }

    fn declaration(&mut self, doc: &Document, node: Node<'_>, key: String) -> NamedDeclaration {
        let id = self.identity(key);
        self.anchors.insert(id.clone(), node.byte_range());
        self.declarations.insert(
            id.clone(),
            DeclarationInfo {
                kind: node.parent().map_or("", |n| n.kind()).into(),
                name: text(doc, node).into(),
                parameters: None,
            },
        );
        self.reference(doc, node, Lookup::Declaration(id.clone()));
        NamedDeclaration {
            id,
            name: text(doc, node).into(),
        }
    }

    fn declarations(&mut self, doc: &Document, parent: Node<'_>) {
        for node in parent.named_children(&mut parent.walk()) {
            let name = field(node, "name");
            match node.kind() {
                "ERROR" => self.declarations(doc, node),
                "module" => {
                    if let Some(name) = name {
                        self.input.module = Some(text(doc, name).into());
                        self.anchors.insert(String::new(), name.byte_range());
                        self.declarations.insert(
                            String::new(),
                            DeclarationInfo {
                                kind: "module".into(),
                                name: text(doc, name).into(),
                                parameters: None,
                            },
                        );
                        self.reference(doc, name, Lookup::Declaration(String::new()));
                    }
                }
                "import" => {
                    self.input.imports.push(name.map(|n| text(doc, n).into()));
                    if let Some(name) = name {
                        self.reference(doc, name, Lookup::Module);
                    }
                }
                "sort" => {
                    if let Some(name) = name {
                        let decl = self.declaration(doc, name, format!("sort:{}", text(doc, name)));
                        self.input.sorts.push(decl);
                    }
                }
                "relation" => {
                    if let Some(name) = name {
                        let decl =
                            self.declaration(doc, name, format!("relation:{}", text(doc, name)));
                        let mut parameters = vec![];
                        let mut labels = vec![];
                        for param in node
                            .named_children(&mut node.walk())
                            .filter(|n| n.kind() == "parameter")
                        {
                            let sort = field(param, "sort");
                            let parameter_name = field(param, "name");
                            labels.push((
                                parameter_name.map_or("?", |n| text(doc, n)).into(),
                                sort.map(|s| text(doc, s).into()),
                            ));
                            if let Some(name) = parameter_name {
                                self.reference(doc, name, Lookup::Parameter);
                            }
                            parameters.push(sort.map(|s| text(doc, s).into()));
                            if let Some(sort) = sort {
                                self.reference(doc, sort, Lookup::Sort);
                            }
                        }
                        // Never infer arity from a recovered/truncated signature.
                        self.input.signatures.push(Signature {
                            id: decl.id.clone(),
                            parameters: (!node.has_error()).then_some(parameters),
                        });
                        self.declarations.insert(
                            decl.id.clone(),
                            DeclarationInfo {
                                kind: field(node, "kind")
                                    .map_or("relation", |n| text(doc, n))
                                    .into(),
                                name: decl.name.clone(),
                                parameters: (!node.has_error()).then_some(labels),
                            },
                        );
                        if field(node, "kind").is_some_and(|n| text(doc, n) == "input") {
                            self.input.input_relations.push(decl.id.clone());
                        }
                        self.input.relations.push(decl);
                    }
                }
                "constants" => {
                    let sort = field(node, "sort");
                    if let Some(sort) = sort {
                        self.reference(doc, sort, Lookup::Sort);
                    }
                    for name in node.children_by_field_name("name", &mut node.walk()) {
                        if name.is_missing() || reserved(text(doc, name)) {
                            continue;
                        }
                        let sort_name = sort.map(|s| text(doc, s).to_owned());
                        let decl = self.declaration(
                            doc,
                            name,
                            format!("constant:{}:{sort_name:?}", text(doc, name)),
                        );
                        self.input.constants.push(Constant {
                            id: decl.id,
                            name: decl.name,
                            sort: sort_name,
                        });
                    }
                }
                "statement" => self.rule(doc, node),
                _ => {}
            }
        }
    }

    fn rule(&mut self, doc: &Document, node: Node<'_>) {
        // Collision-free token serialization, not byte offsets or parser node IDs.
        // Duplicate identical rules have an occurrence suffix; no promise to track
        // which indistinguishable duplicate moved. Editing a body replaces its ID.
        let mut leaves = vec![];
        tokens(doc, node, &mut leaves);
        // Reserved constants are lexical errors reported outside Tree-sitter's
        // recovery nodes. They invalidate binding/lint evidence for this rule too.
        let complete = !node.has_error()
            && !leaves
                .iter()
                .any(|token| !token.comment && reserved(&token.text));
        let key = serde_json::to_string(
            &leaves
                .iter()
                .filter(|t| !t.comment)
                .map(|t| &t.text)
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let id = self.identity(format!("rule:{key}"));
        let reference_id: Arc<str> = id.clone().into();
        let mut anchors = HashMap::new();
        let mut atoms = vec![];
        for child in node.named_children(&mut node.walk()) {
            let (atom, role) = match child.kind() {
                "atom" => (child, Role::Head),
                "positive_atom" => (child, Role::Positive),
                "negative_atom" => {
                    let Some(atom) = child
                        .named_children(&mut child.walk())
                        .find(|n| n.kind() == "atom")
                    else {
                        continue;
                    };
                    (atom, Role::Negative)
                }
                _ => continue,
            };
            let Some(name) = field(atom, "name") else {
                continue;
            };
            let relation = text(doc, name).to_owned();
            let atom_id = format!("atom{}", atoms.len());
            anchors.insert(atom_id.clone(), name.byte_range());
            self.reference(doc, name, Lookup::Relation);
            let mut variables = vec![];
            for term in atom
                .named_children(&mut atom.walk())
                .filter(|n| matches!(n.kind(), "constant" | "variable" | "anonymous"))
            {
                let index = variables.len();
                let term_id = format!("{atom_id}/arg{index}");
                let variable = if term.kind() == "variable" && !term.is_missing() {
                    anchors.insert(term_id.clone(), term.byte_range());
                    self.reference(
                        doc,
                        term,
                        Lookup::Variable {
                            rule: reference_id.clone(),
                            occurrence: term_id.clone(),
                        },
                    );
                    Some(NamedDeclaration {
                        id: term_id,
                        name: text(doc, term).into(),
                    })
                } else {
                    if term.kind() == "anonymous" {
                        self.reference(
                            doc,
                            term,
                            Lookup::Anonymous {
                                relation: relation.clone(),
                                index,
                            },
                        );
                    }
                    if term.kind() == "constant" && !reserved(text(doc, term)) {
                        self.reference(
                            doc,
                            term,
                            Lookup::Constant {
                                relation: relation.clone(),
                                index,
                            },
                        );
                    }
                    None
                };
                variables.push(variable);
            }
            atoms.push(RuleAtom {
                id: atom_id,
                relation,
                role,
                variables,
            });
        }
        self.rule_anchors.insert(id.clone(), anchors);
        self.input.rules.push(RuleSyntax {
            id,
            complete,
            atoms,
        });
    }

    /// Cursor context from current CST tokens, even when no argument AST exists.
    /// No regex reparsing of comments, and no previous-good document fallback.
    pub fn completion_context(&self, byte: usize) -> Option<(Lookup, Range<usize>)> {
        if self
            .tokens
            .iter()
            .any(|t| t.comment && t.span.start <= byte && byte <= t.span.end)
        {
            return None;
        }
        let current = self.tokens.iter().find(|t| {
            t.span.start <= byte
                && byte <= t.span.end
                && t.text
                    .bytes()
                    .all(|c| c.is_ascii_alphanumeric() || c == b'_')
        });
        let start = current.map_or(byte, |t| t.span.start);
        let replacement = current.map_or(byte..byte, |t| t.span.clone());
        let before: Vec<_> = self
            .tokens
            .iter()
            .filter(|t| !t.comment && t.span.end <= start)
            .collect();
        let boundary = before
            .iter()
            .rposition(|t| t.text == ";")
            .map_or(0, |i| i + 1);
        let statement = &before[boundary..];
        if statement.first().is_some_and(|t| t.text == "use") {
            return Some((Lookup::Module, replacement));
        }
        let declaration = statement.first().is_some_and(|t| {
            matches!(
                t.text.as_str(),
                "relation" | "input" | "const" | "module" | "sort"
            )
        });
        if declaration {
            return statement
                .last()
                .filter(|t| t.text == ":")
                .map(|_| (Lookup::Sort, replacement));
        }
        // Flat atoms: the last unclosed '(' determines relation and argument.
        if let Some(open) = statement.iter().rposition(|t| t.text == "(") {
            if open > 0 && !statement[open + 1..].iter().any(|t| t.text == ")") {
                let index = statement[open + 1..]
                    .iter()
                    .filter(|t| t.text == ",")
                    .count();
                return Some((
                    Lookup::Constant {
                        relation: statement[open - 1].text.clone(),
                        index,
                    },
                    replacement,
                ));
            }
        }
        Some((Lookup::Relation, replacement))
    }
}

pub fn reserved(name: &str) -> bool {
    denotate_ir_text::reserved_word(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn project(source: &str) -> Projection {
        let doc = Document::new(&mut crate::syntax::parser(), source.into(), 1, true);
        Projection::new(&doc, &Url::parse("file:///work/example.den").unwrap())
    }

    #[test]
    fn identities_ignore_trivia_and_order_but_keep_duplicate_occurrences() {
        let a = project(
            "module example; sort S; relation r(x: S); r(X) :- r(X); r(Y) :- r(Y); r(X) :- r(X);",
        );
        let b = project("// 🦀\nmodule example;\nr(Y) :- r(Y);\nrelation r(x: S); sort S; r(X) :- // comment\n r(X); r(X) :- r(X);");
        assert_eq!(a.input, b.input);
        assert_eq!(a.input.rules.len(), 3);
        let ids: std::collections::HashSet<_> = a.input.rules.iter().map(|r| &r.id).collect();
        assert_eq!(ids.len(), 3, "duplicates must not overwrite source anchors");
        assert_ne!(a.anchors, b.anchors, "current ranges must be refreshed");
        let c = project("module example; const extra: S; sort S; relation r(x: S); r(X) :- r(X); r(Y) :- r(Y); r(X) :- r(X);");
        assert_eq!(a.input.rules, c.input.rules);
        assert_eq!(a.input.relations, c.input.relations);
    }

    #[test]
    fn reserved_constants_suppress_rule_lints_without_disabling_neighbours() {
        let uri = Url::parse("file:///work/example.den").unwrap();
        let mut semantics = crate::semantic::Semantics::default();
        for word in ["module", "use", "sort", "const", "relation", "input"] {
            let source = format!("module example; sort S; const a: S; relation r(x: S);\nr(X) :- r({word});\nr(Y) :- r(a);\n");
            let doc = Document::new(&mut crate::syntax::parser(), source, 1, true);
            assert!(
                !doc.tree.root_node().has_error(),
                "exercise the lexical-check-only case"
            );
            assert_eq!(doc.diagnostics().len(), 1);
            semantics.update(&uri, &doc);
            let diagnostics = semantics.diagnostics(&uri, &doc);
            assert!(
                diagnostics.iter().all(|d| d.range.start.line != 1),
                "{word}: {diagnostics:?}"
            );
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.range.start.line == 2 && d.message.contains("Y")),
                "valid neighbouring rule must still be checked"
            );

            let repaired = doc.text.replace(&format!("r({word})"), "r(a)");
            let doc = Document::new(&mut crate::syntax::parser(), repaired, 2, true);
            semantics.update(&uri, &doc);
            assert!(doc.diagnostics().is_empty());
            assert!(
                semantics
                    .diagnostics(&uri, &doc)
                    .iter()
                    .any(|d| d.range.start.line == 1 && d.message.contains("X")),
                "repair must restore binding checks"
            );
        }
    }

    #[test]
    fn long_rules_have_short_scoped_child_ids_and_shared_parent_keys() {
        let body = (0..100).map(|_| "r(X)").collect::<Vec<_>>().join(", ");
        let source =
            format!("module example; sort S; relation r(x: S); r(X) :- {body}; r(X) :- r(X);");
        let projection = project(&source);
        assert_eq!(projection.rule_anchors.len(), 2);
        for rule in &projection.input.rules {
            let anchors = &projection.rule_anchors[&rule.id];
            assert_eq!(anchors.len(), rule.atoms.len() * 2);
            let mut shared = None;
            for reference in &projection.references {
                if let Lookup::Variable {
                    rule: parent,
                    occurrence,
                } = &reference.lookup
                {
                    if parent.as_ref() != rule.id {
                        continue;
                    }
                    if let Some(previous) = shared {
                        assert!(Arc::ptr_eq(previous, parent));
                    }
                    shared = Some(parent);
                    assert_eq!(anchors[occurrence], reference.span);
                }
            }
            for (index, atom) in rule.atoms.iter().enumerate() {
                assert_eq!(atom.id, format!("atom{index}"));
                let variable = atom.variables[0].as_ref().unwrap();
                assert_eq!(variable.id, format!("atom{index}/arg0"));
                assert!(variable.id.len() < 32);
            }
        }
        let first = &projection.input.rules[0].id;
        let second = &projection.input.rules[1].id;
        assert_ne!(
            projection.rule_anchors[first]["atom0/arg0"],
            projection.rule_anchors[second]["atom0/arg0"],
            "same local IDs must retain separate source positions"
        );
    }

    #[test]
    fn damaged_signatures_keep_names_but_never_invent_parameter_counts() {
        for signature in [
            "relation r(x: S, y: );",
            "relation r(x: S,);",
            "relation r(x: S, y);",
        ] {
            let projection = project(&format!(
                "module example; sort S; {signature} relation good(x: S);"
            ));
            let r = projection
                .input
                .relations
                .iter()
                .find(|r| r.name == "r")
                .expect(signature);
            assert_eq!(
                projection
                    .input
                    .signatures
                    .iter()
                    .find(|s| s.id == r.id)
                    .unwrap()
                    .parameters,
                None,
                "{signature}"
            );
            let good = projection
                .input
                .relations
                .iter()
                .find(|r| r.name == "good")
                .unwrap();
            assert_eq!(
                projection
                    .input
                    .signatures
                    .iter()
                    .find(|s| s.id == good.id)
                    .unwrap()
                    .parameters,
                Some(vec![Some("S".into())])
            );
        }
    }

    #[test]
    fn incomplete_completion_uses_tokens_and_ignores_comment_punctuation() {
        for suffix in ["r(a,", "r(a, // , fake(\n", "r(a, b"] {
            let source = format!("module example; {suffix}");
            let projection = project(&source);
            assert!(
                matches!(projection.completion_context(source.len()), Some((Lookup::Constant { relation, index: 1 }, _)) if relation == "r"),
                "{suffix}"
            );
        }
        let source = "module example; relation r(x: Sl";
        assert!(matches!(
            project(source).completion_context(source.len()),
            Some((Lookup::Sort, _))
        ));
        let source = "module example; // r(a,";
        assert!(project(source).completion_context(source.len()).is_none());
    }
}
