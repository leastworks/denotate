//! Tree-sitter recovery stays in the editor document. Only a syntax-clean tree
//! projects to a complete AST; skipping damaged mappings would change meaning.
use crate::ast::*;
use denotate_editor::Document;
use denotate_ir::{ProvenanceError, SnapshotId, SourceSpan, Sources};
use std::fmt;
use tree_sitter::{Node, Parser};
use tree_sitter_language::LanguageFn;

unsafe extern "C" {
    fn tree_sitter_inputmapping() -> *const ();
}

pub fn parser() -> Result<Parser, tree_sitter::LanguageError> {
    // This symbol is linked from the generated grammar compiled by build.rs.
    let language = unsafe { LanguageFn::from_raw(tree_sitter_inputmapping) };
    denotate_editor::parser(language.into())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxDiagnostic {
    pub span: SourceSpan,
    pub message: String,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseOutcome {
    Parsed(Program),
    SyntaxErrors(Vec<SyntaxDiagnostic>),
}

/// Integration/attribution failures belong to the DSL creator, not the author.
#[derive(Debug)]
pub enum ParseFailure {
    Provenance(ProvenanceError),
    SnapshotMismatch,
    UnexpectedTree(String),
}
impl fmt::Display for ParseFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InputMapping projection failure: {self:?}")
    }
}
impl std::error::Error for ParseFailure {}
impl From<ProvenanceError> for ParseFailure {
    fn from(error: ProvenanceError) -> Self {
        Self::Provenance(error)
    }
}
type Result<T, E = ParseFailure> = std::result::Result<T, E>;

/// Project against exactly the immutable text the tree describes. Caller-owned
/// Sources survive lowering/checking so every later diagnostic quotes that text.
pub fn project(
    document: &Document,
    sources: &Sources,
    snapshot: SnapshotId,
) -> Result<ParseOutcome> {
    if sources.snapshot(snapshot)?.text.as_ref() != document.text {
        return Err(ParseFailure::SnapshotMismatch);
    }
    let projection = Projection { sources, snapshot };
    let root = document.tree.root_node();
    let mut errors = Vec::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        let message = if node.is_missing() {
            Some(format!("Expected '{}'.", node.kind()))
        } else if node.is_error() {
            Some("Unexpected syntax.".into())
        } else {
            None
        };
        if let Some(message) = message {
            errors.push(SyntaxDiagnostic {
                span: projection.span(node)?,
                message,
            });
        } else if node.has_error() {
            // One diagnostic per error region, not cascades within ERROR nodes.
            pending.extend(node.children(&mut node.walk()));
        }
    }
    if !errors.is_empty() {
        errors.sort_by_key(|error| error.span.byte_range().start);
        return Ok(ParseOutcome::SyntaxErrors(errors));
    }
    if root.kind() != "source_file" || root.has_error() {
        return Err(ParseFailure::UnexpectedTree(root.to_sexp()));
    }
    let mut program = Program::default();
    for node in root.named_children(&mut root.walk()) {
        match node.kind() {
            "comment" => (),
            "declaration" => {
                let kind = match field(node, "kind")?.kind() {
                    "input" => Kind::Input,
                    "slot" => Kind::Slot,
                    other => return Err(ParseFailure::UnexpectedTree(other.into())),
                };
                let names = node
                    .children_by_field_name("name", &mut node.walk())
                    .map(|name| projection.name(name))
                    .collect::<Result<_>>()?;
                program.declarations.push(Declaration {
                    kind,
                    names,
                    span: projection.span(node)?,
                });
            }
            "mapping" => program.mappings.push(Mapping {
                target: projection.name(field(node, "target")?)?,
                input: projection.name(field(node, "input")?)?,
                condition: node
                    .child_by_field_name("condition")
                    .map(|n| projection.expr(n))
                    .transpose()?,
                span: projection.span(node)?,
            }),
            "mask" => program.masks.push(Mask {
                target: projection.name(field(node, "target")?)?,
                condition: node
                    .child_by_field_name("condition")
                    .map(|n| projection.expr(n))
                    .transpose()?,
                span: projection.span(node)?,
            }),
            other => return Err(ParseFailure::UnexpectedTree(other.into())),
        }
    }
    Ok(ParseOutcome::Parsed(program))
}

fn field<'a>(node: Node<'a>, name: &str) -> Result<Node<'a>> {
    node.child_by_field_name(name)
        .ok_or_else(|| ParseFailure::UnexpectedTree(format!("{} missing {name}", node.kind())))
}

struct Projection<'a> {
    sources: &'a Sources,
    snapshot: SnapshotId,
}
impl Projection<'_> {
    fn span(&self, node: Node<'_>) -> Result<SourceSpan> {
        Ok(self.sources.span(self.snapshot, node.byte_range())?)
    }
    fn name(&self, node: Node<'_>) -> Result<Name> {
        let span = self.span(node)?;
        Ok(Name {
            text: self.sources.text(span)?.into(),
            span,
        })
    }
    fn expr(&self, node: Node<'_>) -> Result<Expr> {
        let child = |name| self.expr(field(node, name)?).map(Box::new);
        let kind = match node.kind() {
            "available" => ExprKind::Available(self.name(field(node, "argument")?)?),
            "present" => ExprKind::Present(self.name(field(node, "argument")?)?),
            "input_value" | "slot_value" => ExprKind::Value {
                kind: if node.kind() == "input_value" {
                    Kind::Input
                } else {
                    Kind::Slot
                },
                name: self.name(field(node, "argument")?)?,
                literal: self.name(field(node, "literal")?)?,
            },
            "and" => ExprKind::And(child("left")?, child("right")?),
            "or" => ExprKind::Or(child("left")?, child("right")?),
            "not" => ExprKind::Not {
                keyword: self.span(field(node, "keyword")?)?,
                operand: child("operand")?,
            },
            "group" => ExprKind::Group(child("inner")?),
            other => return Err(ParseFailure::UnexpectedTree(other.into())),
        };
        Ok(Expr {
            kind,
            span: self.span(node)?,
        })
    }
}
