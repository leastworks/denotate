//! Rebuilt for each snapshot. Only the span-free keys cross into recipe queries.

use super::{DslDiagnostic, LoweringFailure, Result, semantic::*};
use crate::{
    ast,
    warnings::{self, SourceEdit},
};
use denotate_ir::{SourceSpan, Sources};
use std::{collections::BTreeMap, sync::Arc};

pub struct StatementSource {
    pub key: StatementKey,
    spans: BTreeMap<AstPath, SourceSpan>,
    pub(crate) removals: BTreeMap<AstPath, SourceEdit>,
}
impl StatementSource {
    pub fn span(&self, path: &AstPath) -> Result<SourceSpan> {
        self.spans.get(path).copied().ok_or_else(|| {
            LoweringFailure::InvalidAst(format!("missing attribution path: {path:?}"))
        })
    }
}

pub struct Projection {
    pub statements: Vec<StatementSource>,
}
impl Projection {
    pub fn keys(&self) -> Vec<StatementKey> {
        self.statements.iter().map(|s| s.key.clone()).collect()
    }
    pub fn diagnostics(&self, diagnostics: &[PathDiagnostic]) -> Result<Vec<DslDiagnostic>> {
        let statements: BTreeMap<_, _> = self.statements.iter().map(|s| (&s.key, s)).collect();
        let locate = |location: &Location| -> Result<SourceSpan> {
            statements
                .get(&location.statement)
                .ok_or_else(|| {
                    LoweringFailure::InvalidAst("diagnostic references a missing statement".into())
                })?
                .span(&location.path)
        };
        diagnostics
            .iter()
            .map(|d| {
                Ok(DslDiagnostic {
                    kind: d.kind.clone(),
                    span: locate(&d.primary)?,
                    related: d.related.iter().map(&locate).collect::<Result<_>>()?,
                })
            })
            .collect()
    }
}

pub fn project(program: &ast::Program, sources: &Sources) -> Result<Projection> {
    let mut result = Projection {
        statements: Vec::new(),
    };
    let mut counts = BTreeMap::<Arc<SemanticStatement>, usize>::new();
    let mut push = |form: SemanticStatement, spans, removals| {
        let form = Arc::new(form);
        let duplicate = counts.entry(form.clone()).or_default();
        result.statements.push(StatementSource {
            key: StatementKey {
                form,
                duplicate: *duplicate,
            },
            spans,
            removals,
        });
        *duplicate += 1;
    };
    // Declarations, mappings, then masks; each list retains authored order.
    // This preserves pre-mask IR order and also supports hand-built ASTs.
    for declaration in &program.declarations {
        sources.text(declaration.span)?;
        let mut spans = BTreeMap::from([(AstPath::Statement, declaration.span)]);
        let mut names = Vec::new();
        for (index, name) in declaration.names.iter().enumerate() {
            validate_name(name, sources)?;
            spans.insert(AstPath::DeclaredName(index), name.span);
            names.push(name.text.clone());
        }
        push(
            SemanticStatement::Declaration {
                kind: declaration.kind,
                names,
            },
            spans,
            BTreeMap::new(),
        );
    }
    for mapping in &program.mappings {
        sources.text(mapping.span)?;
        validate_name(&mapping.target, sources)?;
        validate_name(&mapping.input, sources)?;
        let mut spans = BTreeMap::from([
            (AstPath::Statement, mapping.span),
            (AstPath::Target, mapping.target.span),
            (AstPath::Input, mapping.input.span),
        ]);
        let condition = mapping
            .condition
            .as_ref()
            .map(|expr| expression(expr, &ExprPath::default(), &mut spans, sources))
            .transpose()?;
        push(
            SemanticStatement::Mapping {
                target: mapping.target.text.clone(),
                input: mapping.input.text.clone(),
                condition,
            },
            spans,
            warnings::removals(mapping, sources)?.into_iter().collect(),
        );
    }
    for mask in &program.masks {
        sources.text(mask.span)?;
        validate_name(&mask.target, sources)?;
        let mut spans = BTreeMap::from([
            (AstPath::Statement, mask.span),
            (AstPath::Target, mask.target.span),
        ]);
        let condition = mask
            .condition
            .as_ref()
            .map(|expr| expression(expr, &ExprPath::default(), &mut spans, sources))
            .transpose()?;
        push(
            SemanticStatement::Mask {
                target: mask.target.text.clone(),
                condition,
            },
            spans,
            warnings::condition_removals(mask.condition.as_ref(), mask.target.span, sources)?
                .into_iter()
                .collect(),
        );
    }
    Ok(result)
}

fn validate_name(name: &ast::Name, sources: &Sources) -> Result<()> {
    if sources.text(name.span)? != name.text || name.text.is_empty() {
        return Err(LoweringFailure::InvalidAst(
            "name does not match its source span".into(),
        ));
    }
    Ok(())
}

fn expression(
    expr: &ast::Expr,
    path: &ExprPath,
    spans: &mut BTreeMap<AstPath, SourceSpan>,
    sources: &Sources,
) -> Result<Expression> {
    sources.text(expr.span)?;
    spans.insert(AstPath::Expression(path.clone()), expr.span);
    let mut child = |expr, step| expression(expr, &path.child(step), spans, sources).map(Box::new);
    Ok(match &expr.kind {
        ast::ExprKind::Available(name) | ast::ExprKind::Present(name) => {
            validate_name(name, sources)?;
            spans.insert(AstPath::Argument(path.clone()), name.span);
            if matches!(expr.kind, ast::ExprKind::Available(_)) {
                Expression::Available(name.text.clone())
            } else {
                Expression::Present(name.text.clone())
            }
        }
        ast::ExprKind::Value {
            kind,
            name,
            literal,
        } => {
            validate_name(name, sources)?;
            validate_name(literal, sources)?;
            spans.insert(AstPath::Argument(path.clone()), name.span);
            spans.insert(AstPath::Integer(path.clone()), literal.span);
            Expression::Value {
                kind: *kind,
                name: name.text.clone(),
                literal: IntegerLiteral::parse(&literal.text),
            }
        }
        ast::ExprKind::And(a, b) => Expression::And(child(a, Step::Left)?, child(b, Step::Right)?),
        ast::ExprKind::Or(a, b) => Expression::Or(child(a, Step::Left)?, child(b, Step::Right)?),
        ast::ExprKind::Group(e) => Expression::Group(child(e, Step::Inner)?),
        ast::ExprKind::Not { keyword, operand } => {
            if sources.text(*keyword)? != "not" {
                return Err(LoweringFailure::InvalidAst(
                    "not keyword span must contain 'not'".into(),
                ));
            }
            Expression::Not(child(operand, Step::Operand)?)
        }
    })
}
