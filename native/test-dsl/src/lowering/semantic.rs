//! Span-free inputs and path-keyed name checking. No IR handles or source text.

use super::DiagnosticKind;
use crate::ast::Kind;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemanticStatement {
    Declaration {
        kind: Kind,
        names: Vec<String>,
    },
    Mapping {
        target: String,
        input: String,
        condition: Option<Expression>,
    },
    Mask {
        target: String,
        condition: Option<Expression>,
    },
}

/// Preserve authored grouping and negations, even when their meanings coincide.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression {
    Available(String),
    Present(String),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Group(Box<Self>),
}

/// Document-local occurrence identity, not an edit-history or query identity.
/// The incremental pipeline interns the form separately, without this index.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StatementKey {
    pub form: Arc<SemanticStatement>,
    pub duplicate: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Step {
    Left,
    Right,
    Operand,
    Inner,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExprPath(pub Vec<Step>);
impl ExprPath {
    pub fn child(&self, step: Step) -> Self {
        let mut path = self.clone();
        path.0.push(step);
        path
    }
}

/// A typed selector in one authored statement, not a diagnostic role tag.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstPath {
    Statement,
    DeclaredName(usize),
    Target,
    Input,
    Expression(ExprPath),
    Argument(ExprPath),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    pub statement: StatementKey,
    pub path: AstPath,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathDiagnostic {
    pub kind: DiagnosticKind,
    pub primary: Location,
    pub related: Vec<Location>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    Resolved,
    WrongKind { found: Kind },
    Missing,
}

/// A cached error describes meaning, not a particular statement occurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationDiagnostic {
    pub kind: DiagnosticKind,
    pub primary: AstPath,
    pub related: Option<(Kind, String)>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Names(BTreeMap<(Kind, String), Location>);
impl Names {
    pub fn collect(statements: &[StatementKey]) -> (Self, Vec<PathDiagnostic>) {
        let mut names = Self::default();
        let mut errors = Vec::new();
        for statement in statements {
            let SemanticStatement::Declaration {
                kind,
                names: values,
            } = statement.form.as_ref()
            else {
                continue;
            };
            for (index, name) in values.iter().enumerate() {
                let location = Location {
                    statement: statement.clone(),
                    path: AstPath::DeclaredName(index),
                };
                let key = (*kind, name.clone());
                if let Some(previous) = names.0.get(&key) {
                    errors.push(PathDiagnostic {
                        kind: DiagnosticKind::DuplicateDeclaration {
                            name: name.clone(),
                            kind: *kind,
                        },
                        primary: location,
                        related: vec![previous.clone()],
                    });
                } else {
                    names.0.insert(key, location);
                }
            }
        }
        (names, errors)
    }

    /// The result of one name lookup is the tracked dependency, not a
    /// declaration-table revision or a declaration's current source range.
    pub fn resolve(&self, name: &str, expected: Kind) -> Resolution {
        if self.0.contains_key(&(expected, name.into())) {
            return Resolution::Resolved;
        }
        let other = match expected {
            Kind::Input => Kind::Slot,
            Kind::Slot => Kind::Input,
        };
        match self.0.get(&(other, name.into())) {
            Some(_) => Resolution::WrongKind { found: other },
            None => Resolution::Missing,
        }
    }

    /// Bind shared errors to this occurrence and the current declaration list.
    pub fn bind(
        &self,
        statement: &StatementKey,
        diagnostics: &[ValidationDiagnostic],
    ) -> super::Result<Vec<PathDiagnostic>> {
        diagnostics
            .iter()
            .map(|d| {
                let related = d
                    .related
                    .as_ref()
                    .map(|name| {
                        self.0.get(name).cloned().ok_or_else(|| {
                            super::LoweringFailure::InvalidAst(
                                "diagnostic declaration is missing".into(),
                            )
                        })
                    })
                    .transpose()?
                    .into_iter()
                    .collect();
                Ok(PathDiagnostic {
                    kind: d.kind.clone(),
                    primary: Location {
                        statement: statement.clone(),
                        path: d.primary.clone(),
                    },
                    related,
                })
            })
            .collect()
    }
}

pub fn validate_form(
    form: &SemanticStatement,
    mut resolve: impl FnMut(&str, Kind) -> Resolution,
) -> Vec<ValidationDiagnostic> {
    let mut errors = Vec::new();
    let mut check = |name: &str, expected, path| {
        let (kind, related) = match resolve(name, expected) {
            Resolution::Resolved => return,
            Resolution::Missing => (
                DiagnosticKind::UnknownName {
                    name: name.into(),
                    expected,
                },
                None,
            ),
            Resolution::WrongKind { found } => (
                DiagnosticKind::WrongKind {
                    name: name.into(),
                    expected,
                    found,
                },
                Some((found, name.into())),
            ),
        };
        errors.push(ValidationDiagnostic {
            kind,
            primary: path,
            related,
        });
    };
    fn expression(expr: &Expression, path: &ExprPath, check: &mut impl FnMut(&str, Kind, AstPath)) {
        match expr {
            Expression::Available(name) => check(name, Kind::Slot, AstPath::Argument(path.clone())),
            Expression::Present(name) => check(name, Kind::Input, AstPath::Argument(path.clone())),
            Expression::And(a, b) | Expression::Or(a, b) => {
                expression(a, &path.child(Step::Left), check);
                expression(b, &path.child(Step::Right), check);
            }
            Expression::Not(e) => expression(e, &path.child(Step::Operand), check),
            Expression::Group(e) => expression(e, &path.child(Step::Inner), check),
        }
    }
    let condition = match form {
        SemanticStatement::Mapping {
            target,
            input,
            condition,
        } => {
            check(target, Kind::Slot, AstPath::Target);
            check(input, Kind::Input, AstPath::Input);
            condition
        }
        SemanticStatement::Mask { target, condition } => {
            check(target, Kind::Slot, AstPath::Target);
            condition
        }
        SemanticStatement::Declaration { .. } => return errors,
    };
    if let Some(expr) = condition {
        expression(expr, &ExprPath::default(), &mut check);
    }
    errors
}

pub fn validate(statements: &[StatementKey]) -> super::Result<Vec<PathDiagnostic>> {
    let (names, mut errors) = Names::collect(statements);
    for statement in statements {
        let diagnostics = validate_form(&statement.form, |name, kind| names.resolve(name, kind));
        errors.extend(names.bind(statement, &diagnostics)?);
    }
    Ok(errors)
}
