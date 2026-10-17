//! Arena-free leaf translation and frontend attribution assignments.
use super::semantic::{AstPath, ExprPath, Expression, SemanticStatement, Step};
use crate::ast::Kind;
use denotate_normalize as n;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constant {
    pub kind: Kind,
    pub name: String,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relation {
    MappedTo,
    Masked,
    Present,
    Available,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Payload {
    pub relation: Relation,
    pub arguments: Vec<Constant>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Assignments {
    pub origins: BTreeMap<n::Local, AstPath>,
    pub guards: BTreeMap<n::Local, AstPath>,
    pub removals: BTreeMap<n::Local, AstPath>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Recipe {
    pub form: Arc<SemanticStatement>,
    pub normalized: Option<n::Recipe<Payload, Payload, AstPath>>,
    pub assignments: Assignments,
}
/// Statement-local failures are safe to cache; snapshot failures are not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecipeError {
    Normalization(n::ConstructionError<AstPath>),
    AssignmentRecordCount { output: n::Local, count: usize },
}
impl std::fmt::Display for RecipeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for RecipeError {}

fn expression(expr: &Expression, path: ExprPath) -> n::Expression<Payload, AstPath> {
    let key = AstPath::Expression(path.clone());
    let kind = match expr {
        Expression::Available(name) | Expression::Present(name) => {
            let (relation, kind) = if matches!(expr, Expression::Available(_)) {
                (Relation::Available, Kind::Slot)
            } else {
                (Relation::Present, Kind::Input)
            };
            n::ExpressionKind::Leaf {
                payload: Payload {
                    relation,
                    arguments: vec![Constant {
                        kind,
                        name: name.clone(),
                    }],
                },
                arguments: vec![n::Argument {
                    key: AstPath::Argument(path),
                    variable: false,
                }],
            }
        }
        Expression::And(a, b) => n::ExpressionKind::And(
            Box::new(expression(a, path.child(Step::Left))),
            Box::new(expression(b, path.child(Step::Right))),
        ),
        Expression::Or(a, b) => n::ExpressionKind::Or(
            Box::new(expression(a, path.child(Step::Left))),
            Box::new(expression(b, path.child(Step::Right))),
        ),
        Expression::Not(a) => {
            n::ExpressionKind::Not(Box::new(expression(a, path.child(Step::Operand))))
        }
        Expression::Group(a) => {
            n::ExpressionKind::Group(Box::new(expression(a, path.child(Step::Inner))))
        }
    };
    n::Expression { key, kind }
}
impl Recipe {
    pub fn lower(form: Arc<SemanticStatement>) -> std::result::Result<Self, RecipeError> {
        let mut assignments = Assignments {
            origins: BTreeMap::new(),
            guards: BTreeMap::new(),
            removals: BTreeMap::new(),
        };
        let (relation, args, condition) = match form.as_ref() {
            SemanticStatement::Declaration { .. } => {
                return Ok(Self {
                    form,
                    normalized: None,
                    assignments,
                });
            }
            SemanticStatement::Mapping {
                target,
                input,
                condition,
            } => (
                Relation::MappedTo,
                vec![
                    (Kind::Input, input, AstPath::Input),
                    (Kind::Slot, target, AstPath::Target),
                ],
                condition,
            ),
            SemanticStatement::Mask { target, condition } => (
                Relation::Masked,
                vec![(Kind::Slot, target, AstPath::Target)],
                condition,
            ),
        };
        let definition = n::Definition {
            head: n::Atom {
                key: AstPath::Statement,
                payload: Payload {
                    relation,
                    arguments: args
                        .iter()
                        .map(|(kind, name, _)| Constant {
                            kind: *kind,
                            name: (*name).clone(),
                        })
                        .collect(),
                },
                arguments: args
                    .iter()
                    .map(|(_, _, key)| n::Argument {
                        key: key.clone(),
                        variable: false,
                    })
                    .collect(),
            },
            body: condition
                .as_ref()
                .map(|e| expression(e, ExprPath::default())),
        };
        let normalized = n::normalize(&definition).map_err(RecipeError::Normalization)?;
        // Frontend policy: choose one origin per output occurrence/view.
        for (id, records) in normalized.records() {
            let [record] = records.as_slice() else {
                return Err(RecipeError::AssignmentRecordCount {
                    output: *id,
                    count: records.len(),
                });
            };
            let origin = if let Some(argument) = &record.argument {
                argument.clone()
            } else if let Some(outer) = record.negations.first() {
                outer.clone()
            } else if matches!(record.helper, n::HelperRole::Use(_))
                || (record.helper != n::HelperRole::Neither
                    && matches!(
                        record.kind,
                        n::OutputKind::Helper | n::OutputKind::Head | n::OutputKind::Rule
                    ))
            {
                record.entry.clone()
            } else {
                record.node.clone()
            };
            assignments.origins.insert(*id, origin);
            if record.kind == n::OutputKind::Rule
                && record.helper == n::HelperRole::Neither
                && condition.is_some()
            {
                assignments
                    .guards
                    .insert(*id, AstPath::Expression(ExprPath::default()));
            }
            // The old policy authorizes candidate removals only on leaf literals,
            // not helper uses. Current syntax still decides whether removal is safe.
            if record.kind == n::OutputKind::Literal
                && !matches!(record.helper, n::HelperRole::Use(_))
                && record.polarity == Some(n::Polarity::Negative)
            {
                if let Some(outer) = record.negations.first() {
                    assignments.removals.insert(*id, outer.clone());
                }
            }
        }
        Ok(Self {
            form,
            normalized: Some(normalized),
            assignments,
        })
    }
}
