//! 5.3a candidate adapter, not yet used by the server or Salsa queries.
//! Leaf translation and attribution policy belong here, not in normalization.
use super::{
    projection::Projection,
    semantic::{AstPath, ExprPath, Expression, SemanticStatement, Step},
    *,
};
use crate::{
    attribution::{MaskAttribution, SourceView},
    library,
    warnings::Contribution,
};
use denotate_ir::installation::{self, BoundAtom};
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
fn failure(e: impl std::fmt::Display) -> LoweringFailure {
    LoweringFailure::InvalidAst(e.to_string())
}

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
    pub fn lower(form: Arc<SemanticStatement>) -> Result<Self> {
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
        let normalized = n::normalize(&definition).map_err(failure)?;
        // Frontend policy: choose one origin per output occurrence/view.
        for (id, records) in normalized.records() {
            let [record] = records.as_slice() else {
                return Err(failure(
                    "InputMapping expects one transformation record per output",
                ));
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

pub fn assemble(
    projection: &Projection,
    recipes: &[Recipe],
    sources: &Sources,
) -> Result<LoweredProgram> {
    if recipes.len() != projection.statements.len() {
        return Err(failure("recipe/source statement count differs"));
    }
    let mut corpus = Corpus::new();
    let library = library::build(&mut corpus)?;
    let mut attribution = Attribution::default();
    for rule in corpus.rules() {
        attribution
            .rewrites
            .owners
            .insert(rule.id, Contribution::Library);
    }
    let mut constants = BTreeMap::new();
    for (source, recipe) in projection.statements.iter().zip(recipes) {
        if source.key.form != recipe.form {
            return Err(failure("recipe does not match current semantic statement"));
        }
        if let SemanticStatement::Declaration { kind, names } = recipe.form.as_ref() {
            for (index, name) in names.iter().enumerate() {
                let sort = match kind {
                    Kind::Input => library.input,
                    Kind::Slot => library.slot,
                };
                let constant = corpus.declare_constant(name, sort)?;
                constants.insert((*kind, name.clone()), constant);
                attribution.provenance.attach(
                    &corpus,
                    sources,
                    constant,
                    [Origin::new(source.span(&AstPath::DeclaredName(index))?)],
                )?;
            }
            continue;
        }
        let normalized = recipe
            .normalized
            .as_ref()
            .ok_or_else(|| failure("missing normalized definition"))?;
        let binding = |p: &Payload| -> std::result::Result<BoundAtom, installation::InstallError> {
            let relation = match p.relation {
                Relation::MappedTo => library.mapped_to,
                Relation::Masked => library.masked,
                Relation::Present => library.present,
                Relation::Available => library.available,
            };
            let arguments = p
                .arguments
                .iter()
                .map(|a| {
                    constants
                        .get(&(a.kind, a.name.clone()))
                        .copied()
                        .map(Term::Constant)
                        .ok_or_else(|| {
                            installation::InstallError::Binding(format!(
                                "validated constant missing: {:?} {}",
                                a.kind, a.name
                            ))
                        })
                })
                .collect::<std::result::Result<Vec<_>, _>>()?;
            Ok(BoundAtom {
                relation,
                arguments,
            })
        };
        let installed =
            installation::install(&mut corpus, normalized, binding, binding).map_err(failure)?;
        let origins = recipe
            .assignments
            .origins
            .iter()
            .map(|(id, path)| Ok((*id, vec![Origin::new(source.span(path)?)])))
            .collect::<Result<BTreeMap<_, _>>>()?;
        installed
            .transfer(&corpus, sources, &mut attribution.provenance, &origins)
            .map_err(failure)?;
        for (local, rule) in installed.rules() {
            attribution
                .rewrites
                .owners
                .insert(*rule, Contribution::Program);
            if let Some(path) = recipe.assignments.guards.get(local) {
                let span = source.span(path)?;
                let view = SourceView::try_from(sources.snapshot(span.snapshot())?.view.as_str())?;
                attribution.guards.insert((*rule, view), span);
            }
            if let SemanticStatement::Mask { target, condition } = recipe.form.as_ref() {
                attribution.masks.insert(
                    *rule,
                    MaskAttribution {
                        target: *constants
                            .get(&(Kind::Slot, target.clone()))
                            .ok_or_else(|| failure("validated mask target missing"))?,
                        statement: source.span(&AstPath::Statement)?,
                        condition: condition
                            .as_ref()
                            .map(|_| source.span(&AstPath::Expression(ExprPath::default())))
                            .transpose()?,
                    },
                );
            }
        }
        for (id, path) in &recipe.assignments.removals {
            if let Some(edit) = source.removals.get(path) {
                let occurrence = installed
                    .occurrences()
                    .get(id)
                    .ok_or_else(|| failure("missing removal occurrence"))?;
                attribution
                    .rewrites
                    .removals
                    .insert(*occurrence, edit.clone());
            }
        }
    }
    attribution.validate(&corpus, sources)?;
    Ok(LoweredProgram {
        corpus,
        library,
        attribution,
    })
}

pub fn lower(program: &Program, sources: &Sources) -> Result<LoweringOutcome> {
    let projection = projection::project(program, sources)?;
    let keys = projection.keys();
    let diagnostics = semantic::validate(&keys)?;
    if !diagnostics.is_empty() {
        return Ok(LoweringOutcome::UserErrors(
            projection.diagnostics(&diagnostics)?,
        ));
    }
    let recipes = keys
        .iter()
        .map(|s| Recipe::lower(s.form.clone()))
        .collect::<Result<Vec<_>>>()?;
    Ok(LoweringOutcome::Lowered(assemble(
        &projection,
        &recipes,
        sources,
    )?))
}
