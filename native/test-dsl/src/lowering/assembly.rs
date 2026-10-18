//! Fresh snapshot installation and source binding of cached recipes.
use super::{
    projection::Projection,
    recipe::{Payload, Recipe, Relation, Value},
    semantic::{AstPath, ExprPath, SemanticStatement},
    *,
};
use crate::{
    attribution::{MaskAttribution, SourceView},
    library,
    warnings::Contribution,
};
use denotate_ir::installation::{self, BoundAtom};
use std::collections::BTreeMap;

fn failure(e: impl std::fmt::Display) -> LoweringFailure {
    LoweringFailure::InvalidAst(e.to_string())
}

pub fn assemble<R: std::borrow::Borrow<Recipe>>(
    projection: &Projection,
    recipes: &[R],
    sources: &Sources,
) -> Result<LoweredProgram> {
    if recipes.len() != projection.statements.len() {
        return Err(failure("recipe/source statement count differs"));
    }
    let mut corpus = Corpus::new();
    let library = library::build(&mut corpus)?;
    // K is snapshot-local. No cached recipe depends on this union.
    let mut integers = std::collections::BTreeSet::new();
    for recipe in recipes {
        if let Some(normalized) = &recipe.borrow().normalized {
            for instruction in normalized.instructions() {
                if let denotate_normalize::Instruction::Atom {
                    target:
                        denotate_normalize::Target::Head(p) | denotate_normalize::Target::Leaf(p),
                    ..
                } = instruction
                {
                    for argument in &p.arguments {
                        if let Value::Integer(value) = argument {
                            integers.insert(*value);
                        }
                    }
                }
            }
        }
    }
    let integers = integers
        .into_iter()
        .map(|v| Ok((v, corpus.declare_constant(v.to_string(), library.integer)?)))
        .collect::<Result<BTreeMap<_, _>>>()?;
    let mut attribution = Attribution::default();
    for rule in corpus.rules() {
        attribution
            .rewrites
            .owners
            .insert(rule.id, Contribution::Library);
    }
    let mut constants = BTreeMap::new();
    for (source, recipe) in projection.statements.iter().zip(recipes) {
        let recipe = recipe.borrow();
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
                Relation::Value => library.value,
                Relation::SlotValue => library.slot_value,
            };
            let arguments = p
                .arguments
                .iter()
                .map(|a| {
                    let id = match a {
                        Value::Name(a) => constants.get(&(a.kind, a.name.clone())),
                        Value::Integer(value) => integers.get(value),
                    };
                    id.copied().map(Term::Constant).ok_or_else(|| {
                        installation::InstallError::Binding(format!(
                            "validated constant missing: {a:?}"
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
