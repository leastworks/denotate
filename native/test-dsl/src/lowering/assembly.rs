//! Replays recipes into a fresh IR arena, then reconnects current-source paths.

use super::{LoweredProgram, LoweringFailure, Result, projection::Projection, recipe::*};
use crate::{
    ast::Kind,
    attribution::{Attribution, SourceView},
    library,
    warnings::Contribution,
};
use denotate_ir::{
    Atom, ConstantId, Corpus, Literal as IrLiteral, OccurrenceId, Origin, RelationRole, Sources,
    Term,
};
use std::collections::BTreeMap;

fn invalid(message: &str) -> LoweringFailure {
    LoweringFailure::InvalidAst(message.into())
}

pub fn assemble(
    projection: &Projection,
    recipes: &[Recipe],
    sources: &Sources,
) -> Result<LoweredProgram> {
    if recipes.len() != projection.statements.len() {
        return Err(invalid("recipe/source statement count differs"));
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
    let mut constants = BTreeMap::<(Kind, String), ConstantId>::new();
    let mut next_helper = 1;
    for (source, recipe) in projection.statements.iter().zip(recipes) {
        if source.key.form != recipe.form {
            return Err(invalid("recipe does not match current semantic statement"));
        }
        let mut occurrences = BTreeMap::<LocalOccurrence, OccurrenceId>::new();
        let mut helpers = BTreeMap::new();
        let mut atoms = BTreeMap::<LocalOccurrence, Atom>::new();
        let mut rules = BTreeMap::new();
        for instruction in &recipe.instructions {
            match instruction {
                Instruction::Constant { id, value } => {
                    let sort = match value.kind {
                        Kind::Input => library.input,
                        Kind::Slot => library.slot,
                    };
                    let constant = corpus.declare_constant(&value.name, sort)?;
                    constants.insert((value.kind, value.name.clone()), constant);
                    occurrences.insert(*id, constant.into());
                }
                Instruction::Helper { id } => {
                    let relation = corpus.declare_relation(
                        format!("$condition_{next_helper}"),
                        RelationRole::Derived,
                        [],
                    )?;
                    next_helper += 1;
                    helpers.insert(*id, relation);
                    occurrences.insert(*id, relation.into());
                }
                Instruction::Atom {
                    id,
                    relation,
                    arguments,
                } => {
                    let relation = match relation {
                        RelationRef::MappedTo => library.mapped_to,
                        RelationRef::Present => library.present,
                        RelationRef::Available => library.available,
                        RelationRef::Helper(id) => *helpers
                            .get(id)
                            .ok_or_else(|| invalid("undeclared recipe helper"))?,
                    };
                    let terms = arguments
                        .iter()
                        .map(|arg| {
                            constants
                                .get(&(arg.value.kind, arg.value.name.clone()))
                                .copied()
                                .map(Term::Constant)
                                .ok_or_else(|| invalid("validated name missing during assembly"))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let atom = corpus.atom(relation, terms)?;
                    occurrences.insert(*id, atom.id());
                    for (arg, term) in arguments.iter().zip(atom.arguments()) {
                        occurrences.insert(arg.id, term.id());
                    }
                    atoms.insert(*id, atom);
                }
                Instruction::Rule { id, head, body } => {
                    let head = atoms
                        .remove(head)
                        .ok_or_else(|| invalid("recipe head missing or reused"))?;
                    let body = body
                        .iter()
                        .map(|literal| {
                            let atom = atoms
                                .remove(&literal.atom)
                                .ok_or_else(|| invalid("recipe body atom missing or reused"))?;
                            Ok(if literal.negative {
                                IrLiteral::Negative(atom)
                            } else {
                                IrLiteral::Positive(atom)
                            })
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let rule = corpus.add_rule(head, body)?;
                    rules.insert(*id, rule);
                    occurrences.insert(*id, rule.into());
                    attribution
                        .rewrites
                        .owners
                        .insert(rule, Contribution::Program);
                }
            }
        }
        if !atoms.is_empty() {
            return Err(invalid("unconsumed recipe atoms"));
        }
        let occurrence = |id: &LocalOccurrence| {
            occurrences
                .get(id)
                .copied()
                .ok_or_else(|| invalid("missing assembled occurrence"))
        };
        // Attach only after rules register their atoms with the construction API.
        for (id, path) in &recipe.origins {
            attribution.provenance.attach(
                &corpus,
                sources,
                occurrence(id)?,
                [Origin::new(source.span(path)?)],
            )?;
        }
        for (id, path) in &recipe.guards {
            let rule = *rules
                .get(id)
                .ok_or_else(|| invalid("guard references a non-rule occurrence"))?;
            let span = source.span(path)?;
            let view = SourceView::try_from(sources.snapshot(span.snapshot())?.view.as_str())?;
            attribution.guards.insert((rule, view), span);
        }
        for (id, path) in &recipe.removals {
            if let Some(edit) = source.removals.get(path) {
                attribution
                    .rewrites
                    .removals
                    .insert(occurrence(id)?, edit.clone());
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
