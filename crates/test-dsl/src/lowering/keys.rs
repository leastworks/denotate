//! Frontend-owned identity encoding and fresh installation binding. This is an
//! in-session structural encoding, not a persisted format or hash digest.
use super::{semantic::StatementKey, *};
use denotate_ir::installation::Installation;
use denotate_normalize::Instruction;

pub const LIBRARY: &str = "test-dsl/library";
const DOCUMENT: &str = "test-dsl/document";

pub fn owner(statement: &StatementKey) -> OwnerKey {
    // This encoding relies on DERIVED Debug for EVERY type nested inside
    // SemanticStatement (including future fields). A custom Debug implementation
    // must not erase semantic distinctions; change the encoding before adding one.
    // Debug of these closed, derived structural enums is injective (strings are
    // escaped and variants/fields delimited). Numeric aliases already normalize.
    OwnerKey::new(
        DOCUMENT,
        format!("{:?}/duplicate:{}", statement.form, statement.duplicate).into_bytes(),
    )
}

pub fn library(
    corpus: &Corpus,
    library: &MappingLibrary,
) -> std::result::Result<SemanticKeys, KeyError> {
    let mut keys = SemanticKeys::default();
    for s in corpus.sorts() {
        keys.bind_sort(
            corpus,
            s.id,
            SortKey(QualifiedKey::new(LIBRARY, s.name.as_str())),
        )?;
    }
    for r in corpus.relations() {
        keys.bind_relation(
            corpus,
            r.id,
            RelationKey::Named(QualifiedKey::new(LIBRARY, r.name.as_str())),
        )?;
    }
    for c in corpus.constants() {
        constant(&mut keys, corpus, c.id)?;
    }
    for (name, id) in &library.rules {
        let key = RuleKey::Library(QualifiedKey::new(LIBRARY, *name));
        keys.bind_rule(corpus, *id, key.clone())?;
        let rule = corpus
            .rule(*id)
            .ok_or(KeyError::UnknownOccurrence((*id).into()))?;
        for (position, atom) in std::iter::once(&rule.head)
            .chain(rule.body.iter().map(Literal::atom))
            .enumerate()
        {
            keys.bind_occurrence(
                corpus,
                atom.id(),
                OccurrenceKey::Library {
                    rule: key.clone(),
                    atom: position,
                    argument: None,
                },
            )?;
            for (argument, term) in atom.arguments().iter().enumerate() {
                keys.bind_occurrence(
                    corpus,
                    term.id(),
                    OccurrenceKey::Library {
                        rule: key.clone(),
                        atom: position,
                        argument: Some(argument),
                    },
                )?;
            }
        }
    }
    for o in corpus.obligations() {
        keys.bind_obligation(
            corpus,
            o.id,
            ObligationKey(QualifiedKey::new(LIBRARY, o.name.as_str())),
        )?;
    }
    for a in corpus.assumptions() {
        keys.bind_assumption(
            corpus,
            a.id,
            AssumptionKey(QualifiedKey::new(LIBRARY, a.name.as_str())),
        )?;
    }
    for v in corpus.verifications() {
        keys.bind_verification(
            corpus,
            v.id,
            VerificationKey(QualifiedKey::new(LIBRARY, v.name.as_str())),
        )?;
    }
    Ok(keys)
}

pub fn constant(
    keys: &mut SemanticKeys,
    corpus: &Corpus,
    id: ConstantId,
) -> std::result::Result<(), KeyError> {
    let c = corpus
        .constant(id)
        .ok_or(KeyError::UnknownOccurrence(id.into()))?;
    keys.bind_constant(
        corpus,
        id,
        ConstantKey {
            sort: keys.sort(c.sort)?.clone(),
            name: c.name.as_str().into(),
        },
    )
}

pub fn installed(
    keys: &mut SemanticKeys,
    corpus: &Corpus,
    statement: &StatementKey,
    recipe: &recipe::Recipe,
    installed: &Installation,
) -> std::result::Result<(), KeyError> {
    let owner = owner(statement);
    let normalized = recipe
        .normalized
        .as_ref()
        .ok_or(KeyError::InvalidStructure("missing recipe"))?;
    // Helper declarations are in the installer's occurrence map, with their
    // typed RelationId obtained from the just-installed rule atoms.
    let relations: std::collections::BTreeMap<_, _> = installed
        .rules()
        .values()
        .filter_map(|id| corpus.rule(*id))
        .flat_map(|r| std::iter::once(&r.head).chain(r.body.iter().map(Literal::atom)))
        .map(|a| (OccurrenceId::from(a.relation()), a.relation()))
        .collect();
    for instruction in normalized.instructions() {
        match instruction {
            Instruction::Helper { id } => {
                let occurrence = installed
                    .occurrences()
                    .get(id)
                    .ok_or(KeyError::InvalidStructure("missing installed helper"))?;
                let relation = relations
                    .get(occurrence)
                    .ok_or(KeyError::InvalidStructure("unreferenced installed helper"))?;
                keys.bind_relation(
                    corpus,
                    *relation,
                    RelationKey::Generated {
                        owner: owner.clone(),
                        local: id.0,
                    },
                )?;
            }
            Instruction::Rule { id, .. } => {
                let rule = installed
                    .rules()
                    .get(id)
                    .ok_or(KeyError::InvalidStructure("missing installed rule"))?;
                keys.bind_rule(
                    corpus,
                    *rule,
                    RuleKey::Installed {
                        owner: owner.clone(),
                        local: id.0,
                    },
                )?;
            }
            Instruction::Atom { id, arguments, .. } => {
                for local in std::iter::once(*id).chain(arguments.iter().map(|a| a.id)) {
                    let occurrence = installed
                        .occurrences()
                        .get(&local)
                        .ok_or(KeyError::InvalidStructure("missing installed occurrence"))?;
                    keys.bind_occurrence(
                        corpus,
                        *occurrence,
                        OccurrenceKey::Installed {
                            owner: owner.clone(),
                            local: local.0,
                        },
                    )?;
                }
            }
        }
    }
    Ok(())
}
