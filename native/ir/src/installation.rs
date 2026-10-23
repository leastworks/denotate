//! Fresh installation of arena-free Boolean recipes. Frontends supply bindings
//! and selected origins; this module never selects attribution or safe edits.
use crate::*;
use denotate_normalize::{Instruction, Local, Polarity, Recipe, Target};
use std::collections::BTreeMap;

#[derive(Debug)]
pub enum InstallError {
    Construction(ConstructionError),
    Provenance(ProvenanceError),
    /// Frontend could not resolve a symbolic payload in this snapshot.
    Binding(String),
    /// Binding disagrees with the recipe's arity or variable-occurrence contract.
    InvalidBinding(Local),
    UnknownLocal(Local),
}
impl From<ConstructionError> for InstallError {
    fn from(e: ConstructionError) -> Self {
        Self::Construction(e)
    }
}
impl From<ProvenanceError> for InstallError {
    fn from(e: ProvenanceError) -> Self {
        Self::Provenance(e)
    }
}
impl std::fmt::Display for InstallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid normalization installation: {self:?}")
    }
}
impl std::error::Error for InstallError {}
type Result<T> = std::result::Result<T, InstallError>;

pub struct BoundAtom {
    pub relation: RelationId,
    pub arguments: Vec<Term>,
}
#[derive(Debug)]
pub struct Installation {
    occurrences: BTreeMap<Local, OccurrenceId>,
    rules: BTreeMap<Local, RuleId>,
}
impl Installation {
    pub fn occurrences(&self) -> &BTreeMap<Local, OccurrenceId> {
        &self.occurrences
    }
    pub fn rules(&self) -> &BTreeMap<Local, RuleId> {
        &self.rules
    }
    /// Many-to-many transfer. The caller has already chosen the origins in each
    /// view and resolved them against the current source snapshot.
    pub fn transfer(
        &self,
        corpus: &Corpus,
        sources: &Sources,
        provenance: &mut Provenance,
        assignments: &BTreeMap<Local, Vec<Origin>>,
    ) -> Result<()> {
        for (local, origins) in assignments {
            let id = self
                .occurrences
                .get(local)
                .ok_or(InstallError::UnknownLocal(*local))?;
            provenance.attach(corpus, sources, *id, origins.iter().cloned())?;
        }
        Ok(())
    }
}
/// Like Corpus construction, errors may leave partial construction in the
/// destination. Build into a fresh snapshot and discard it on creator failure.
pub fn install<H, L, K>(
    corpus: &mut Corpus,
    recipe: &Recipe<H, L, K>,
    head_binding: impl FnMut(&H) -> Result<BoundAtom>,
    leaf_binding: impl FnMut(&L) -> Result<BoundAtom>,
) -> Result<Installation> {
    install_in(
        corpus,
        Namespace::default(),
        recipe,
        head_binding,
        leaf_binding,
    )
}

/// Install into the transformation's owning namespace. All generated helpers
/// and rules inherit this context, even when bindings reference declarations
/// in other namespaces. The caller supplies the triggering IR construct's
/// namespace, or chooses an explicit context for a shared transformation.
/// Recipes remain independent of namespace, source snapshots and file placement.
/// Errors have the same partial-construction behavior as [`install`].
pub fn install_in<H, L, K>(
    corpus: &mut Corpus,
    namespace: impl Into<Namespace>,
    recipe: &Recipe<H, L, K>,
    mut head_binding: impl FnMut(&H) -> Result<BoundAtom>,
    mut leaf_binding: impl FnMut(&L) -> Result<BoundAtom>,
) -> Result<Installation> {
    let namespace = namespace.into();
    let mut result = Installation {
        occurrences: BTreeMap::new(),
        rules: BTreeMap::new(),
    };
    let mut helpers = BTreeMap::new();
    let mut atoms = BTreeMap::new();
    for instruction in recipe.instructions() {
        match instruction {
            Instruction::Helper { id } => {
                let relation = corpus.declare_generated_relation_in(&namespace);
                helpers.insert(*id, relation);
                result.occurrences.insert(*id, relation.into());
            }
            Instruction::Atom {
                id,
                target,
                arguments,
            } => {
                let bound = match target {
                    Target::Head(h) => head_binding(h)?,
                    Target::Leaf(l) => leaf_binding(l)?,
                    Target::Helper(local) => BoundAtom {
                        relation: *helpers
                            .get(local)
                            .ok_or(InstallError::UnknownLocal(*local))?,
                        arguments: vec![],
                    },
                };
                if arguments.len() != bound.arguments.len()
                    || arguments
                        .iter()
                        .zip(&bound.arguments)
                        .any(|(a, t)| a.variable != matches!(t, Term::Variable { .. }))
                {
                    return Err(InstallError::InvalidBinding(*id));
                }
                let atom = corpus.atom(bound.relation, bound.arguments)?;
                result.occurrences.insert(*id, atom.id());
                for (a, t) in arguments.iter().zip(atom.arguments()) {
                    result.occurrences.insert(a.id, t.id());
                }
                atoms.insert(*id, atom);
            }
            Instruction::Rule { id, head, body } => {
                let head = atoms
                    .remove(head)
                    .ok_or(InstallError::UnknownLocal(*head))?;
                let body = body
                    .iter()
                    .map(|literal| {
                        let atom = atoms
                            .remove(&literal.atom)
                            .ok_or(InstallError::UnknownLocal(literal.atom))?;
                        Ok(match literal.polarity {
                            Polarity::Positive => Literal::Positive(atom),
                            Polarity::Negative => Literal::Negative(atom),
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let rule = corpus.add_rule_in(&namespace, head, body)?;
                result.rules.insert(*id, rule);
                result.occurrences.insert(*id, rule.into());
            }
        }
    }
    Ok(result)
}
