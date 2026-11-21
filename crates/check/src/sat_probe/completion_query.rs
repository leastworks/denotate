//! Experimental completion queries, separate from stable-model search.
//! No least-model folding, reduct validation, loop clauses or admission rewrites
//! enter this engine. Interpretations are checked against the original equations.
use super::*;
use denotate_ir::{AssumptionKey, Corpus, RelationKey, SemanticKeys, Semantics, VerificationId};
use existence::{Encoding, encode, world_cone};
use std::sync::Arc;

mod queries;
#[cfg(test)]
mod tests;

/// Limits for one public query, in addition to the ordinary checker limits.
#[derive(Debug, Clone)]
pub struct QueryLimits {
    pub max_solves: usize,
    pub max_solver_polls: usize,
    pub max_conflicts: u64,
    pub max_propagations: u64,
}
impl Default for QueryLimits {
    fn default() -> Self {
        Self {
            max_solves: 128,
            max_solver_polls: 100_000,
            max_conflicts: 100_000,
            max_propagations: 1_000_000,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CompatibilitySource {
    SelectedAssumption(AssumptionKey),
    InputDomain { input: RelationKey },
}
/// Conservative compatibility refusal, not proof that the program has no models.
#[derive(Debug, Clone)]
pub struct CompatibilityIssue {
    pub source: CompatibilitySource,
    pub relation: RelationKey,
    pub recursive_component: Vec<AtomKey>,
}

pub enum Preparation {
    Ready(Engine),
    Unsupported(CompatibilityIssue),
    Inconclusive(Inconclusive),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelScope {
    Classification,
    Processing,
    WholeProgram,
}

/// A completion interpretation, not a finite derivation. Unlisted legal tuples
/// inside the scope have empty definitions and are false. Outside-scope derived
/// atoms are unknown. The complete input observation is retained in every model.
#[derive(Debug, Clone)]
pub struct Model {
    program: Arc<GroundProgram>,
    input_relations: Arc<BTreeSet<RelationId>>,
    members: Option<Arc<BTreeSet<GroundAtom>>>,
    values: Arc<[bool]>,
    scope: ModelScope,
}
impl Model {
    pub fn scope(&self) -> ModelScope {
        self.scope
    }
    pub fn value(&self, atom: &GroundAtom) -> Option<bool> {
        self.program.validate_atom(atom).ok()?;
        if !self.input_relations.contains(&atom.relation)
            && self.members.as_ref().is_some_and(|m| !m.contains(atom))
        {
            return None;
        }
        Some(
            self.program
                .atom_index
                .get(atom)
                .is_some_and(|i| self.values[*i]),
        )
    }
    pub fn observation(&self) -> Observation {
        Observation {
            present: self
                .program
                .inputs
                .iter()
                .filter(|a| self.value(a) == Some(true))
                .cloned()
                .collect(),
            absent: self
                .program
                .inputs
                .iter()
                .filter(|a| self.value(a) == Some(false))
                .cloned()
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Interpretations {
    NoMeaning,
    Unique(Model),
    Multiple {
        first: Model,
        second: Model,
    },
    /// Retain an already validated interpretation if only uniqueness exhausted.
    Inconclusive {
        cause: Inconclusive,
        example: Option<Model>,
    },
}

#[derive(Debug, Clone)]
pub enum ObservationOutcome {
    NotPermitted,
    Rejected,
    Ambiguous {
        first: Model,
        second: Model,
    },
    Accepted {
        classification: Model,
        processing: Interpretations,
    },
    /// No hypothesis: zero models is no meaning, never a rejection.
    WholeProgram(Interpretations),
    Inconclusive {
        cause: Inconclusive,
        example: Option<Model>,
    },
}

#[derive(Debug, Clone)]
pub enum WorldAnswer {
    World(Observation),
    NoWorld,
    Inconclusive(Inconclusive),
}

/// Pins and excluded cubes refer only to input atoms. Omitting a pin leaves that
/// input free. This searches W alone, including worlds with no program meaning.
#[derive(Debug, Clone, Default)]
pub struct WorldQuery {
    pub pins: Vec<(GroundAtom, bool)>,
    pub exclude: Vec<Vec<(GroundAtom, bool)>>,
}

/// Immutable preparation. Each query owns its SAT solver; no learned clauses,
/// partial append or cutoff can contaminate another observation or semantics.
/// Re-preparing is required for edits to H, W, domains, eligibility or rules.
pub struct Engine {
    program: Arc<GroundProgram>,
    cone: Cone,
    world: Cone,
    classification: Option<(Cone, Arc<BTreeSet<GroundAtom>>, usize)>,
    input_relations: Arc<BTreeSet<RelationId>>,
    limits: Limits,
    config: QueryLimits,
}

fn inconclusive(error: CheckError) -> Result<Inconclusive> {
    match error {
        CheckError::Deadline { phase, details } => Ok(Inconclusive {
            phase,
            resource: "deadline",
            details,
        }),
        other => Inconclusive::from_error(other),
    }
}

impl Engine {
    pub fn prepare(
        corpus: &Corpus,
        domains: &Domains,
        keys: &SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        config: QueryLimits,
    ) -> Result<Preparation> {
        let result = Self::prepare_inner(corpus, domains, keys, verification, limits, config);
        match result {
            Ok(p) => Ok(p),
            Err(e) => Ok(Preparation::Inconclusive(inconclusive(e)?)),
        }
    }

    fn prepare_inner(
        corpus: &Corpus,
        domains: &Domains,
        keys: &SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        config: QueryLimits,
    ) -> Result<Preparation> {
        limits.cancellation.check()?;
        let declaration = corpus
            .verification(verification)
            .ok_or(CheckError::InvalidRequest(
                "unknown completion verification",
            ))?;
        if declaration.options.semantics != Semantics::Completion {
            return Err(CheckError::InvalidRequest(
                "completion queries require completion semantics",
            ));
        }
        keys.validate(corpus).map_err(CheckError::Keys)?;
        let mut b = Budget::new(limits);
        // Retain ordinary construction validation. The stronger completion check
        // below is scoped to this verification's selected declarations.
        corpus.input_domain_cone_with(|| b.tick("completion input domains"))?;
        let mut program = GroundProgram::prepare_completion(corpus, domains, &mut b)?;
        for r in corpus.relations() {
            b.tick("completion compatibility")?;
            if let Some(provider) = r.input_domain {
                if let Some(issue) = compatibility(
                    &program,
                    provider,
                    CompatibilitySource::InputDomain {
                        input: keys.relation(r.id).map_err(CheckError::Keys)?.clone(),
                    },
                    keys,
                    &mut b,
                )? {
                    return Ok(Preparation::Unsupported(issue));
                }
            }
        }
        // Only now is least-model evaluation safe for these acyclic providers.
        program.completion_inputs(corpus, &mut b)?;
        for id in &declaration.assumptions {
            let a = corpus.assumption(*id).unwrap();
            if let Some(issue) = compatibility(
                &program,
                a.restriction.relation(),
                CompatibilitySource::SelectedAssumption(
                    keys.assumption(*id).map_err(CheckError::Keys)?.clone(),
                ),
                keys,
                &mut b,
            )? {
                return Ok(Preparation::Unsupported(issue));
            }
        }
        let mut cone = program::original_cone(&program, corpus, verification, &mut b)?;
        let world = world_cone(&cone, false, &mut b)?;
        // Restrictions belong exclusively to W. In particular, definitions
        // omitted from a classification cone must not make W inconsistent.
        cone.groups.clear();
        let classification = if let Some(h) = declaration.options.hypothesis {
            let atom = GroundAtom::new(h, []);
            let closure = program.dependency_cone_with_budget([atom.clone()], &mut b)?;
            let members = Arc::new(closure.facts);
            let mut c = cone.clone();
            c.rules.retain(|r| members.contains(&c.atoms[r.head]));
            let index = program
                .atom_index
                .get(&atom)
                .copied()
                .unwrap_or(cone.atoms.len() + 1);
            Some((c, members, index))
        } else {
            None
        };
        b.check("completion preparation")?;
        Ok(Preparation::Ready(Self {
            program: Arc::new(program),
            cone,
            world,
            classification,
            input_relations: Arc::new(
                corpus
                    .relations()
                    .filter(|r| r.role == denotate_ir::RelationRole::Input)
                    .map(|r| r.id)
                    .collect(),
            ),
            limits: limits.clone(),
            config,
        }))
    }

    /// Ground structure and source occurrences for inspection. Its stable
    /// evaluation/admission methods are not completion-meaning operations.
    pub fn original_program(&self) -> &GroundProgram {
        &self.program
    }

    fn model(&self, values: Vec<bool>, scope: ModelScope) -> Model {
        Model {
            program: self.program.clone(),
            input_relations: self.input_relations.clone(),
            members: if scope == ModelScope::Classification {
                Some(self.classification.as_ref().unwrap().1.clone())
            } else {
                None
            },
            values: values.into(),
            scope,
        }
    }
}

fn compatibility(
    p: &GroundProgram,
    relation: RelationId,
    source: CompatibilitySource,
    keys: &SemanticKeys,
    b: &mut Budget<'_>,
) -> Result<Option<CompatibilityIssue>> {
    let mut roots = Vec::new();
    for a in &p.core.atoms {
        b.tick("completion compatibility")?;
        if a.relation == relation {
            roots.push(a.clone());
        }
    }
    let cone = p.dependency_cone_with_budget(roots, b)?;
    for component in &p.components {
        b.tick("completion compatibility")?;
        if component.recursive && cone.components.contains(&component.id) {
            let mut atoms = Vec::new();
            for a in &component.atoms {
                b.tick("completion compatibility")?;
                atoms.push(AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?);
            }
            atoms.sort();
            return Ok(Some(CompatibilityIssue {
                source,
                relation: keys.relation(relation).map_err(CheckError::Keys)?.clone(),
                recursive_component: atoms,
            }));
        }
    }
    Ok(None)
}
