//! Experimental completion queries, separate from stable-model search.
//! Required queries use no least-model folding, reduct acceptance, loop clauses or
//! admission rewrites. Interpretations are checked against the original equations;
//! the optional reduct detector reports circular support without changing meaning.
use super::*;
use denotate_ir::{Corpus, SemanticKeys, Semantics, VerificationId};
use existence::{Encoding, encode, world_cone};
use std::sync::Arc;

mod advisory;
mod contracts;
mod providers;
pub use contracts::{AssumptionAmbiguity, AssumptionAnalysis};
pub use providers::{InputDomainFailure, InputDomainIssue};
mod checking;
mod properties;
mod queries;
mod symbolic;
pub use advisory::*;
pub use checking::*;
pub use properties::*;
#[cfg(test)]
mod tests;

/// Limits for one observation query or one symbolic whole-check search, in
/// addition to the ordinary checker limits.
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

pub enum Preparation {
    Ready(Engine),
    InputDomains(Vec<InputDomainIssue>),
    Inconclusive(Inconclusive),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelScope {
    Classification,
    ClassificationWithoutHypothesis,
    Processing,
    WholeProgram,
    Property,
    Assumption,
    InputDomain,
}

/// A completion interpretation, not a finite derivation. Unlisted legal tuples
/// inside the scope are false: no producer survives completion-safe pruning. Outside-scope derived
/// atoms are unknown. Every model retains its input observation and explicitly
/// names unused bounded input relations omitted from that observation.
#[derive(Debug, Clone)]
pub struct Model {
    program: Arc<GroundProgram>,
    input_relations: Arc<BTreeSet<RelationId>>,
    members: Option<Arc<BTreeSet<GroundAtom>>>,
    values: Arc<[bool]>,
    scope: ModelScope,
    omitted_inputs: Arc<BTreeSet<RelationId>>,
}
impl Model {
    /// Original named atoms in this interpretation's scope, including inputs.
    /// Other legal tuples in scope have no surviving producer and are false.
    pub fn interpretation(&self) -> impl Iterator<Item = (&GroundAtom, bool)> {
        self.program
            .core
            .atoms
            .iter()
            .filter_map(|a| self.value(a).map(|v| (a, v)))
    }
    /// None denotes the whole program. Observations include eligible inputs
    /// outside these live cone members, except `omitted_input_relations`.
    pub fn scope_atoms(&self) -> Option<&BTreeSet<GroundAtom>> {
        self.members.as_deref()
    }
    pub fn scope(&self) -> ModelScope {
        self.scope
    }
    pub fn omitted_input_relations(&self) -> &BTreeSet<RelationId> {
        &self.omitted_inputs
    }
    pub fn value(&self, atom: &GroundAtom) -> Option<bool> {
        if self.omitted_inputs.contains(&atom.relation) {
            return None;
        }
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
    NotAnalysed,
    NoMeaning,
    /// One projection onto the selected decision relations; helpers may vary.
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
    UndeterminedAssumptions(Vec<AssumptionAnalysis>),
    NotPermitted,
    /// C has an interpretation, but none satisfying H.
    Rejected {
        without_hypothesis: Model,
    },
    /// Even C without H has no interpretation: a specification failure.
    ClassificationNoMeaning,
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
/// Re-preparing is required for edits to H, W, decisions, domains, eligibility or rules.
pub struct Engine {
    program: Arc<GroundProgram>,
    original: crate::ground::OriginalDependencies,
    assumptions: Vec<contracts::Assumption>,
    ignored_input_domains: Vec<InputDomainIssue>,
    cone: Cone,
    world: Cone,
    classification: Option<(Cone, Arc<BTreeSet<GroundAtom>>, usize)>,
    input_relations: Arc<BTreeSet<RelationId>>,
    limits: Limits,
    config: QueryLimits,
    verification: VerificationId,
    hypothesis: Option<RelationId>,
    decisions: Option<BTreeSet<RelationId>>,
    selection: Vec<(denotate_ir::ObligationId, denotate_ir::Requirement)>,
    notices: BTreeSet<denotate_ir::NoticeId>,
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
        corpus.input_domain_structure_with(|| b.tick("completion input domains"))?;
        let (program, ignored_input_domains) =
            match providers::prepare(corpus, domains, verification, limits, &config, &mut b)? {
                providers::Inputs::Ready(p, ignored) => (p, ignored),
                providers::Inputs::Invalid(issues) => return Ok(Preparation::InputDomains(issues)),
            };
        let mut engine = Self::skeleton(
            corpus,
            domains,
            verification,
            program,
            limits,
            config,
            &mut b,
        )?;
        engine.ignored_input_domains = ignored_input_domains;
        engine.assumptions = contracts::build(&engine, corpus, &mut b)?;
        let cone = &engine.cone;
        let program = &engine.program;
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
        engine.classification = classification;
        Ok(Preparation::Ready(engine))
    }
    fn skeleton(
        corpus: &Corpus,
        domains: &Domains,
        verification: VerificationId,
        program: GroundProgram,
        limits: &Limits,
        config: QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<Self> {
        let declaration = corpus.verification(verification).unwrap();
        let original = crate::ground::OriginalDependencies::new(corpus, domains, b)?;
        let mut cone = program::completion_cone(&program, corpus, verification, b)?;
        let world = world_cone(&cone, false, b)?;
        cone.groups.clear();
        Ok(Self {
            program: Arc::new(program),
            original,
            cone,
            world,
            classification: None,
            assumptions: vec![],
            ignored_input_domains: vec![],
            input_relations: Arc::new(
                corpus
                    .relations()
                    .filter(|r| r.role == denotate_ir::RelationRole::Input)
                    .map(|r| r.id)
                    .collect(),
            ),
            limits: limits.clone(),
            config,
            verification,
            hypothesis: declaration.options.hypothesis,
            decisions: declaration.options.decisions.clone(),
            selection: declaration
                .obligations
                .iter()
                .map(|id| (*id, corpus.obligation(*id).unwrap().requirement.clone()))
                .collect(),
            notices: declaration.notices.iter().copied().collect(),
        })
    }

    /// Completion-equivalent ground instances and original source occurrences.
    /// Impossible producers are omitted; the resulting dependency scopes are
    /// frozen before W, H or decision selection. Its stable
    /// evaluation/admission methods are not completion-meaning operations.
    pub fn original_program(&self) -> &GroundProgram {
        &self.program
    }

    fn decision(&self, atom: &GroundAtom) -> bool {
        self.decisions
            .as_ref()
            .is_none_or(|relations| relations.contains(&atom.relation))
    }

    fn model(&self, values: Vec<bool>, scope: ModelScope) -> Model {
        Model {
            program: self.program.clone(),
            input_relations: self.input_relations.clone(),
            members: if matches!(
                scope,
                ModelScope::Classification | ModelScope::ClassificationWithoutHypothesis
            ) {
                Some(self.classification.as_ref().unwrap().1.clone())
            } else {
                None
            },
            values: values.into(),
            scope,
            omitted_inputs: if scope == ModelScope::InputDomain {
                // Static provider interpretations precede the runtime universe.
                // They cannot claim any runtime input tuple is absent.
                self.input_relations.clone()
            } else {
                Arc::new(self.ignored_input_domains.iter().map(|i| i.input).collect())
            },
        }
    }
}
