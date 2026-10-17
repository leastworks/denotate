//! Deterministic relational lowering, not semantic checking. In particular,
//! negative cycles are retained for the checker, not rejected by the frontend.

use crate::{
    ast::*,
    attribution::{Attribution, AttributionError},
    library::MappingLibrary,
};
use denotate_ir::*;
use std::fmt;

pub mod assembly;
pub mod incremental;
pub mod projection;
pub mod recipe;
pub mod semantic;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
    UnknownName {
        name: String,
        expected: Kind,
    },
    WrongKind {
        name: String,
        expected: Kind,
        found: Kind,
    },
    DuplicateDeclaration {
        name: String,
        kind: Kind,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DslDiagnostic {
    pub kind: DiagnosticKind,
    pub span: SourceSpan,
    pub related: Vec<SourceSpan>,
}

#[derive(Debug)]
pub enum LoweringFailure {
    Construction(ConstructionError),
    Provenance(ProvenanceError),
    InvalidAst(String),
    Attribution(AttributionError),
    Recipe(recipe::RecipeError),
}

impl From<recipe::RecipeError> for LoweringFailure {
    fn from(error: recipe::RecipeError) -> Self {
        Self::Recipe(error)
    }
}

impl From<AttributionError> for LoweringFailure {
    fn from(error: AttributionError) -> Self {
        Self::Attribution(error)
    }
}

impl From<ConstructionError> for LoweringFailure {
    fn from(error: ConstructionError) -> Self {
        Self::Construction(error)
    }
}
impl From<ProvenanceError> for LoweringFailure {
    fn from(error: ProvenanceError) -> Self {
        Self::Provenance(error)
    }
}
impl fmt::Display for LoweringFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InputMapping lowering failed: {self:?}")
    }
}
impl std::error::Error for LoweringFailure {}

pub struct LoweredProgram {
    pub corpus: Corpus,
    pub library: MappingLibrary,
    pub attribution: Attribution,
}

pub enum LoweringOutcome {
    Lowered(LoweredProgram),
    UserErrors(Vec<DslDiagnostic>),
}

type Result<T> = std::result::Result<T, LoweringFailure>;

/// Uncached pipeline using the same normalizer as the cached path. Names must
/// be valid before assembly; source locations are rebuilt for this snapshot.
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
        .map(|s| recipe::Recipe::lower(s.form.clone()))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    Ok(LoweringOutcome::Lowered(assembly::assemble(
        &projection,
        &recipes,
        sources,
    )?))
}
