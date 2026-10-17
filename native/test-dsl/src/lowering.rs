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
/// 5.3a candidate pipeline; the server still uses the existing recipes.
pub mod shared;

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

/// Uncached reference pipeline. Names must be valid before any IR
/// is assembled; all source-dependent locations are rebuilt for this snapshot.
pub fn lower(program: &Program, sources: &Sources) -> Result<LoweringOutcome> {
    let projection = projection::project(program, sources)?;
    let keys = projection.keys();
    let diagnostics = semantic::validate(&keys)?;
    if !diagnostics.is_empty() {
        return Ok(LoweringOutcome::UserErrors(
            projection.diagnostics(&diagnostics)?,
        ));
    }
    let recipes: Vec<_> = keys
        .iter()
        .map(|key| recipe::Recipe::lower(key.form.clone()))
        .collect();
    Ok(LoweringOutcome::Lowered(assembly::assemble(
        &projection,
        &recipes,
        sources,
    )?))
}
