//! Shared interpretation of checked evidence. No editor protocol, source language,
//! filesystem, scheduling or source-edit authority lives here.
mod assumptions;
mod evidence;
mod identity;
mod locations;
mod rewrites;
pub use assumptions::*;
pub use evidence::*;
pub use identity::*;
pub use locations::*;
pub use rewrites::*;

#[derive(Debug)]
pub enum Error {
    InvalidFinding(&'static str),
    Provenance(denotate_ir::ProvenanceError),
    Keys(denotate_ir::KeyError),
}
impl From<denotate_ir::ProvenanceError> for Error {
    fn from(e: denotate_ir::ProvenanceError) -> Self {
        Self::Provenance(e)
    }
}
impl From<denotate_ir::KeyError> for Error {
    fn from(e: denotate_ir::KeyError) -> Self {
        Self::Keys(e)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Creator-facing presentation failure: {self:?}")
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
