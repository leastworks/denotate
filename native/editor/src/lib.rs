//! Language-independent editor mechanisms. Frontends own grammars, semantics,
//! workspace policy and presentation.
pub mod checking;
mod document;
pub mod presentation;
mod synchronization;
pub mod test_support;
pub mod transport;
pub mod workspace_edit;

pub use document::{parser, Document};
pub use synchronization::Documents;
