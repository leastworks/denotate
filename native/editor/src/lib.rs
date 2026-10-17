//! Language-independent editor mechanisms. Frontends own grammars, semantics,
//! workspace policy, scheduling and presentation.
mod document;
mod synchronization;
pub mod test_support;
pub mod transport;

pub use document::{parser, Document};
pub use synchronization::Documents;
