//! Language-independent editor mechanisms. Frontends own grammars, semantics,
//! workspace policy and presentation.
pub mod checking;
pub mod checking_server;
mod document;
pub mod lifecycle;
pub mod presentation;
pub mod publication;
mod synchronization;
pub mod test_support;
pub mod transport;
pub mod workspace_edit;

pub use document::{parser, Document};
pub use synchronization::Documents;
