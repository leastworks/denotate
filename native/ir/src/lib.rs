//! Relational construction IR. No parser, editor, evaluator or solver dependency.
//!
//! Construction errors describe invalid IR supplied by a caller. They are not
//! diagnostics to publish against a DSL user's source. Source attribution lives
//! separately in [`Provenance`], keyed by occurrences rather than semantic values.

mod ids;
pub mod installation;
mod model;
mod provenance;

pub use ids::*;
pub use model::*;
pub use provenance::*;
