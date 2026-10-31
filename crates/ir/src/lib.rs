//! Relational construction IR. No parser, editor, evaluator or solver dependency.
//!
//! Construction errors describe invalid IR supplied by a caller. They are not
//! diagnostics to publish against a DSL user's source. Source attribution lives
//! separately in [`Provenance`], keyed by occurrences rather than semantic values.

mod assumptions;
mod ids;
mod input_domains;
pub mod installation;
mod keys;
mod model;
mod namespace;
mod provenance;

pub use ids::*;
pub use keys::*;
pub use model::*;
pub use namespace::*;
pub use provenance::*;
