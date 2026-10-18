//! Finite grounding, conservative rewrites, BDD checking and replayed findings.
//! Observation certificates are scoped to one input snapshot. Frontends own presentation.

mod boolean;
mod certification;
mod completion;
mod contracts;
mod evaluate;
mod findings;
mod graph;
mod ground;
mod keys;
mod limits;
mod request;
mod rewrite;
mod symbolic;
mod upper_bounds;

pub use boolean::*;
pub use certification::*;
pub use completion::*;
pub use contracts::*;
pub use evaluate::*;
pub use findings::*;
pub use graph::*;
pub use ground::*;
pub use keys::*;
pub use limits::*;
pub use request::*;
pub use rewrite::*;
pub use symbolic::*;
pub use upper_bounds::ComponentUpperBounds;

// Compile fixtures as unit tests so the Cartesian oracle stays test-only,
// without a production API or feature exposing the obsolete grounder.
#[cfg(test)]
mod tests;
#[cfg(test)]
extern crate self as denotate_check;
