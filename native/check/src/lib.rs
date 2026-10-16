//! Finite grounding, conservative rewrites, BDD checking and replayed findings.
//! No observation-specific admission. Frontends own presentation.

mod boolean;
mod completion;
mod contracts;
mod evaluate;
mod findings;
mod graph;
mod ground;
mod limits;
mod rewrite;
mod symbolic;
mod upper_bounds;

pub use boolean::*;
pub use completion::*;
pub use contracts::*;
pub use evaluate::*;
pub use findings::*;
pub use graph::*;
pub use ground::*;
pub use limits::*;
pub use rewrite::*;
pub use symbolic::*;
pub use upper_bounds::ComponentUpperBounds;

// Compile fixtures as unit tests so the Cartesian oracle stays test-only,
// without a production API or feature exposing the obsolete grounder.
#[cfg(test)]
mod tests;
#[cfg(test)]
extern crate self as denotate_check;
