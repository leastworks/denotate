//! Finite grounding, local stratification and concrete replay (slice 3a).
//! No solver, obligation checking, discharge or observation-specific pruning.

mod evaluate;
mod graph;
mod ground;
mod limits;

pub use evaluate::*;
pub use graph::*;
pub use ground::*;
pub use limits::*;

// Compile fixtures as unit tests so the Cartesian oracle stays test-only,
// without a production API or feature exposing the obsolete grounder.
#[cfg(test)]
mod tests;
