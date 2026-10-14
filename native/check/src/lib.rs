//! Finite grounding, concrete replay and BDD-backed checking (slices 3a-3b).
//! No discharge, observation-specific pruning or diagnostic presentation.

mod boolean;
mod contracts;
mod evaluate;
mod graph;
mod ground;
mod limits;
mod symbolic;

pub use boolean::*;
pub use contracts::*;
pub use evaluate::*;
pub use graph::*;
pub use ground::*;
pub use limits::*;
pub use symbolic::*;

// Compile fixtures as unit tests so the Cartesian oracle stays test-only,
// without a production API or feature exposing the obsolete grounder.
#[cfg(test)]
mod tests;
