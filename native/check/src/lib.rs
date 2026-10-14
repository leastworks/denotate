//! Finite grounding, BDD-backed checking and replayed findings (slices 3a/b/d).
//! No discharge or observation-specific pruning. Frontends own presentation.

mod boolean;
mod contracts;
mod evaluate;
mod findings;
mod graph;
mod ground;
mod limits;
mod symbolic;

pub use boolean::*;
pub use contracts::*;
pub use evaluate::*;
pub use findings::*;
pub use graph::*;
pub use ground::*;
pub use limits::*;
pub use symbolic::*;

// Compile fixtures as unit tests so the Cartesian oracle stays test-only,
// without a production API or feature exposing the obsolete grounder.
#[cfg(test)]
mod tests;
