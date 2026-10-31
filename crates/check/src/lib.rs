//! Finite grounding, conservative rewrites, BDD checking and replayed findings.
//! Observation certificates are scoped to one input snapshot. Frontends own presentation.

mod accounting;
mod assumptions;
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
mod local;
mod request;
mod rewrite;
mod symbolic;
mod upper_bounds;

pub use accounting::*;
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
pub use local::*;
pub use request::*;
pub use rewrite::*;
pub use symbolic::*;
pub use upper_bounds::ComponentUpperBounds;

// Generic oracles remain here; frontend acceptance tests use the opt-in test support.
#[cfg(test)]
mod tests;
#[cfg(test)]
extern crate self as denotate_check;

#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub mod test_support;

mod emptiness;
pub use emptiness::{
    Attribution, EMPTINESS_EXAMPLE_LIMIT, EmptinessReport, EmptinessResult, EmptinessSummary,
    PresenceExample,
};
mod coverage;
pub use coverage::{CoverageExample, CoverageReport, CoverageResult, CoverageSummary};

mod notices;
pub use notices::*;
