//! Finite grounding, conservative rewrites, BDD checking and replayed findings.
//! Observation certificates are scoped to one input snapshot. Frontends own presentation.

mod accounting;
mod admission_dump;
pub use admission_dump::*;
mod admission_progress;
pub use admission_progress::{
    AdmissionAttempts, AdmissionComponent, AdmissionConditionPool, AdmissionObserver,
    AdmissionPhase, AdmissionProgress, AdmissionStorage, GuardedAttempt, GuardedSplitProgress,
    SplitReplacementSizes,
};
mod admission_scope;
mod admission_skips;
mod admission_storage;
mod component_passes;
pub use admission_skips::{AdmissionAttemptKind, AdmissionSkip};
mod assumption_validation;
mod assumptions;
mod boolean;
mod certification;
mod checking_progress;
pub use checking_progress::*;
mod completion;
mod contracts;
mod evaluate;
mod findings;
mod graph;
mod ground;
mod keys;
mod limits;
mod profile;
pub use profile::*;
mod guarded_bounds;
mod guarded_preparation;
mod guarded_settlement;
pub use guarded_bounds::{
    DeadReason as GuardedDeadReason, GuardedBounds, GuardedCone, GuardedProducer,
    Pruning as GuardedPruning,
};
mod local;
mod request;
mod rewrite;
pub use guarded_settlement::{
    GuardedCertificate, GuardedSettlementProof, GuardedSettlementStep, JointCertificate,
};
mod settled_expression;
mod structural;
mod structural_split;
pub use settled_expression::{SettledExpression, SettledReplacement};
mod sat_probe;
pub use sat_probe::{
    CandidateProbeCounts, CandidateProbeLimits, CandidateProbePair, CandidateProbeReport,
    SatExistenceAnswer, SatExistenceReport, SatProbeAnswer, SatProbeEvent, SatProbeLimits,
    SatProbeObserver, SatProbePair, SatProbeReport,
};
mod symbolic;
pub use structural::{
    StructuralCertificate, StructuralProof, StructuralReason, StructuralSettlement,
};
mod upper_bounds;

pub use accounting::*;
pub use assumption_validation::*;
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
    Attribution, EMPTINESS_EXAMPLE_LIMIT, EmptinessExamples, EmptinessReport, EmptinessResult,
    EmptinessSummary, PresenceExample,
};
mod coverage;
pub use coverage::{CoverageExample, CoverageReport, CoverageResult, CoverageSummary};

mod notices;
pub use notices::*;

mod input_order;
pub use input_order::{InputOrder, InputOrderReport};

mod implied_guard;
pub use implied_guard::{ImpliedGuardPremise, ImpliedGuardProof};
