//! Fresh and memoized checker drivers; snapshot presentation always remains fresh.
use denotate_check::{CheckError, LocalCheckOutcome, OperationalLimits, PreparedCheck};

#[derive(Default)]
pub struct FreshSession;
impl FreshSession {
    pub fn verify<'p>(
        &mut self,
        prepared: &'p PreparedCheck<'_>,
        operations: &OperationalLimits,
    ) -> Result<LocalCheckOutcome<'p>, CheckError> {
        prepared.verify_local(operations)
    }
}
#[cfg(test)]
mod tests;

mod cache;
pub use cache::*;

mod retention;

mod plans;
pub use plans::PlanStats;

mod grounding;
pub use grounding::GroundingStats;

mod fixed;
pub use fixed::FixedStats;

pub mod profiling;
