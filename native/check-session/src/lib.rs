//! Fresh checker session boundary. No memoization or editor lifecycle state yet.
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
