use crate::GroundAtom;
use denotate_ir::{ConstantId, SortId};
use std::{
    fmt,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    InvalidDomain {
        sort: SortId,
        reason: &'static str,
    },
    ConstantOutsideDomain(ConstantId),
    InvalidObservation(GroundAtom),
    UnknownAtom(GroundAtom),
    LimitExceeded {
        phase: &'static str,
        resource: &'static str,
    },
    Internal(&'static str),
}
impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Checker: {self:?}")
    }
}
impl std::error::Error for CheckError {}

pub(crate) type Result<T> = std::result::Result<T, CheckError>;

/// Per prepare/evaluate call. Limits cover construction and graph work too.
/// Exceeding a limit returns no partial successful result. Deadlines are checked
/// cooperatively between work items, not a promise of hard real-time preemption.
#[derive(Debug, Clone)]
pub struct Limits {
    pub max_atoms: usize,
    pub max_rules: usize,
    pub max_dependencies: usize,
    pub max_work: usize,
    pub timeout: Duration,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_atoms: 100_000,
            max_rules: 200_000,
            max_dependencies: 1_000_000,
            max_work: 20_000_000,
            timeout: Duration::from_secs(10),
        }
    }
}

pub(crate) struct Budget<'a> {
    pub limits: &'a Limits,
    start: Instant,
    work: usize,
}
impl<'a> Budget<'a> {
    pub fn new(limits: &'a Limits) -> Self {
        Self {
            limits,
            start: Instant::now(),
            work: 0,
        }
    }
    pub fn tick(&mut self, phase: &'static str) -> Result<()> {
        if self.start.elapsed() >= self.limits.timeout {
            return Err(CheckError::LimitExceeded {
                phase,
                resource: "time",
            });
        }
        if self.work >= self.limits.max_work {
            return Err(CheckError::LimitExceeded {
                phase,
                resource: "work",
            });
        }
        self.work += 1;
        Ok(())
    }
    pub fn room(
        &mut self,
        count: usize,
        limit: usize,
        phase: &'static str,
        resource: &'static str,
    ) -> Result<()> {
        self.tick(phase)?;
        if count >= limit {
            return Err(CheckError::LimitExceeded { phase, resource });
        }
        Ok(())
    }
}
