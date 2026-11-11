use crate::{
    DeterministicLimits, GroundAtom, QueryKey, ResourceKey, WorkCharges, WorkReceipt, WorkReceipts,
};
use denotate_ir::{ConstantId, SortId};
use std::{
    fmt,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

/// Diagnostic context only. Counts describe the checked demand, including a
/// rejected addition, not the eventual size of a completed program. Unknown
/// solver counts are omitted. Deadline limits are milliseconds; no timings are
/// retained here or used in semantic equality.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LimitDetails {
    pub subphase: Option<&'static str>,
    pub limit: Option<usize>,
    pub observed: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    Keys(denotate_ir::KeyError),
    Construction(denotate_ir::ConstructionError),
    /// Superseded work, not a resource limit or a semantic result.
    Cancelled,
    Deadline {
        phase: &'static str,
        details: LimitDetails,
    },
    InvalidRequest(&'static str),
    /// A selected restriction depends on a negative cycle before admission.
    InvalidAssumptionCone {
        relation: denotate_ir::RelationKey,
        cycles: Vec<crate::AssumptionCycle>,
    },
    /// Low-level property queries cannot report vacuous proofs. Request checking
    /// represents this as an inconsistent context with no obligation results.
    InconsistentAssumptions,
    Receipts(crate::ReceiptError),
    InvalidDomain {
        sort: SortId,
        reason: &'static str,
    },
    ConstantOutsideDomain(ConstantId),
    InvalidObservation(GroundAtom),
    InvalidInputGroup(&'static str),
    UnknownAtom(GroundAtom),
    OutsideReplay(GroundAtom),
    ForeignCondition,
    LimitExceeded {
        phase: &'static str,
        resource: &'static str,
        details: LimitDetails,
    },
    Internal(&'static str),
}
impl CheckError {
    pub fn limit(
        phase: &'static str,
        resource: &'static str,
        limit: usize,
        observed: Option<usize>,
    ) -> Self {
        Self::LimitExceeded {
            phase,
            resource,
            details: LimitDetails {
                limit: Some(limit),
                observed,
                subphase: None,
            },
        }
    }
    pub fn deadline(phase: &'static str, timeout: Duration) -> Self {
        Self::Deadline {
            phase,
            details: LimitDetails {
                limit: timeout.as_millis().try_into().ok(),
                ..Default::default()
            },
        }
    }
    /// Keep an enclosing operation's established phase while preserving where
    /// within it the failure happened. This never changes the failure kind.
    pub(crate) fn in_phase(mut self, outer: &'static str, subphase: Option<&'static str>) -> Self {
        match &mut self {
            Self::LimitExceeded { phase, details, .. } | Self::Deadline { phase, details } => {
                details.subphase = subphase
                    .or(details.subphase)
                    .or_else(|| (*phase != outer).then_some(*phase));
                *phase = outer;
            }
            _ => {}
        }
        self
    }
}
impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Checker: {self:?}")
    }
}
impl std::error::Error for CheckError {}

pub(crate) type Result<T> = std::result::Result<T, CheckError>;

/// One-way, per-run cancellation. Clones refer to the same request; a new run
/// gets a fresh token. Cancellation does not interrupt a BDD operation mid-call.
#[derive(Debug, Clone, Default)]
pub struct Cancellation(Arc<AtomicBool>);
impl Cancellation {
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }
    pub fn check(&self) -> Result<()> {
        if self.0.load(Ordering::Relaxed) {
            Err(CheckError::Cancelled)
        } else {
            Ok(())
        }
    }
}

/// Per checker operation, including preparation, evaluation and Boolean queries.
/// Low-level operations return LimitExceeded; reporting APIs preserve completed
/// scopes and label unfinished work Inconclusive. Deadlines are checked
/// cooperatively between work items, not a promise of hard real-time preemption.
#[derive(Debug, Clone)]
pub struct Limits {
    pub cancellation: Cancellation,
    pub max_atoms: usize,
    pub max_rules: usize,
    pub max_dependencies: usize,
    pub max_work: usize,
    pub timeout: Duration,
    pub max_bdd_variables: usize,
    pub max_bdd_nodes: usize,
    pub max_bdd_tasks: usize,
    /// Sum of BDD sizes retained in one query (or a whole property report in
    /// the historical low-level API). Symbolic evaluation is one shared query.
    /// Counts shared conditions conservatively, not exact heap usage.
    pub max_condition_nodes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            cancellation: Cancellation::default(),
            max_atoms: 100_000,
            max_rules: 200_000,
            max_dependencies: 1_000_000,
            max_work: 20_000_000,
            timeout: Duration::from_secs(10),
            max_bdd_variables: 10_000,
            max_bdd_nodes: 100_000,
            max_bdd_tasks: 100_000,
            max_condition_nodes: 1_000_000,
        }
    }
}

pub(crate) struct Budget<'a> {
    pub limits: &'a Limits,
    start: Instant,
    work: usize,
    charges: Option<WorkCharges>,
    #[cfg(any(test, feature = "test-support"))]
    pub profile: Option<PreparationProfile>,
}

/// Diagnostic-only counters. Timed public-path samples leave this disabled.
#[cfg(any(test, feature = "test-support"))]
#[derive(Debug)]
pub struct PreparationProfile {
    pub work: std::collections::BTreeMap<&'static str, usize>,
    pub calls: std::collections::BTreeMap<&'static str, usize>,
    pub segments_ns: std::collections::BTreeMap<&'static str, u128>,
    last: Instant,
}
impl<'a> Budget<'a> {
    pub fn new(limits: &'a Limits) -> Self {
        Self {
            limits,
            start: Instant::now(),
            work: 0,
            charges: None,
            #[cfg(any(test, feature = "test-support"))]
            profile: None,
        }
    }
    pub fn tracked(limits: &'a Limits) -> Self {
        let mut budget = Self::new(limits);
        budget.charges = Some(WorkCharges::default());
        budget
    }
    pub(crate) fn snapshot(&self) -> WorkCharges {
        self.charges.clone().expect("tracked budget")
    }
    pub(crate) fn resume(limits: &'a Limits, charges: WorkCharges) -> Self {
        Self {
            work: charges.work,
            charges: Some(charges),
            ..Self::tracked(limits)
        }
    }
    pub fn observe(&mut self, phase: &str, resource: &str, count: usize) {
        if let Some(charges) = &mut self.charges {
            let peak = charges
                .resource_peaks
                .entry(ResourceKey {
                    phase: phase.into(),
                    resource: resource.into(),
                })
                .or_default();
            *peak = (*peak).max(count);
        }
    }
    pub fn failure(&mut self, error: &CheckError) {
        if let (
            Some(charges),
            CheckError::LimitExceeded {
                phase, resource, ..
            },
        ) = (&mut self.charges, error)
        {
            charges.exhausted.insert(ResourceKey {
                phase: (*phase).into(),
                resource: (*resource).into(),
            });
        }
    }
    pub fn record(
        &mut self,
        receipts: &mut WorkReceipts,
        key: QueryKey,
        dependencies: impl IntoIterator<Item = QueryKey>,
    ) -> Result<()> {
        #[cfg(any(test, feature = "test-support"))]
        crate::accounting::test_trace(&key);
        let own = self
            .charges
            .take()
            .ok_or(CheckError::Internal("untracked query receipt"))?;
        receipts
            .record(
                key,
                WorkReceipt {
                    allowance: DeterministicLimits::from(self.limits),
                    own,
                    dependencies: dependencies.into_iter().collect(),
                },
            )
            .map_err(CheckError::Receipts)
    }
    #[cfg(any(test, feature = "test-support"))]
    pub fn enable_profile(&mut self) {
        self.profile = Some(PreparationProfile {
            work: Default::default(),
            calls: Default::default(),
            segments_ns: Default::default(),
            last: Instant::now(),
        });
    }
    #[cfg(any(test, feature = "test-support"))]
    pub fn mark(&mut self, label: &'static str) {
        if let Some(profile) = &mut self.profile {
            profile
                .segments_ns
                .insert(label, profile.last.elapsed().as_nanos());
            profile.last = Instant::now();
        }
    }
    pub fn tick(&mut self, phase: &'static str) -> Result<()> {
        self.charge(1, phase)
    }
    pub fn remaining(&self) -> usize {
        self.limits.max_work.saturating_sub(self.work)
    }
    pub fn used(&self) -> usize {
        self.work
    }
    pub fn check(&self, phase: &'static str) -> Result<()> {
        self.limits.cancellation.check()?;
        if self.start.elapsed() >= self.limits.timeout {
            return Err(CheckError::deadline(phase, self.limits.timeout));
        }
        Ok(())
    }
    pub fn charge(&mut self, amount: usize, phase: &'static str) -> Result<()> {
        self.check(phase)?;
        if amount > self.remaining() {
            if let Some(charges) = &mut self.charges {
                let rejected = charges.rejected_work.entry(phase.into()).or_default();
                *rejected = rejected
                    .checked_add(amount)
                    .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
                charges.exhausted.insert(ResourceKey {
                    phase: phase.into(),
                    resource: "work".into(),
                });
            }
            return Err(CheckError::limit(
                phase,
                "work",
                self.limits.max_work,
                self.work.checked_add(amount),
            ));
        }
        self.work = self
            .work
            .checked_add(amount)
            .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
        if let Some(charges) = &mut self.charges {
            charges.work = charges
                .work
                .checked_add(amount)
                .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
            let phase_work = charges.by_phase.entry(phase.into()).or_default();
            *phase_work = phase_work
                .checked_add(amount)
                .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
        }
        #[cfg(any(test, feature = "test-support"))]
        if let Some(profile) = &mut self.profile {
            let work = profile.work.entry(phase).or_default();
            *work = work
                .checked_add(amount)
                .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
            let calls = profile.calls.entry(phase).or_default();
            *calls = calls
                .checked_add(1)
                .ok_or(CheckError::Receipts(crate::ReceiptError::Overflow))?;
        }
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
        self.observe(phase, resource, count.saturating_add(1));
        if count >= limit {
            let error = CheckError::limit(phase, resource, limit, count.checked_add(1));
            self.failure(&error);
            return Err(error);
        }
        Ok(())
    }
}

impl From<denotate_ir::ConstructionError> for CheckError {
    fn from(e: denotate_ir::ConstructionError) -> Self {
        Self::Construction(e)
    }
}
impl From<denotate_ir::KeyError> for CheckError {
    fn from(e: denotate_ir::KeyError) -> Self {
        Self::Keys(e)
    }
}
