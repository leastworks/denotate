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
    /// An explicit experiment stop at a completed admission round. Not cacheable.
    StoppedAfterRound {
        round: usize,
    },
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
    EmptyInputUniverse,
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
    pub profile: crate::Profile,
    pub progress: crate::CheckingProgress,
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
    /// Optional input placement allowances; a cutoff falls back to key order.
    /// Entries bound peak retained metadata; work also consumes max_work.
    pub max_input_order_entries: usize,
    pub max_input_order_work: usize,
    /// Optional whole-component structural splitting. Exhausting these falls
    /// back to ordinary admission; global work and deadlines still apply.
    pub max_structural_split_depth: usize,
    pub max_structural_split_leaves: usize,
    pub max_structural_split_work: usize,
    pub max_structural_split_scoring_work: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            cancellation: Cancellation::default(),
            profile: Default::default(),
            progress: Default::default(),
            max_atoms: 100_000,
            max_rules: 200_000,
            max_dependencies: 1_000_000,
            max_work: 20_000_000,
            timeout: Duration::from_secs(10),
            max_bdd_variables: 10_000,
            max_bdd_nodes: 100_000,
            max_bdd_tasks: 100_000,
            max_condition_nodes: 1_000_000,
            max_input_order_entries: 1_000_000,
            max_input_order_work: 4_000_000,
            max_structural_split_depth: 32,
            max_structural_split_leaves: 64,
            max_structural_split_work: 100_000_000,
            max_structural_split_scoring_work: 1_000_000,
        }
    }
}

pub(crate) struct Budget<'a> {
    pub limits: &'a Limits,
    start: Instant,
    work: usize,
    charges: Option<WorkCharges>,
    structural_split_start: Option<usize>,
    charges_until_clock: usize,
    #[cfg(test)]
    clock: Option<TestClock>,
    #[cfg(any(test, feature = "test-support"))]
    pub profile: Option<PreparationProfile>,
}

// Bounds skipped polling opportunities, not time: one operation can be long.
const DEADLINE_POLL_CHARGES: usize = 256;

#[cfg(test)]
#[derive(Default)]
struct TestClock {
    elapsed: Duration,
    reads: std::cell::Cell<usize>,
    readings: Vec<Duration>,
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
            structural_split_start: None,
            charges_until_clock: 0,
            #[cfg(test)]
            clock: None,
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
        self.limits.progress.failure(error);
        self.record_failure(error);
    }
    /// Admission emits its own recoverable-skip event, not a stopped query.
    pub(crate) fn record_failure(&mut self, error: &CheckError) {
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
    /// Diagnostic work has its own clock. Preserve all elapsed checker time,
    /// including on errors; cancellation is checked by both budgets.
    pub(crate) fn excluding_time<T>(&mut self, run: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = run();
        self.exclude_elapsed(start.elapsed());
        result
    }
    fn exclude_elapsed(&mut self, elapsed: Duration) {
        self.start += elapsed;
    }
    pub fn remaining(&self) -> usize {
        let global = self.limits.max_work.saturating_sub(self.work);
        self.structural_split_start.map_or(global, |start| {
            global.min(
                self.limits
                    .max_structural_split_work
                    .saturating_sub(self.work - start),
            )
        })
    }
    /// A preflight can stop before consuming its allowance. Preserve which
    /// budget bounded it; only the global one may stop admission. Ties are global.
    pub(crate) fn work_exhaustion(&self, phase: &'static str) -> CheckError {
        if self.remaining() < self.limits.max_work.saturating_sub(self.work) {
            CheckError::limit(
                "structural split",
                "structural split work",
                self.limits.max_structural_split_work,
                None,
            )
            .in_phase("structural split", Some(phase))
        } else {
            CheckError::limit(phase, "work", self.limits.max_work, None)
        }
    }
    pub fn used(&self) -> usize {
        self.work
    }
    /// Charge all nested search, evaluation and staging work to the existing
    /// query, with an additional optional-search allowance. Always restore it
    /// before fallback, including on errors. No second deadline or receipt.
    pub(crate) fn structural_split<T>(
        &mut self,
        run: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let previous = self.structural_split_start.replace(self.work);
        let result = run(self);
        self.structural_split_start = previous;
        result
    }
    pub fn check(&self, phase: &'static str) -> Result<()> {
        self.limits.cancellation.check()?;
        if self.elapsed() >= self.limits.timeout {
            let error = CheckError::deadline(phase, self.limits.timeout);
            self.limits.progress.failure(&error);
            return Err(error);
        }
        Ok(())
    }
    fn elapsed(&self) -> Duration {
        #[cfg(test)]
        if let Some(clock) = &self.clock {
            let read = clock.reads.get();
            clock.reads.set(read + 1);
            return clock.readings.get(read).copied().unwrap_or(clock.elapsed);
        }
        self.start.elapsed()
    }
    pub fn charge(&mut self, amount: usize, phase: &'static str) -> Result<()> {
        if amount == 0 || self.charges_until_clock == 0 {
            self.check(phase)?;
            self.charges_until_clock = DEADLINE_POLL_CHARGES - 1;
        } else {
            self.limits.cancellation.check()?;
            self.charges_until_clock -= 1;
        }
        if amount > self.limits.max_work.saturating_sub(self.work) {
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
            let error = CheckError::limit(
                phase,
                "work",
                self.limits.max_work,
                self.work.checked_add(amount),
            );
            self.limits.progress.failure(&error);
            return Err(error);
        }
        if let Some(start) = self.structural_split_start {
            let used = self.work - start;
            let limit = self.limits.max_structural_split_work;
            if amount > limit.saturating_sub(used) {
                return Err(CheckError::limit(
                    "structural split",
                    "structural split work",
                    limit,
                    used.checked_add(amount),
                )
                .in_phase("structural split", Some(phase)));
            }
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

#[cfg(test)]
mod diagnostic_clock_tests {
    use super::*;
    #[test]
    fn boolean_boundaries_read_deadlines_even_after_failed_operations() {
        use crate::test_support::rewrites::{atom, rel};
        let mut c = denotate_ir::Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let defaults = Limits::default();
        let p = crate::GroundProgram::prepare(&c, &crate::Domains::new(), &defaults).unwrap();
        let ctx = p.condition_context(&defaults).unwrap();
        let a = ctx.input(&atom(i), &defaults).unwrap();
        let b = ctx.input(&atom(j), &defaults).unwrap();
        for (tasks, nodes, reads_before_expiry, phase) in [
            (0, 100, 0, "BDD operation"),   // start
            (0, 100, 2, "BDD preflight"),   // failed preflight
            (100, 100, 2, "BDD operation"), // successful preflight
            (100, 3, 3, "BDD operation"),   // failed result construction
            (100, 100, 3, "BDD operation"), // successful result construction
        ] {
            let limits = Limits {
                max_bdd_tasks: tasks,
                max_bdd_nodes: nodes,
                ..defaults.clone()
            };
            let mut budget = Budget::new(&limits);
            budget.charges_until_clock = DEADLINE_POLL_CHARGES - 1;
            budget.clock = Some(TestClock {
                elapsed: limits.timeout,
                readings: vec![Duration::ZERO; reads_before_expiry],
                ..TestClock::default()
            });
            assert!(
                matches!(ctx.apply(&a, &b, biodivine_lib_bdd::op_function::and, &mut budget),
                Err(CheckError::Deadline { phase: actual, .. }) if actual == phase)
            );
        }
    }
    #[test]
    fn deadline_is_read_on_schedule_and_at_explicit_boundaries() {
        let limits = Limits::default();
        let mut budget = Budget::tracked(&limits);
        budget.clock = Some(TestClock::default());
        budget.tick("first").unwrap();
        assert_eq!(budget.clock.as_ref().unwrap().reads.get(), 1);
        budget.clock.as_mut().unwrap().elapsed = limits.timeout;
        for _ in 1..DEADLINE_POLL_CHARGES {
            budget.tick("between polls").unwrap();
        }
        assert_eq!(budget.clock.as_ref().unwrap().reads.get(), 1);
        assert!(matches!(
            budget.tick("scheduled"),
            Err(CheckError::Deadline {
                phase: "scheduled",
                ..
            })
        ));
        assert_eq!(budget.clock.as_ref().unwrap().reads.get(), 2);
        assert_eq!(budget.used(), DEADLINE_POLL_CHARGES);
        assert_eq!(budget.snapshot().work, DEADLINE_POLL_CHARGES);

        // Explicit checks and zero-work charges never wait for that schedule.
        budget.clock.as_mut().unwrap().elapsed = Duration::ZERO;
        budget.tick("restart").unwrap();
        budget.clock.as_mut().unwrap().elapsed = limits.timeout;
        assert!(matches!(
            budget.check("boundary"),
            Err(CheckError::Deadline {
                phase: "boundary",
                ..
            })
        ));
        assert!(matches!(
            budget.charge(0, "zero"),
            Err(CheckError::Deadline { phase: "zero", .. })
        ));
    }

    #[test]
    fn cancellation_and_work_limits_do_not_wait_for_a_clock_poll() {
        let limits = Limits {
            max_work: 1,
            ..Limits::default()
        };
        let mut budget = Budget::tracked(&limits);
        budget.clock = Some(TestClock::default());
        budget.tick("first").unwrap();
        assert!(matches!(
            budget.tick("work"),
            Err(CheckError::LimitExceeded {
                resource: "work",
                ..
            })
        ));
        assert_eq!(budget.clock.as_ref().unwrap().reads.get(), 1);
        assert_eq!(budget.snapshot().rejected_work["work"], 1);
        limits.cancellation.cancel();
        assert!(matches!(budget.tick("cancel"), Err(CheckError::Cancelled)));
        assert_eq!(budget.clock.as_ref().unwrap().reads.get(), 1);
    }

    #[test]
    fn exclusion_preserves_spent_time_and_never_resets_a_deadline() {
        let limits = Limits {
            timeout: Duration::from_secs(30),
            ..Limits::default()
        };
        let mut budget = Budget::new(&limits);
        // Simulate 10 seconds of admission and 100 of diagnosis. Excluding the
        // latter must permit more admission, without erasing the former.
        let now = Instant::now();
        budget.start = now - Duration::from_secs(110);
        budget.exclude_elapsed(Duration::from_secs(100));
        assert_eq!(budget.start, now - Duration::from_secs(10));
        budget.check("admission").unwrap();
        budget.start -= Duration::from_secs(21);
        budget.excluding_time(|| ());
        assert!(matches!(
            budget.check("admission"),
            Err(CheckError::Deadline { .. })
        ));
    }
}
