//! A shared accounting ledger, never a shared proof cache. Trial cones and proofs
//! are owned by the candidate child; only selected partitions publish findings.
use super::*;
struct Allowance {
    time: Duration,
    work: usize,
    query: QueryLimits,
}
pub(in crate::sat_probe::completion_query) struct TrialPool {
    slots: BTreeMap<Bucket, Allowance>,
    elapsed: Duration,
    attempts: usize,
    proved: usize,
    released: Duration,
    available_released: Duration,
}
impl TrialPool {
    pub(super) fn new(reservations: &Reservations, e: &Engine) -> Self {
        let n = reservations
            .slots
            .keys()
            .filter(|(s, _)| *s != "property")
            .count();
        let mut slots = BTreeMap::new();
        for key in reservations.slots.keys() {
            if key.0 == "property" {
                continue;
            }
            slots.insert(
                *key,
                Allowance {
                    time: Duration::ZERO,
                    work: e.limits.max_work / 4 / n,
                    query: QueryLimits {
                        max_solves: e.config.max_solves / n,
                        max_solver_polls: e.config.max_solver_polls / n,
                        max_conflicts: e.config.max_conflicts / n as u64,
                        max_propagations: e.config.max_propagations / n as u64,
                    },
                },
            );
        }
        Self {
            slots,
            elapsed: Duration::ZERO,
            attempts: 0,
            proved: 0,
            released: Duration::ZERO,
            available_released: Duration::ZERO,
        }
    }
    /// Credit only an existing ranking allocation, once per ranking pass, never
    /// per child or candidate. Logical counters are not replenished.
    pub(in crate::sat_probe::completion_query) fn fund_ranking(
        &mut self,
        scope: &'static str,
        time: Duration,
    ) {
        let n = self.slots.keys().filter(|(s, _)| *s == scope).count();
        if n == 0 {
            return;
        }
        for ((s, _), slot) in &mut self.slots {
            if *s == scope {
                slot.time += time / n as u32;
            }
        }
    }
    pub(super) fn release(&mut self, time: Duration) {
        self.available_released += time;
    }
    /// Root redistribution has priority. Only genuinely leftover time can
    /// enlarge ranking, within the question's existing deadline.
    pub(in crate::sat_probe::completion_query) fn take_released(
        &mut self,
        max: Duration,
    ) -> Duration {
        let time = self.available_released.min(max);
        self.available_released -= time;
        self.released += time;
        time
    }
    pub(in crate::sat_probe::completion_query) fn available(
        &self,
        scope: &'static str,
        context: PruningContext,
    ) -> bool {
        self.slots.contains_key(&(scope, context)) && self.cutoff(scope, context).is_none()
    }
    pub(in crate::sat_probe::completion_query) fn cutoff(
        &self,
        scope: &'static str,
        context: PruningContext,
    ) -> Option<CheckError> {
        let s = self.slots.get(&(scope, context))?;
        let phase = if context == PruningContext::World {
            "completion branch pruning W"
        } else {
            "completion branch pruning W+H"
        };
        if s.time.is_zero() {
            return Some(CheckError::deadline(phase, Duration::ZERO));
        }
        for (empty, resource) in [
            (s.work == 0, "remaining trial work"),
            (s.query.max_solves == 0, "remaining trial solves"),
            (s.query.max_solver_polls == 0, "remaining trial polls"),
            (s.query.max_conflicts == 0, "remaining trial conflicts"),
            (
                s.query.max_propagations == 0,
                "remaining trial propagations",
            ),
        ] {
            if empty {
                return Some(CheckError::limit(phase, resource, 0, None));
            }
        }
        None
    }
    pub(in crate::sat_probe::completion_query) fn summarize(&self, report: &mut PruningReport) {
        report.trial_elapsed = self.elapsed;
        report.trial_released = self.released;
        report.trial_attempts = self.attempts;
        report.trial_proved = self.proved;
    }
}
/// Charge the entire attempt, including materialization and propagation, even
/// when discarded or interrupted. Only this accounting ledger is shared.
pub(in crate::sat_probe::completion_query) fn trial<T>(
    e: &Engine,
    scope: &'static str,
    context: PruningContext,
    pool: &Arc<std::sync::Mutex<TrialPool>>,
    outer: &mut Budget<'_>,
    config: &mut QueryLimits,
    operation: impl FnOnce(
        &mut Budget<'_>,
        &QueryLimits,
        &mut QueryLimits,
        &mut PruningReport,
    ) -> Result<T>,
) -> Result<Option<(T, PruningReport)>> {
    let mut pool = pool.lock().unwrap();
    let slot = pool
        .slots
        .get_mut(&(scope, context))
        .expect("planned trial scope");
    if slot.time.is_zero()
        || slot.work == 0
        || slot.query.max_solves == 0
        || slot.query.max_solver_polls == 0
        || slot.query.max_conflicts == 0
        || slot.query.max_propagations == 0
    {
        return Ok(None);
    }
    let mut limits = e.limits.clone();
    // Leave room for ranking the installed prefix and subsequent children.
    limits.timeout = slot.time.min(outer.remaining_time() / 2);
    limits.max_work = slot.work.min(outer.remaining() / 2);
    let query = QueryLimits {
        max_solves: slot.query.max_solves.min(config.max_solves),
        max_solver_polls: slot.query.max_solver_polls.min(config.max_solver_polls),
        max_conflicts: slot.query.max_conflicts.min(config.max_conflicts),
        max_propagations: slot.query.max_propagations.min(config.max_propagations),
    };
    let start = Instant::now();
    let mut budget = Budget::new(&limits);
    let mut report = PruningReport::default();
    let mut used = QueryLimits {
        max_solves: 0,
        max_solver_polls: 0,
        max_conflicts: 0,
        max_propagations: 0,
    };
    let result = operation(&mut budget, &query, &mut used, &mut report);
    let elapsed = start.elapsed();
    slot.time = slot.time.saturating_sub(elapsed);
    slot.work = slot.work.saturating_sub(budget.used());
    for q in [&mut slot.query, config] {
        q.max_solves = q.max_solves.saturating_sub(used.max_solves);
        q.max_solver_polls = q.max_solver_polls.saturating_sub(used.max_solver_polls);
        q.max_conflicts = q.max_conflicts.saturating_sub(used.max_conflicts);
        q.max_propagations = q.max_propagations.saturating_sub(used.max_propagations);
    }
    pool.elapsed += elapsed;
    pool.attempts += report.attempts;
    pool.proved += report.records.len() + report.omitted;
    outer.charge(budget.used(), "completion branch pruning")?;
    result.map(|value| Some((value, report)))
}

pub(in crate::sat_probe::completion_query) fn prove(
    e: &Engine,
    base: &Cone,
    scope: &'static str,
    context: PruningContext,
    pins: &[(usize, bool)],
    heads: &BTreeSet<usize>,
    budget: &mut Budget<'_>,
    used: &mut QueryLimits,
    report: &mut PruningReport,
) -> Result<Arc<Cone>> {
    let mut result = base.clone();
    let mut successes = Successes::default();
    let original = if scope == "classification" {
        &e.classification.as_ref().unwrap().0
    } else {
        &e.cone
    };
    let answer = simplify(
        e,
        base,
        &mut result,
        context,
        scope,
        original
            .rules
            .iter()
            .map(|r| r.head)
            .collect::<BTreeSet<_>>()
            .len(),
        report,
        budget,
        used,
        &BTreeSet::new(),
        &mut successes,
        Some(heads),
    );
    if let Err(error) = answer {
        e.limits.cancellation.check()?;
        report.incomplete.push(inconclusive(error)?);
    }
    for record in &mut report.records {
        record.pins = pins
            .iter()
            .take(32)
            .map(|(i, v)| (base.atoms[*i].clone(), *v))
            .collect();
        record.omitted_pins = pins.len().saturating_sub(32);
    }
    Ok(Arc::new(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn failed_trials_are_charged_without_borrowing_from_h_or_refreshing_the_pool() {
        use crate::sat_probe::completion_query::tests::{prepare, verification};
        use crate::test_support::rewrites::{rel, rule};
        let mut corpus = Corpus::new();
        let h = rel(&mut corpus, "h", false);
        rule(&mut corpus, h, &[(h, false)]);
        let v = verification(&mut corpus, Some(h), &[]);
        let e = prepare(&corpus, v, &Default::default());
        let cache = Cache::for_engine(&e);
        let original: Duration = cache.reservations.slots.values().map(|s| s.allowance).sum();
        let mut pool = TrialPool::new(&cache.reservations, &e);
        assert!(pool.slots.values().all(|s| s.time.is_zero()));
        assert_eq!(
            original,
            cache
                .reservations
                .slots
                .values()
                .map(|s| s.allowance)
                .sum::<Duration>()
                + pool.slots.values().map(|s| s.time).sum::<Duration>()
        );
        pool.fund_ranking("classification", Duration::from_secs(1));
        let w = ("classification", PruningContext::World);
        let h = ("classification", PruningContext::Hypothesis);
        pool.slots.get_mut(&w).unwrap().query.max_solves = 1;
        let work = pool.slots[&w].work;
        let h_time = pool.slots[&h].time;
        assert_eq!(pool.slots[&w].time, h_time);
        // Only unallocated releases can supplement ranking; taking is one-shot.
        pool.release(Duration::from_millis(8));
        assert_eq!(
            pool.take_released(Duration::from_millis(5)),
            Duration::from_millis(5)
        );
        assert_eq!(
            pool.take_released(Duration::from_millis(5)),
            Duration::from_millis(3)
        );
        assert_eq!(pool.take_released(Duration::from_millis(5)), Duration::ZERO);
        let pool = Arc::new(std::sync::Mutex::new(pool));
        let mut budget = Budget::new(&e.limits);
        let mut q = e.config.clone();
        let result = trial::<()>(
            &e,
            w.0,
            w.1,
            &pool,
            &mut budget,
            &mut q,
            |b, _, used, report| {
                b.charge(3, "test failed trial")?;
                used.max_solves = 1;
                report.attempts = 1;
                Err(CheckError::deadline("test trial cutoff", Duration::ZERO))
            },
        );
        assert!(result.is_err());
        assert_eq!(budget.used(), 3);
        {
            let pool = pool.lock().unwrap();
            assert_eq!(pool.slots[&w].work, work - 3);
            assert_eq!(pool.slots[&h].time, h_time);
            assert_eq!(pool.attempts, 1);
        }
        assert!(
            trial::<()>(
                &e,
                w.0,
                w.1,
                &pool,
                &mut budget,
                &mut q,
                |_, _, _, _| panic!("exhausted allowance restarted")
            )
            .unwrap()
            .is_none()
        );
        pool.lock()
            .unwrap()
            .fund_ranking("classification", Duration::from_secs(1));
        assert!(
            !pool.lock().unwrap().available(w.0, w.1),
            "ranking time cannot refresh explicit query limits"
        );
    }
}
