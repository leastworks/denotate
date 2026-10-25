//! Owned-input Salsa evaluation and answer queries, with bounded recycled slots.
use denotate_check::*;
use salsa::Setter;
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
    time::Instant,
};

#[salsa::input]
struct Slot {
    #[returns(ref)]
    input: Option<Arc<LocalInput>>,
}
#[salsa::db]
pub(crate) trait Db: salsa::Database {
    fn operations(&self) -> OperationalLimits;
    fn measured(&self, answer: bool, metrics: LocalMetrics);
}
#[derive(Default)]
struct Executions {
    evaluation: usize,
    answer: usize,
    metrics: LocalMetrics,
}
#[salsa::db]
#[derive(Clone)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
    operations: Arc<Mutex<OperationalLimits>>,
    executed: Arc<Mutex<Executions>>,
    #[cfg(test)]
    interrupt_after_evaluation: Arc<std::sync::atomic::AtomicBool>,
}
impl Default for Database {
    fn default() -> Self {
        Self {
            storage: Default::default(),
            operations: Arc::new(Mutex::new(OperationalLimits::from(&Limits::default()))),
            executed: Default::default(),
            #[cfg(test)]
            interrupt_after_evaluation: Default::default(),
        }
    }
}
#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn operations(&self) -> OperationalLimits {
        self.operations.lock().unwrap().clone()
    }
    fn measured(&self, answer: bool, m: LocalMetrics) {
        let mut e = self.executed.lock().unwrap();
        if answer {
            e.answer += 1;
        } else {
            e.evaluation += 1;
        }
        e.metrics.evaluation += m.evaluation;
        e.metrics.export += m.export;
        e.metrics.property += m.property;
        e.metrics.completion += m.completion;
        #[cfg(any(test, feature = "test-support"))]
        e.metrics.merge_scc_work(m.scc_work);
        #[cfg(test)]
        if !answer
            && self
                .interrupt_after_evaluation
                .swap(false, std::sync::atomic::Ordering::Relaxed)
        {
            self.operations.lock().unwrap().cancellation.cancel();
        }
    }
}
#[salsa::tracked]
fn query_input(db: &dyn Db, slot: Slot) -> Option<Arc<LocalInput>> {
    slot.input(db).clone()
}
#[salsa::tracked]
fn evaluation(db: &dyn Db, slot: Slot) -> Result<Option<Arc<OwnedEvaluation>>, CheckError> {
    let Some(input) = query_input(db, slot) else {
        return Ok(None);
    };
    let mut metrics = LocalMetrics::default();
    let value = evaluate_owned_local(input, &db.operations(), &mut metrics);
    db.measured(false, metrics);
    value.map(|v| Some(Arc::new(v)))
}
// Receipt changes cannot invalidate this semantic projection by themselves.
#[salsa::tracked]
fn evaluation_value(
    db: &dyn Db,
    slot: Slot,
) -> Result<Option<Arc<(Option<Arc<LocalEvaluation>>, Option<Inconclusive>)>>, CheckError> {
    Ok(evaluation(db, slot)
        .as_ref()
        .map_err(Clone::clone)?
        .as_ref()
        .map(|e| Arc::new((e.value.clone(), e.failure))))
}
#[salsa::tracked]
fn answer_input(db: &dyn Db, slot: Slot) -> Option<Arc<LocalInput>> {
    query_input(db, slot)
        .as_ref()
        .map(|i| Arc::new(i.for_answer()))
}
#[salsa::tracked]
fn answer(db: &dyn Db, slot: Slot) -> Result<Option<Arc<OwnedAnswer>>, CheckError> {
    let Some(input) = answer_input(db, slot) else {
        return Ok(None);
    };
    let value = evaluation_value(db, slot)
        .as_ref()
        .map_err(Clone::clone)?
        .as_ref()
        .ok_or(CheckError::Internal("missing owned evaluation"))?;
    let mut metrics = LocalMetrics::default();
    let result = answer_owned_local(
        input,
        value.0.as_deref(),
        value.1,
        &db.operations(),
        &mut metrics,
    );
    db.measured(true, metrics);
    result.map(|v| Some(Arc::new(v)))
}
#[derive(Debug, Clone, Copy)]
pub struct Retention {
    pub max_entries: usize,
    pub max_bytes: usize,
    pub max_condition_nodes: usize,
}
impl Default for Retention {
    fn default() -> Self {
        Self {
            max_entries: 1024,
            max_bytes: 64 * 1024 * 1024,
            max_condition_nodes: 1_000_000,
        }
    }
}
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CacheStats {
    pub lookup_ns: u64,
    pub publication_ns: u64,
    pub reused_query_work: usize,
    pub evaluation_hits: usize,
    pub evaluation_misses: usize,
    pub verdict_hits: usize,
    pub verdict_misses: usize,
    pub completion_hits: usize,
    pub completion_misses: usize,
    pub invalidated: usize,
    pub evicted: usize,
    pub bypassed: usize,
    pub resets: usize,
    pub retained_entries: usize,
    pub retained_bytes: usize,
    pub retained_condition_nodes: usize,
}

struct Entry {
    slot: Slot,
    touched: u64,
    input: Arc<LocalInput>,
    receipts: Option<(WorkReceipt, WorkReceipt)>,
    bytes: usize,
    nodes: usize,
}
/// Per open document. Recycled slots bound stale inputs and their tracked memos.
pub struct Session {
    db: Database,
    entries: BTreeMap<LocalScope, Entry>,
    free: Vec<Slot>,
    allocated: usize,
    retention: Retention,
    total_retention: Retention,
    clock: u64,
    stats: CacheStats,
    plans: crate::plans::PlanCache,
    grounding: Option<crate::grounding::GroundingCache>,
    #[cfg(any(test, feature = "test-support"))]
    fresh_grounding: bool,
    #[cfg(any(test, feature = "test-support"))]
    fresh_planning: bool,
}
impl Default for Session {
    fn default() -> Self {
        Self::new(Retention::default())
    }
}
impl Session {
    pub fn new(retention: Retention) -> Self {
        Self {
            db: Default::default(),
            entries: Default::default(),
            free: vec![],
            allocated: 0,
            retention,
            total_retention: retention,
            clock: 0,
            stats: Default::default(),
            plans: Default::default(),
            grounding: None,
            #[cfg(any(test, feature = "test-support"))]
            fresh_grounding: false,
            #[cfg(any(test, feature = "test-support"))]
            fresh_planning: false,
        }
    }
    /// Measurement control: effectively unbounded retained bytes, entries and
    /// condition nodes, including the experimental graph slot limits. Logical
    /// work limits and plan admission policy are unchanged.
    #[cfg(any(test, feature = "test-support"))]
    pub fn without_retention_limits(mut self) -> Self {
        self.total_retention = Retention {
            max_entries: usize::MAX,
            max_bytes: usize::MAX,
            max_condition_nodes: usize::MAX,
        };
        self.retention = self.total_retention;
        if let Some(g) = &mut self.grounding {
            g.unconstrained_retention = true;
        }
        self
    }
    #[cfg(any(test, feature = "test-support"))]
    pub fn with_fresh_planning() -> Self {
        Self {
            fresh_planning: true,
            ..Self::default()
        }
    }
    /// 6b.3b relation-SCC grounding, followed by the usual coarse local queries.
    pub fn with_grounding() -> Self {
        Self::new_grounding(Retention::default())
    }
    pub fn new_grounding(retention: Retention) -> Self {
        Self {
            grounding: Some(Default::default()),
            ..Self::new(retention)
        }
    }
    pub fn enable_grounding(&mut self) {
        self.grounding = Some(Default::default());
        #[cfg(any(test, feature = "test-support"))]
        if self.total_retention.max_bytes == usize::MAX {
            self.grounding.as_mut().unwrap().unconstrained_retention = true;
        }
    }
    #[cfg(any(test, feature = "test-support"))]
    pub fn with_fresh_grounding() -> Self {
        Self {
            fresh_grounding: true,
            ..Self::with_grounding()
        }
    }
    pub fn grounding_stats(&self) -> crate::GroundingStats {
        self.grounding
            .as_ref()
            .map_or(Default::default(), |g| g.stats)
    }
    pub fn plan_stats(&self) -> crate::PlanStats {
        self.plans.stats
    }
    /// Plans share bytes, but have a separate entry allowance. Local evaluation
    /// and answer each retain up to max_entries/2 slots (512 each at defaults).
    pub fn prepare<'s>(
        &mut self,
        request: &CheckRequest,
        corpus: &'s denotate_ir::Corpus,
        keys: &'s denotate_ir::SemanticKeys,
        operations: &OperationalLimits,
    ) -> Result<RequestPreparation<'s>, CheckError> {
        #[cfg(any(test, feature = "test-support"))]
        if self.fresh_planning {
            return request.prepare(corpus, keys, operations);
        }
        let plan_bytes = self.total_retention.max_bytes / 8;
        let plan_entries = self.total_retention.max_entries / 2;
        operations.cancellation.check()?;
        let rule_keys = corpus
            .rules()
            .filter(|r| {
                r.body
                    .iter()
                    .filter(|l| matches!(l, denotate_ir::Literal::Positive(_)))
                    .count()
                    >= crate::plans::MIN_POSITIVE_LITERALS
            })
            .map(|r| keys.rule(r.id).cloned().map_err(CheckError::Keys))
            .collect::<Result<Vec<_>, _>>()?;
        let reserve_entries = self.plans.reserve_entries(&rule_keys, plan_entries);
        // An all-small fresh snapshot allocates no plan slots or byte reserve.
        let plan_bytes = if reserve_entries == 0 { 0 } else { plan_bytes };
        self.trim_local(
            self.total_retention
                .max_bytes
                .saturating_sub(plan_bytes)
                .saturating_sub(self.grounding_stats().retained_bytes),
            self.total_retention.max_entries,
        );
        self.plans.begin(plan_entries, plan_bytes);
        let result = if let Some(grounding) = &mut self.grounding {
            grounding.begin(self.total_retention.max_bytes / 4);
            #[cfg(any(test, feature = "test-support"))]
            let fresh = self.fresh_grounding;
            #[cfg(not(any(test, feature = "test-support")))]
            let fresh = false;
            let store: &mut dyn GroundingStore = if fresh {
                &mut FreshGrounding
            } else {
                grounding
            };
            request.prepare_with_grounding(corpus, keys, operations, &mut self.plans, store)
        } else {
            request.prepare_with_plans(corpus, keys, operations, &mut self.plans)
        };
        let stats = self.plans.stats;
        self.trim_local(
            self.total_retention
                .max_bytes
                .saturating_sub(stats.retained_bytes)
                .saturating_sub(self.grounding_stats().retained_bytes),
            self.total_retention.max_entries,
        );
        result
    }

    fn trim_local(&mut self, bytes: usize, entries: usize) {
        self.retention.max_bytes = bytes;
        self.retention.max_entries = entries;
        self.refresh();
        while (self.stats.retained_bytes > bytes || self.entries.len() * 2 > entries)
            && !self.entries.is_empty()
        {
            let key = self.victim(None).unwrap();
            self.remove(&key);
            self.refresh();
        }
        // Empty slot bookkeeping cannot fit in an arbitrarily tiny byte cap.
        if self.stats.retained_bytes > bytes {
            self.reset_local();
        }
    }
    #[cfg(test)]
    pub(crate) fn local_retention_for_test(&self) -> Retention {
        self.retention
    }
    #[cfg(test)]
    pub(crate) fn interrupt_after_evaluation(&self) {
        self.db
            .interrupt_after_evaluation
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }
    pub fn stats(&self) -> CacheStats {
        self.stats
    }
    pub fn reset(&mut self) {
        self.plans.clear();
        if let Some(grounding) = &mut self.grounding {
            grounding.clear();
        }
        self.retention = self.total_retention;
        self.reset_local();
    }
    fn reset_local(&mut self) {
        self.entries.clear();
        self.free.clear();
        self.allocated = 0;
        self.db = Database::default();
        self.clock = 0;
        self.stats.resets += 1;
        self.refresh();
    }
    pub fn verify<'p>(
        &mut self,
        prepared: &'p PreparedCheck<'_>,
        operations: &OperationalLimits,
    ) -> Result<LocalCheckOutcome<'p>, CheckError> {
        self.stats = CacheStats::default();
        self.refresh();
        operations.cancellation.check()?;
        if operations.timeout.is_zero() {
            return Err(CheckError::Deadline {
                phase: "local cache lookup",
            });
        }
        *self.db.operations.lock().unwrap() = operations.clone();
        let result = prepared.verify_local_with(operations, self);
        operations.cancellation.check()?;
        result
    }
    fn refresh(&mut self) {
        self.stats.retained_entries = self.entries.len() * 2;
        self.stats.retained_bytes = self
            .entries
            .values()
            .fold(self.allocated.saturating_mul(1024), |n, e| {
                n.saturating_add(e.bytes)
            });
        self.stats.retained_condition_nodes = self.entries.values().map(|e| e.nodes).sum();
    }
    fn clear_slot(&mut self, slot: Slot) {
        slot.set_input(&mut self.db).to(None);
        let _ = evaluation(&self.db, slot);
        let _ = evaluation_value(&self.db, slot);
        let _ = answer(&self.db, slot);
    }
    fn victim(&self, except: Option<&LocalScope>) -> Option<LocalScope> {
        self.entries
            .iter()
            .filter(|(k, _)| Some(*k) != except)
            .min_by_key(|(_, e)| e.touched)
            .map(|(k, _)| k.clone())
    }
    fn remove(&mut self, key: &LocalScope) {
        let e = self.entries.remove(key).unwrap();
        self.clear_slot(e.slot);
        self.free.push(e.slot);
        self.stats.evicted += 2;
    }
    pub fn evict_values(&mut self) {
        if let Some(grounding) = &mut self.grounding {
            grounding.evict_values();
        }
        let keys = self.entries.keys().cloned().collect::<Vec<_>>();
        for k in keys {
            let slot = self.entries[&k].slot;
            self.clear_slot(slot);
            let e = self.entries.get_mut(&k).unwrap();
            e.nodes = 0;
            e.bytes = crate::retention::bytes(&(&k, &e.input, &e.receipts));
            self.stats.evicted += 2;
        }
        self.refresh();
    }
    pub fn retained_receipts(&self, scope: &LocalScope) -> Option<(WorkReceipt, WorkReceipt)> {
        self.entries.get(scope).and_then(|e| e.receipts.clone())
    }
}
impl LocalMemoStore for Session {
    fn execute(
        &mut self,
        input: &LocalInput,
        operations: &OperationalLimits,
        metrics: &mut LocalMetrics,
    ) -> Result<Arc<LocalMemo>, CheckError> {
        // A scope identifies the cache slot, not its validity across verifications.
        // LocalInput includes relevant constraints, input groups, obligation shape
        // and completion proof context; Salsa compares that full input. Request
        // identity and replay are attached afresh by PreparedCheck.
        if let Some(e) = self.entries.get_mut(&input.scope) {
            if e.input.as_ref() != input {
                e.receipts = None;
            }
        }
        operations.cancellation.check()?;
        if operations.timeout.is_zero() {
            return Err(CheckError::Deadline {
                phase: "local cache lookup",
            });
        }
        let start = Instant::now();
        if self.clock == u64::MAX {
            self.reset_local();
        }
        self.clock += 1;
        *self.db.operations.lock().unwrap() = operations.clone();
        // Bypass retention using the same owned queries and allowances.
        if self.retention.max_entries < 2 || self.retention.max_bytes < 1024 {
            self.stats.bypassed += 2;
            self.stats.evaluation_misses += 1;
            match input.scope {
                LocalScope::Group(_) => self.stats.verdict_misses += 1,
                LocalScope::Region(_) => self.stats.completion_misses += 1,
            };
            return NoLocalMemo.execute(input, operations, metrics);
        }
        let slot = if let Some(e) = self.entries.get(&input.scope) {
            if e.input.as_ref() != input {
                self.stats.invalidated += 2;
            }
            e.slot
        } else if let Some(slot) = self.free.pop() {
            slot
        } else if self.allocated < self.retention.max_entries / 2
            && (self.allocated + 1) * 1024 <= self.retention.max_bytes
        {
            self.allocated += 1;
            Slot::new(&self.db, None)
        } else if let Some(key) = self.victim(None) {
            self.remove(&key);
            self.free.pop().unwrap()
        } else {
            self.stats.bypassed += 2;
            return NoLocalMemo.execute(input, operations, metrics);
        };
        *self.db.operations.lock().unwrap() = operations.clone();
        *self.db.executed.lock().unwrap() = Executions::default();
        let installed = Arc::new(input.clone());
        slot.set_input(&mut self.db).to(Some(installed.clone()));
        let computed = (|| {
            let a = evaluation(&self.db, slot)
                .clone()?
                .ok_or(CheckError::Internal("missing owned evaluation"))?;
            let b = answer(&self.db, slot)
                .clone()?
                .ok_or(CheckError::Internal("missing owned answer"))?;
            operations.cancellation.check()?;
            if start.elapsed() >= operations.timeout {
                return Err(CheckError::Deadline {
                    phase: "owned local query",
                });
            }
            Ok::<_, CheckError>(Arc::new(LocalMemo {
                evaluation: a.value.as_deref().cloned(),
                answer: b.value.clone(),
                failure: b.failure.or(a.failure),
                evaluation_receipt: a.receipt.clone(),
                answer_receipt: b.receipt.clone(),
            }))
        })();
        let exec = std::mem::take(&mut *self.db.executed.lock().unwrap());
        metrics.evaluation += exec.metrics.evaluation;
        metrics.export += exec.metrics.export;
        metrics.property += exec.metrics.property;
        metrics.completion += exec.metrics.completion;
        #[cfg(any(test, feature = "test-support"))]
        metrics.merge_scc_work(exec.metrics.scc_work);
        self.stats.evaluation_misses += exec.evaluation;
        self.stats.evaluation_hits += usize::from(exec.evaluation == 0);
        match input.scope {
            LocalScope::Group(_) => {
                self.stats.verdict_misses += exec.answer;
                self.stats.verdict_hits += usize::from(exec.answer == 0)
            }
            LocalScope::Region(_) => {
                self.stats.completion_misses += exec.answer;
                self.stats.completion_hits += usize::from(exec.answer == 0)
            }
        }
        let value = match computed {
            Ok(v) => v,
            Err(e) => {
                // Operational/internal failures never survive as reusable query memos.
                self.entries.remove(&input.scope);
                self.clear_slot(slot);
                self.free.push(slot);
                self.refresh();
                return Err(e);
            }
        };
        if exec.evaluation == 0 {
            self.stats.reused_query_work = self
                .stats
                .reused_query_work
                .saturating_add(value.evaluation_receipt.own.work)
        }
        if exec.answer == 0 {
            self.stats.reused_query_work = self
                .stats
                .reused_query_work
                .saturating_add(value.answer_receipt.own.work)
        }
        // Walk the actual retained allocations. Salsa may retain an older
        // equal semantic projection alongside a changed evaluation receipt.
        let evaluated = evaluation(&self.db, slot).as_ref().unwrap();
        let semantic = evaluation_value(&self.db, slot).as_ref().unwrap();
        let answered = answer(&self.db, slot).as_ref().unwrap();
        let receipts = Some((
            value.evaluation_receipt.clone(),
            value.answer_receipt.clone(),
        ));
        let bytes = crate::retention::bytes(&(
            (&input.scope, &installed, query_input(&self.db, slot)),
            (answer_input(&self.db, slot), evaluated, semantic),
            (answered, &receipts),
        ));
        let mut node_count = nodes(&value);
        if let (Some(a), Some(b)) = (
            evaluated.as_ref().and_then(|v| v.value.as_ref()),
            semantic.as_ref().and_then(|v| v.0.as_ref()),
        ) {
            if !Arc::ptr_eq(a, b) {
                node_count = node_count
                    .saturating_add(b.permitted.node_count())
                    .saturating_add(
                        b.conditions
                            .values()
                            .map(OwnedCondition::node_count)
                            .sum::<usize>(),
                    );
            }
        }
        self.entries.insert(
            input.scope.clone(),
            Entry {
                slot,
                touched: self.clock,
                input: installed,
                receipts,
                bytes,
                nodes: node_count,
            },
        );
        self.refresh();
        if bytes.saturating_add(self.allocated * 1024) > self.retention.max_bytes
            || node_count > self.retention.max_condition_nodes
        {
            self.remove(&input.scope);
            self.stats.bypassed += 2;
            self.refresh();
            return Ok(value);
        }
        while (self.stats.retained_bytes > self.retention.max_bytes
            || self.stats.retained_condition_nodes > self.retention.max_condition_nodes)
            && self.entries.len() > 1
        {
            let key = self.victim(Some(&input.scope)).unwrap();
            self.remove(&key);
            self.refresh();
        }
        if self.stats.retained_bytes > self.retention.max_bytes
            || self.stats.retained_condition_nodes > self.retention.max_condition_nodes
        {
            self.remove(&input.scope);
            self.stats.bypassed += 2;
            self.refresh();
        }
        self.stats.lookup_ns = self
            .stats
            .lookup_ns
            .saturating_add(start.elapsed().as_nanos().min(u64::MAX as u128) as u64);
        Ok(value)
    }
}
fn nodes(value: &LocalMemo) -> usize {
    let mut n = 0usize;
    let mut add = |c: &OwnedCondition| {
        n = n.saturating_add(c.node_count());
    };
    if let Some(e) = &value.evaluation {
        add(&e.permitted);
        for c in e.conditions.values() {
            add(c);
        }
    }
    match &value.answer {
        Some(LocalAnswer::Group(LocalVerdict::Overlap(c))) => add(c),
        Some(LocalAnswer::Completion {
            bad_input,
            boundary,
            ..
        }) => {
            if let Some(c) = bad_input {
                add(c);
            }
            for c in boundary.values() {
                add(c);
            }
        }
        _ => {}
    }
    n
}
