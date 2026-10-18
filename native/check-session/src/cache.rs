//! Salsa owns completed local query publications. Execution uses the checker's
//! borrowed snapshot outside the database; only fully completed owned values are
//! published. Neither a cancelled thunk nor arena data can enter Salsa storage.
use denotate_check::*;
use salsa::Setter;
use std::{collections::BTreeMap, sync::Arc, time::Instant};

#[salsa::input]
struct Slot {
    #[returns(ref)]
    input: Arc<LocalInput>,
    #[returns(ref)]
    work: Arc<LocalWorkInput>,
    #[returns(ref)]
    receipts: Option<Arc<(WorkReceipt, WorkReceipt)>>,
    #[returns(ref)]
    value: Option<Arc<LocalMemo>>,
}
#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
}
#[salsa::db]
impl salsa::Database for Database {}

// Keeping publications and their receipts in Salsa permits independent value
// eviction. Structural comparison precedes publication, never hash-only lookup.
#[salsa::tracked]
fn evaluation(db: &dyn salsa::Database, slot: Slot) -> Option<Arc<LocalMemo>> {
    slot.value(db).clone()
}
#[salsa::tracked]
fn answer(db: &dyn salsa::Database, slot: Slot) -> Option<Arc<LocalMemo>> {
    evaluation(db, slot).clone()
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
    metadata_bytes: usize,
    value_bytes: usize,
    nodes: usize,
    valid: bool,
}

/// One open document's session. Drop on close; no persistent/cross-document data.
pub struct Session {
    db: Database,
    entries: BTreeMap<LocalScope, Entry>,
    retention: Retention,
    clock: u64,
    stats: CacheStats,
}
impl Default for Session {
    fn default() -> Self {
        Self::new(Retention::default())
    }
}
impl Session {
    pub fn new(retention: Retention) -> Self {
        Self {
            db: Database::default(),
            entries: BTreeMap::new(),
            retention,
            clock: 0,
            stats: CacheStats::default(),
        }
    }
    pub fn stats(&self) -> CacheStats {
        self.stats
    }
    pub fn reset(&mut self) {
        self.entries.clear();
        self.db = Database::default();
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
        let result = prepared.verify_local_with(operations, self);
        operations.cancellation.check()?;
        result
    }
    fn refresh(&mut self) {
        self.stats.retained_entries = self.entries.len().saturating_mul(2);
        self.stats.retained_bytes = self.entries.values().fold(0usize, |n, e| {
            n.saturating_add(e.metadata_bytes)
                .saturating_add(e.value_bytes)
        });
        self.stats.retained_condition_nodes = self
            .entries
            .values()
            .fold(0usize, |n, e| n.saturating_add(e.nodes));
    }
    fn touch(&mut self) -> u64 {
        if self.clock == u64::MAX {
            self.reset();
            self.clock = 0;
        }
        self.clock += 1;
        self.clock
    }
    /// Evict values while retaining validated keys and receipts. Once metadata
    /// cannot fit, dropping the whole database also reclaims Salsa bookkeeping.
    pub fn evict_values(&mut self) {
        let scopes = self.entries.keys().cloned().collect::<Vec<_>>();
        for scope in scopes {
            self.evict(&scope);
        }
        self.refresh();
    }
    fn evict(&mut self, scope: &LocalScope) {
        let e = self.entries.get_mut(scope).unwrap();
        if e.value_bytes == 0 {
            return;
        }
        e.slot.set_value(&mut self.db).to(None);
        // Validate both memos now, releasing the evicted Arc without waiting for
        // a future lookup. No database snapshots are retained by this driver.
        let _ = answer(&self.db, e.slot);
        e.value_bytes = 0;
        e.nodes = 0;
        self.stats.evicted += 2;
    }
    pub fn retained_receipts(&self, scope: &LocalScope) -> Option<(WorkReceipt, WorkReceipt)> {
        self.entries.get(scope).filter(|e| e.valid).and_then(|e| {
            e.slot
                .receipts(&self.db)
                .as_ref()
                .map(|r| r.as_ref().clone())
        })
    }
}
impl LocalMemoStore for Session {
    fn get(&mut self, input: &LocalInput, work: &LocalWorkInput) -> Option<Arc<LocalMemo>> {
        let started = Instant::now();
        let tick = self.touch();
        let value = self.entries.get_mut(&input.scope).and_then(|e| {
            e.touched = tick;
            let same_work = e.slot.work(&self.db).as_ref() == work
                || (e.slot.work(&self.db).same_component_work(work)
                    && e.slot.value(&self.db).as_ref().is_some_and(|v| {
                        v.reorder_safe && v.evaluation_receipt.own.exhausted.is_empty()
                    }));
            if !e.valid || e.slot.input(&self.db).as_ref() != input || !same_work {
                if e.valid {
                    self.stats.invalidated += 2;
                }
                e.valid = false;
                // Changing any receipt dependency invalidates receipts even when
                // the next semantic value happens to compare equal.
                None
            } else {
                answer(&self.db, e.slot).clone()
            }
        });
        if self.entries.get(&input.scope).is_some_and(|e| !e.valid) {
            self.evict(&input.scope);
            let slot = self.entries[&input.scope].slot;
            slot.set_receipts(&mut self.db).to(None);
            self.refresh();
        }
        if value.is_some() {
            self.stats.evaluation_hits += 1;
        } else {
            self.stats.evaluation_misses += 1;
        }
        match (&input.scope, value.is_some()) {
            (LocalScope::Group(_), true) => self.stats.verdict_hits += 1,
            (LocalScope::Group(_), false) => self.stats.verdict_misses += 1,
            (LocalScope::Region(_), true) => self.stats.completion_hits += 1,
            (LocalScope::Region(_), false) => self.stats.completion_misses += 1,
        }
        if let Some(value) = &value {
            self.stats.reused_query_work = self
                .stats
                .reused_query_work
                .saturating_add(
                    value
                        .evaluation_receipt
                        .own
                        .work
                        .saturating_sub(work.discovery.work),
                )
                .saturating_add(value.answer_receipt.own.work);
        }
        self.stats.lookup_ns = self
            .stats
            .lookup_ns
            .saturating_add(started.elapsed().as_nanos().min(u64::MAX as u128) as u64);
        value
    }
    fn put(&mut self, input: &LocalInput, work: &LocalWorkInput, value: Arc<LocalMemo>) {
        let started = Instant::now();
        self.publish(input, work, value);
        self.stats.publication_ns = self
            .stats
            .publication_ns
            .saturating_add(started.elapsed().as_nanos().min(u64::MAX as u128) as u64);
    }
}
impl Session {
    fn publish(&mut self, input: &LocalInput, work: &LocalWorkInput, value: Arc<LocalMemo>) {
        let receipts = Arc::new((
            value.evaluation_receipt.clone(),
            value.answer_receipt.clone(),
        ));
        // Explicit structural payloads; allocation sharing is counted within
        // each part, conservatively charged again across independently evictable entries.
        let metadata_bytes = crate::retention::bytes(input)
            .saturating_add(crate::retention::bytes(&input.scope))
            .saturating_add(crate::retention::bytes(work))
            .saturating_add(crate::retention::bytes(&receipts))
            .saturating_add(512);
        let value_bytes = crate::retention::bytes(&value).saturating_add(256);
        let nodes = nodes(&value);
        if self.retention.max_entries < 2
            || metadata_bytes.saturating_add(value_bytes) > self.retention.max_bytes
            || nodes > self.retention.max_condition_nodes
        {
            self.stats.bypassed += 2;
            // Bypass this value without throwing away unrelated completed work.
            // Keep any existing slot empty/invalid until it can be reused; its
            // already-accounted metadata stays bounded and never supplies a receipt.
            if let Some(e) = self.entries.get_mut(&input.scope) {
                e.valid = false;
                e.slot.set_receipts(&mut self.db).to(None);
                self.evict(&input.scope);
                self.refresh();
            }
            return;
        }
        if !self.entries.contains_key(&input.scope)
            && self.entries.len().saturating_add(1).saturating_mul(2) > self.retention.max_entries
        {
            self.reset();
        }
        let old_bytes = self
            .entries
            .get(&input.scope)
            .map_or(0, |e| e.metadata_bytes.saturating_add(e.value_bytes));
        let old_nodes = self.entries.get(&input.scope).map_or(0, |e| e.nodes);
        self.refresh();
        while self
            .stats
            .retained_bytes
            .saturating_sub(old_bytes)
            .saturating_add(metadata_bytes)
            .saturating_add(value_bytes)
            > self.retention.max_bytes
            || self
                .stats
                .retained_condition_nodes
                .saturating_sub(old_nodes)
                .saturating_add(nodes)
                > self.retention.max_condition_nodes
        {
            let victim = self
                .entries
                .iter()
                .filter(|(k, e)| **k != input.scope && e.value_bytes > 0)
                .min_by_key(|(_, e)| e.touched)
                .map(|(k, _)| k.clone());
            if let Some(victim) = victim {
                self.evict(&victim);
                self.refresh();
            } else {
                self.reset();
                break;
            }
        }
        let tick = self.touch();
        if let Some(e) = self.entries.get_mut(&input.scope) {
            e.slot.set_input(&mut self.db).to(Arc::new(input.clone()));
            e.slot.set_work(&mut self.db).to(Arc::new(work.clone()));
            e.slot.set_receipts(&mut self.db).to(Some(receipts));
            e.slot.set_value(&mut self.db).to(Some(value));
            e.touched = tick;
            e.metadata_bytes = metadata_bytes;
            e.value_bytes = value_bytes;
            e.nodes = nodes;
            e.valid = true;
            let _ = answer(&self.db, e.slot);
        } else {
            let slot = Slot::new(
                &self.db,
                Arc::new(input.clone()),
                Arc::new(work.clone()),
                Some(receipts),
                Some(value),
            );
            let _ = answer(&self.db, slot);
            self.entries.insert(
                input.scope.clone(),
                Entry {
                    slot,
                    touched: tick,
                    metadata_bytes,
                    value_bytes,
                    nodes,
                    valid: true,
                },
            );
        }
        self.refresh();
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
