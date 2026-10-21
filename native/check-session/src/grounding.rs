//! Bounded retained grounding. Salsa owns validity; the host installs the current
//! relation graph and reclaims slots. Only possible tuples feed downstream units.
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
    input: Option<Arc<GroundingInput>>,
    #[returns(ref)]
    providers: Vec<(GroundingKey, Slot)>,
}
#[salsa::db]
trait Db: salsa::Database {
    fn operations(&self) -> OperationalLimits;
    fn executed(&self, metrics: GroundingMetrics);
}
#[salsa::db]
#[derive(Clone)]
struct Database {
    storage: salsa::Storage<Self>,
    operations: Arc<Mutex<OperationalLimits>>,
    executions: Arc<Mutex<(usize, GroundingMetrics)>>,
    #[cfg(test)]
    interrupt: Arc<std::sync::atomic::AtomicBool>,
}
impl Default for Database {
    fn default() -> Self {
        Self {
            storage: Default::default(),
            operations: Arc::new(Mutex::new(OperationalLimits::from(&Limits::default()))),
            executions: Default::default(),
            #[cfg(test)]
            interrupt: Default::default(),
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
    fn executed(&self, m: GroundingMetrics) {
        let mut e = self.executions.lock().unwrap();
        e.0 += 1;
        e.1.reconstruction_ns += m.reconstruction_ns;
        e.1.closure_ns += m.closure_ns;
        e.1.export_ns += m.export_ns;
        #[cfg(test)]
        if self
            .interrupt
            .swap(false, std::sync::atomic::Ordering::Relaxed)
        {
            self.operations.lock().unwrap().cancellation.cancel();
        }
    }
}
#[salsa::tracked]
fn input(db: &dyn Db, slot: Slot) -> Option<Arc<GroundingInput>> {
    slot.input(db).clone()
}
#[salsa::tracked]
fn providers(db: &dyn Db, slot: Slot) -> Vec<(GroundingKey, Slot)> {
    slot.providers(db).clone()
}
#[salsa::tracked]
fn evaluate(db: &dyn Db, slot: Slot) -> Result<Option<Arc<GroundingResult>>, CheckError> {
    let Some(input) = input(db, slot) else {
        return Ok(None);
    };
    let mut values = BTreeMap::new();
    for (key, slot) in providers(db, slot) {
        let value = possible(db, *slot)
            .as_ref()
            .map_err(Clone::clone)?
            .as_ref()
            .ok_or(CheckError::Internal("missing retained grounding provider"))?;
        values.insert(key.clone(), value.clone());
    }
    let mut metrics = GroundingMetrics::default();
    let result = ground_owned_unit(input, &values, &db.operations(), &mut metrics);
    db.executed(metrics);
    result.map(|r| Some(Arc::new(r)))
}
#[salsa::tracked]
fn possible(db: &dyn Db, slot: Slot) -> Result<Option<Arc<GroundingProvider>>, CheckError> {
    Ok(evaluate(db, slot)
        .as_ref()
        .map_err(Clone::clone)?
        .as_ref()
        .map(|r| Arc::new(r.provider())))
}
impl crate::retention::Retained for Slot {
    fn heap(&self, _: &mut crate::retention::Payload) {}
}
#[derive(Debug, Default, Clone, Copy)]
pub struct GroundingStats {
    pub units: usize,
    pub executed: usize,
    pub reused: usize,
    pub bypassed_graphs: usize,
    pub evicted: usize,
    pub allocated_slots: usize,
    pub retained_units: usize,
    pub retained_bytes: usize,
    pub reused_work: usize,
    pub install_ns: u64,
    pub equality_ns: u64,
    pub query_ns: u64,
    pub receipts_ns: u64,
    pub retention_ns: u64,
    pub reconstruction_ns: u64,
    pub closure_ns: u64,
    pub export_ns: u64,
}
struct Entry {
    slot: Slot,
    touched: u64,
    bytes: usize,
}
#[derive(Default)]
pub(crate) struct GroundingCache {
    db: Database,
    entries: BTreeMap<GroundingKey, Entry>,
    free: Vec<Slot>,
    allocated: usize,
    clock: u64,
    pub stats: GroundingStats,
    max_bytes: usize,
    #[cfg(any(test, feature = "test-support"))]
    pub unconstrained_retention: bool,
    #[cfg(test)]
    pub reverse_requests: bool,
}
const MAX_UNITS: usize = 512;
const SLOT_BYTES: usize = 2048;
fn ns(t: Instant) -> u64 {
    t.elapsed().as_nanos().min(u64::MAX as u128) as u64
}
impl GroundingCache {
    #[cfg(test)]
    pub fn interrupt_after_unit(&self) {
        self.db
            .interrupt
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }
    pub fn begin(&mut self, max_bytes: usize) {
        self.stats = GroundingStats::default();
        self.max_bytes = max_bytes;
        self.refresh();
    }
    fn refresh(&mut self) {
        self.stats.allocated_slots = self.allocated;
        self.stats.retained_units = self.entries.len();
        self.stats.retained_bytes = self
            .entries
            .values()
            .fold(self.allocated * SLOT_BYTES, |b, e| {
                b.saturating_add(e.bytes)
            });
    }
    pub fn clear(&mut self) {
        self.db = Database::default();
        self.entries.clear();
        self.free.clear();
        self.allocated = 0;
        self.clock = 0;
        self.refresh();
    }
    fn remove(&mut self, key: &GroundingKey) {
        let e = self.entries.remove(key).unwrap();
        e.slot.set_input(&mut self.db).to(None);
        e.slot.set_providers(&mut self.db).to(vec![]);
        let _ = providers(&self.db, e.slot);
        let _ = evaluate(&self.db, e.slot);
        let _ = possible(&self.db, e.slot);
        self.free.push(e.slot);
        self.stats.evicted += 1;
    }
    pub fn evict_values(&mut self) {
        for key in self.entries.keys().cloned().collect::<Vec<_>>() {
            self.remove(&key);
        }
        self.refresh();
    }
    fn run(
        &mut self,
        graph: &GroundingGraph,
        operations: &OperationalLimits,
    ) -> Result<BTreeMap<GroundingKey, Arc<GroundingResult>>, CheckError> {
        operations.cancellation.check()?;
        let max_units = MAX_UNITS;
        #[cfg(any(test, feature = "test-support"))]
        let max_units = if self.unconstrained_retention {
            usize::MAX
        } else {
            max_units
        };
        if graph.inputs.len() > max_units
            || graph.inputs.len().saturating_mul(SLOT_BYTES) > self.max_bytes
        {
            self.stats.bypassed_graphs += 1;
            self.stats.units = graph.inputs.len();
            self.stats.executed = graph.inputs.len();
            return FreshGrounding.ground(graph, operations);
        }
        let started = Instant::now();
        let start = Instant::now();
        if self.clock == u64::MAX {
            self.clear();
        }
        self.clock += 1;
        // Deleted units and SCC merges/splits remove their old internal support.
        // Every current edge is installed before any query is requested.
        for key in self
            .entries
            .keys()
            .filter(|k| !graph.inputs.contains_key(*k))
            .cloned()
            .collect::<Vec<_>>()
        {
            self.remove(&key);
        }
        for key in graph.inputs.keys() {
            if self.entries.contains_key(key) {
                continue;
            }
            let slot = if let Some(slot) = self.free.pop() {
                slot
            } else {
                self.allocated += 1;
                Slot::new(&self.db, None, vec![])
            };
            self.entries.insert(
                key.clone(),
                Entry {
                    slot,
                    touched: self.clock,
                    bytes: 0,
                },
            );
        }
        for (key, value) in &graph.inputs {
            let slot = self.entries[key].slot;
            let deps = value
                .providers
                .iter()
                .map(|k| (k.clone(), self.entries[k].slot))
                .collect::<Vec<_>>();
            let equality = Instant::now();
            let equal_input = slot.input(&self.db).as_ref() == Some(value);
            let equal_edges = slot.providers(&self.db) == &deps;
            self.stats.equality_ns += ns(equality);
            if !equal_input {
                slot.set_input(&mut self.db).to(Some(value.clone()));
            }
            if !equal_edges {
                slot.set_providers(&mut self.db).to(deps);
            }
            self.entries.get_mut(key).unwrap().touched = self.clock;
        }
        self.stats.install_ns += ns(start);
        *self.db.operations.lock().unwrap() = operations.clone();
        *self.db.executions.lock().unwrap() = Default::default();
        let start = Instant::now();
        let mut results = BTreeMap::new();
        #[allow(unused_mut)]
        let mut order = graph.order.clone();
        #[cfg(test)]
        if self.reverse_requests {
            order.reverse();
        }
        for key in &order {
            operations.cancellation.check()?;
            if started.elapsed() >= operations.timeout {
                return Err(CheckError::Deadline {
                    phase: "grounding queries",
                });
            }
            let before = self.db.executions.lock().unwrap().0;
            let result = evaluate(&self.db, self.entries[key].slot)
                .clone()?
                .ok_or(CheckError::Internal("missing retained grounding unit"))?;
            let _ = possible(&self.db, self.entries[key].slot)
                .as_ref()
                .map_err(Clone::clone)?;
            if self.db.executions.lock().unwrap().0 == before {
                self.stats.reused_work += result.receipt.own.work;
            }
            let receipt = Instant::now();
            results.insert(key.clone(), result);
            self.stats.receipts_ns += ns(receipt);
        }
        operations.cancellation.check()?;
        self.stats.query_ns += ns(start);
        let (executed, m) = *self.db.executions.lock().unwrap();
        self.stats.units = graph.inputs.len();
        self.stats.executed = executed;
        self.stats.reused = self.stats.units.saturating_sub(executed);
        self.stats.reconstruction_ns = m.reconstruction_ns;
        self.stats.closure_ns = m.closure_ns;
        self.stats.export_ns = m.export_ns;
        // Account and evict only after all consumers have read current providers.
        let start = Instant::now();
        for (key, e) in &mut self.entries {
            e.bytes = crate::retention::bytes(&(
                (key, e.slot.input(&self.db), input(&self.db, e.slot)),
                (e.slot.providers(&self.db), providers(&self.db, e.slot)),
                (
                    evaluate(&self.db, e.slot).as_ref().unwrap(),
                    possible(&self.db, e.slot).as_ref().unwrap(),
                ),
            ));
        }
        self.refresh();
        while self.stats.retained_bytes > self.max_bytes {
            let Some(key) = self
                .entries
                .iter()
                .min_by_key(|(_, e)| e.touched)
                .map(|(k, _)| k.clone())
            else {
                break;
            };
            self.remove(&key);
            self.refresh();
        }
        self.stats.retention_ns += ns(start);
        Ok(results)
    }
}
impl GroundingStore for GroundingCache {
    fn ground(
        &mut self,
        graph: &GroundingGraph,
        operations: &OperationalLimits,
    ) -> Result<BTreeMap<GroundingKey, Arc<GroundingResult>>, CheckError> {
        let result = self.run(graph, operations);
        if result.is_err() {
            self.evict_values();
        }
        result
    }
}
