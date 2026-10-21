//! Bounded SCC evaluation and semantic provider queries in the scope database.
use crate::cache::{Database, Db};
use denotate_check::*;
use salsa::Setter;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::Instant,
};

#[salsa::input]
pub(crate) struct Slot {
    #[returns(ref)]
    input: Option<Arc<ComponentInput>>,
    #[returns(ref)]
    providers: Vec<(ComponentKey, Slot)>,
}
#[derive(Default)]
pub(crate) struct Executions {
    pub evaluations: usize,
    pub providers: usize,
    pub metrics: LocalMetrics,
}
#[salsa::tracked]
fn component_input(db: &dyn Db, slot: Slot) -> Option<Arc<ComponentInput>> {
    slot.input(db).clone()
}
#[salsa::tracked]
fn provider_slots(db: &dyn Db, slot: Slot) -> Vec<(ComponentKey, Slot)> {
    slot.providers(db).clone()
}
impl crate::retention::Retained for Slot {
    fn heap(&self, _: &mut crate::retention::Payload) {}
}
#[salsa::tracked]
fn evaluate(db: &dyn Db, slot: Slot) -> Result<Option<Arc<OwnedEvaluation>>, CheckError> {
    let Some(input) = component_input(db, slot) else {
        return Ok(None);
    };
    let mut dependencies = BTreeMap::new();
    for (key, provider) in provider_slots(db, slot) {
        let value = provide(db, *provider)
            .as_ref()
            .map_err(Clone::clone)?
            .as_ref()
            .ok_or(CheckError::Internal("missing retained component provider"))?;
        dependencies.insert(key.clone(), value.clone());
    }
    let mut metrics = LocalMetrics::default();
    let value = evaluate_owned_component(input, &dependencies, &db.operations(), &mut metrics);
    db.component_measured(false, metrics);
    value.map(|v| Some(Arc::new(v)))
}
#[salsa::tracked]
fn provide(db: &dyn Db, slot: Slot) -> Result<Option<Arc<ProviderValue>>, CheckError> {
    let result = evaluate(db, slot).as_ref().map_err(Clone::clone)?;
    let Some(result) = result else {
        return Ok(None);
    };
    db.component_measured(true, LocalMetrics::default());
    Ok(Some(Arc::new((result.value.clone(), result.failure))))
}
/// Called by the tracked cone evaluation, so provider equality can backdate
/// before assembly, verdict or completion computation executes.
pub(crate) fn values(
    db: &dyn Db,
    slots: &[(ComponentKey, Slot)],
) -> Result<BTreeMap<ComponentKey, Arc<ProviderValue>>, CheckError> {
    slots
        .iter()
        .map(|(key, slot)| {
            let value = provide(db, *slot)
                .as_ref()
                .map_err(Clone::clone)?
                .as_ref()
                .ok_or(CheckError::Internal("missing cone provider"))?;
            Ok((key.clone(), value.clone()))
        })
        .collect()
}
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ComponentStats {
    pub evaluations: usize,
    pub provider_projections: usize,
    pub hits: usize,
    pub bypassed_graphs: usize,
    pub evicted: usize,
    pub retained_components: usize,
    pub allocated_slots: usize,
    pub retained_bytes: usize,
    pub retained_nodes: usize,
    pub projection_ns: u64,
    /// Input/edge installation, including the separately reported equality time.
    pub input_install_ns: u64,
    pub input_equality_ns: u64,
    /// Tracked cone assembly executions, excluding cached validation.
    pub assembly_ns: u64,
    pub receipts_ns: u64,
    /// Component validation/execution and receipt collection, excluding assembly.
    pub query_ns: u64,
    pub retention_ns: u64,
}
struct Entry {
    slot: Slot,
    touched: u64,
    bytes: usize,
    nodes: usize,
}
#[derive(Default)]
pub(crate) struct ComponentCache {
    entries: BTreeMap<ComponentKey, Entry>,
    free: Vec<Slot>,
    allocated: usize,
    clock: u64,
    pub stats: ComponentStats,
    #[cfg(any(test, feature = "test-support"))]
    pub unconstrained_retention: bool,
    #[cfg(test)]
    pub reverse_requests: bool,
}
// Paired 512 evaluation slots and 512 provider projections, separate from the
// existing 512 cone/512 answer and 512 plan limits, under one document byte cap.
const MAX_COMPONENTS: usize = 512;
const SLOT_BYTES: usize = 2048;
fn nanos(start: Instant) -> u64 {
    start.elapsed().as_nanos().min(u64::MAX as u128) as u64
}
impl ComponentCache {
    pub fn begin(&mut self) {
        self.stats = ComponentStats::default();
        self.refresh();
    }
    fn refresh(&mut self) {
        self.stats.retained_components = self.entries.len();
        self.stats.allocated_slots = self.allocated;
        self.stats.retained_bytes = self
            .entries
            .values()
            .fold(self.allocated.saturating_mul(SLOT_BYTES), |b, e| {
                b.saturating_add(e.bytes)
            });
        self.stats.retained_nodes = self.entries.values().map(|e| e.nodes).sum();
    }
    fn remove(&mut self, db: &mut Database, key: &ComponentKey) {
        let e = self.entries.remove(key).unwrap();
        e.slot.set_input(db).to(None);
        e.slot.set_providers(db).to(vec![]);
        let _ = provider_slots(db, e.slot);
        let _ = evaluate(db, e.slot);
        let _ = provide(db, e.slot);
        self.free.push(e.slot);
        self.stats.evicted += 1;
    }
    fn victim(&self, protected: &BTreeSet<ComponentKey>) -> Option<ComponentKey> {
        self.entries
            .iter()
            .filter(|(k, _)| !protected.contains(*k))
            .min_by_key(|(_, e)| e.touched)
            .map(|(k, _)| k.clone())
    }
    pub fn evict_values(&mut self, db: &mut Database) {
        let keys = self.entries.keys().cloned().collect::<Vec<_>>();
        for key in keys {
            self.remove(db, &key);
        }
        self.refresh();
    }
    pub fn stage(
        &mut self,
        db: &mut Database,
        input: &LocalInput,
        operations: &OperationalLimits,
        metrics: &mut LocalMetrics,
        max_bytes: usize,
    ) -> Result<Option<(Vec<(ComponentKey, Slot)>, WorkReceipts)>, CheckError> {
        operations.cancellation.check()?;
        let started = Instant::now();
        let start = Instant::now();
        let graph = ComponentGraph::project(input)?;
        self.stats.projection_ns += nanos(start);
        let max_components = MAX_COMPONENTS;
        #[cfg(any(test, feature = "test-support"))]
        let max_components = if self.unconstrained_retention {
            usize::MAX
        } else {
            max_components
        };
        if graph.inputs.len() > max_components
            || graph.inputs.len().saturating_mul(SLOT_BYTES) > max_bytes
        {
            self.stats.bypassed_graphs += 1;
            return Ok(None);
        }
        if self.clock == u64::MAX {
            self.evict_values(db);
            self.clock = 0;
        }
        self.clock += 1;
        let start = Instant::now();
        let protected = graph.inputs.keys().cloned().collect::<BTreeSet<_>>();
        for key in graph.inputs.keys() {
            if self.entries.contains_key(key) {
                continue;
            }
            let slot = if let Some(slot) = self.free.pop() {
                slot
            } else if self.allocated < max_components
                && (self.allocated + 1) * SLOT_BYTES <= max_bytes
            {
                self.allocated += 1;
                Slot::new(db, None, vec![])
            } else {
                let victim = self
                    .victim(&protected)
                    .ok_or(CheckError::Internal("no recyclable component slot"))?;
                self.remove(db, &victim);
                self.free.pop().unwrap()
            };
            self.entries.insert(
                key.clone(),
                Entry {
                    slot,
                    touched: self.clock,
                    bytes: 0,
                    nodes: 0,
                },
            );
        }
        for (key, value) in &graph.inputs {
            let slot = self.entries[key].slot;
            let dependencies = value
                .providers
                .iter()
                .map(|k| (k.clone(), self.entries[k].slot))
                .collect();
            let equality = Instant::now();
            let same_input = slot.input(db).as_ref() == Some(value);
            let same_providers = slot.providers(db) == &dependencies;
            self.stats.input_equality_ns += nanos(equality);
            if !same_input {
                slot.set_input(db).to(Some(value.clone()));
            }
            if !same_providers {
                slot.set_providers(db).to(dependencies);
            }
            self.entries.get_mut(key).unwrap().touched = self.clock;
        }
        self.stats.input_install_ns += nanos(start);
        *db.component_executed.lock().unwrap() = Executions::default();
        let start = Instant::now();
        let result = (|| {
            let mut receipts = WorkReceipts::default();
            // Prevalidation in topological order avoids deep physical Salsa
            // recursion and collects current receipts even after semantic cutoff.
            #[allow(unused_mut)]
            let mut requests = graph.order.clone();
            #[cfg(test)]
            if self.reverse_requests {
                requests.reverse();
            }
            for key in &requests {
                let slot = self.entries[key].slot;
                provide(db, slot).as_ref().map_err(Clone::clone)?;
                let result = evaluate(db, slot)
                    .as_ref()
                    .map_err(Clone::clone)?
                    .as_ref()
                    .unwrap();
                let receipt_start = Instant::now();
                receipts
                    .record(
                        QueryKey::ComponentEvaluation(key.clone()),
                        result.receipt.clone(),
                    )
                    .map_err(CheckError::Receipts)?;
                self.stats.receipts_ns += nanos(receipt_start);
                operations.cancellation.check()?;
                if started.elapsed() >= operations.timeout {
                    return Err(CheckError::Deadline {
                        phase: "component graph",
                    });
                }
            }
            let slots = graph
                .order
                .iter()
                .map(|key| (key.clone(), self.entries[key].slot))
                .collect();
            Ok(Some((slots, receipts)))
        })();
        self.stats.query_ns += nanos(start);
        let e = std::mem::take(&mut *db.component_executed.lock().unwrap());
        self.stats.evaluations += e.evaluations;
        self.stats.provider_projections += e.providers;
        self.stats.hits += graph.inputs.len().saturating_sub(e.evaluations);
        metrics.evaluation += e.metrics.evaluation;
        metrics.export += e.metrics.export;
        if result.is_err() {
            for key in &graph.order {
                self.remove(db, key);
            }
            self.refresh();
        }
        result
    }
    /// Account actual current and backdated allocations, then trim AFTER the
    /// tracked cone/answer queries finish reading their providers.
    pub fn finish(
        &mut self,
        db: &mut Database,
        slots: &[(ComponentKey, Slot)],
        max_bytes: usize,
        max_nodes: usize,
    ) {
        let start = Instant::now();
        for (key, slot) in slots {
            let evaluated = evaluate(db, *slot).as_ref().unwrap();
            let provided = provide(db, *slot).as_ref().unwrap();
            let bytes = crate::retention::bytes(&(
                ((key, slot.input(db)), component_input(db, *slot)),
                (evaluated, provided),
                (slot.providers(db), provider_slots(db, *slot)),
            ));
            let mut nodes = 0;
            let mut seen = BTreeSet::new();
            for v in [
                evaluated.as_ref().and_then(|v| v.value.as_ref()),
                provided.as_ref().and_then(|v| v.0.as_ref()),
            ]
            .into_iter()
            .flatten()
            {
                if seen.insert(Arc::as_ptr(v) as usize) {
                    nodes += v.permitted.node_count()
                        + v.conditions
                            .values()
                            .map(OwnedCondition::node_count)
                            .sum::<usize>();
                }
            }
            let entry = self.entries.get_mut(key).unwrap();
            entry.bytes = bytes;
            entry.nodes = nodes;
        }
        self.refresh();
        while self.stats.retained_bytes > max_bytes || self.stats.retained_nodes > max_nodes {
            if let Some(key) = self.victim(&BTreeSet::new()) {
                self.remove(db, &key);
                self.refresh();
            }
            // Stage only allocates a graph if its slot metadata fits. A fixed
            // per-session byte cap therefore always accommodates empty slots.
            else {
                break;
            }
        }
        self.stats.retention_ns += nanos(start);
    }
}
