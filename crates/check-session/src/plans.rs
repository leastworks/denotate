//! Real tracked owned-input planning. The host manages bounded input slots, but
//! Salsa alone decides whether the planner body executes or an old result is valid.
use denotate_check::*;
use denotate_ir::*;
use salsa::Setter;
use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::Instant,
};

// Small bodies cost less to plan fresh than to retain/validate through Salsa.
// This is cache admission policy, not another planner or a logical work discount.
pub(crate) const MIN_POSITIVE_LITERALS: usize = 4;

#[salsa::input]
struct SchemaInput {
    #[returns(ref)]
    schema: Option<Arc<RuleSchema>>,
}
#[salsa::db]
trait Db: salsa::Database {
    fn executed(&self, nanos: usize);
    #[cfg(test)]
    fn downstream(&self);
}
#[salsa::db]
#[derive(Clone, Default)]
struct Database {
    storage: salsa::Storage<Self>,
    executions: Arc<AtomicUsize>,
    execution_ns: Arc<AtomicUsize>,
    #[cfg(test)]
    downstreams: Arc<AtomicUsize>,
}
#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    #[cfg(test)]
    fn downstream(&self) {
        self.downstreams.fetch_add(1, Ordering::Relaxed);
    }
    fn executed(&self, nanos: usize) {
        self.executions.fetch_add(1, Ordering::Relaxed);
        self.execution_ns.fetch_add(nanos, Ordering::Relaxed);
    }
}
#[salsa::tracked]
fn rule_schema(db: &dyn Db, input: SchemaInput) -> Option<Arc<RuleSchema>> {
    // Input setters advance a revision even for equal values in pinned Salsa.
    // This tracked projection backdates equal schemas so the planner can stay
    // green. Equality/validation belongs to Salsa, not host-side memo lookup.
    input.schema(db).clone()
}
#[salsa::tracked]
fn plan(db: &dyn Db, input: SchemaInput) -> Result<Option<Arc<OwnedJoinPlan>>, CheckError> {
    let Some(schema) = rule_schema(db, input) else {
        return Ok(None);
    };
    let start = Instant::now();
    let result =
        OwnedJoinPlan::compute(JoinPlanSchema::from_schema(schema)).map(|p| Some(Arc::new(p)));
    db.executed(start.elapsed().as_nanos().min(usize::MAX as u128) as usize);
    result
}

#[derive(Debug, Clone, Copy, Default)]
pub struct PlanStats {
    pub queries: usize,
    pub executed: usize,
    pub reused: usize,
    pub fallback: usize,
    pub small_rules: usize,
    pub evicted: usize,
    pub bypassed: usize,
    pub reused_work: usize,
    pub retained_entries: usize,
    pub retained_bytes: usize,
    pub query_ns: u64,
    pub execution_ns: u64,
    pub projection_ns: u64,
}
struct Entry {
    slot: SchemaInput,
    touched: u64,
    bytes: usize,
}
#[derive(Default)]
pub(crate) struct PlanCache {
    db: Database,
    entries: BTreeMap<RuleKey, Entry>,
    free: Vec<SchemaInput>,
    allocated: usize,
    clock: u64,
    pub stats: PlanStats,
    max_entries: usize,
    max_bytes: usize,
}
impl PlanCache {
    pub fn reserve_entries(&self, keys: &[RuleKey], cap: usize) -> usize {
        let new = keys
            .iter()
            .filter(|k| !self.entries.contains_key(*k))
            .count();
        self.allocated
            .saturating_add(new.saturating_sub(self.free.len()))
            .min(cap)
    }
    pub fn begin(&mut self, max_entries: usize, max_bytes: usize) {
        self.stats = PlanStats::default();
        self.max_entries = max_entries;
        self.max_bytes = max_bytes;
        if self.allocated > max_entries || self.bytes() > max_bytes {
            self.clear();
        }
        self.refresh();
    }
    fn bytes(&self) -> usize {
        self.entries
            .values()
            .fold(self.allocated.saturating_mul(512), |n, e| {
                n.saturating_add(e.bytes)
            })
    }
    fn refresh(&mut self) {
        self.stats.retained_entries = self.allocated;
        self.stats.retained_bytes = self.bytes();
    }
    pub fn clear(&mut self) {
        self.entries.clear();
        self.free.clear();
        self.allocated = 0;
        self.db = Database::default();
        self.clock = 0;
        self.refresh();
    }
    fn remove(&mut self, key: &RuleKey) -> SchemaInput {
        let entry = self.entries.remove(key).unwrap();
        entry.slot.set_schema(&mut self.db).to(None);
        // Force memo validation to release the old owned plan immediately.
        let _ = plan(&self.db, entry.slot);
        self.stats.evicted += 1;
        entry.slot
    }
    fn victim(&self, except: Option<&RuleKey>) -> Option<RuleKey> {
        self.entries
            .iter()
            .filter(|(k, _)| Some(*k) != except)
            .min_by_key(|(_, e)| e.touched)
            .map(|(k, _)| k.clone())
    }
}
impl JoinPlanStore for PlanCache {
    fn should_cache(&mut self, positive_literals: usize) -> bool {
        let eligible = positive_literals >= MIN_POSITIVE_LITERALS;
        self.stats.small_rules += usize::from(!eligible);
        eligible
    }

    fn plan(
        &mut self,
        key: RuleKey,
        schema: RuleSchema,
        remaining: usize,
    ) -> Result<Option<Arc<OwnedJoinPlan>>, CheckError> {
        if !self.should_cache(schema.body.iter().filter(|(negative, _)| !negative).count()) {
            return Ok(None);
        }
        let start = Instant::now();
        let shape = JoinPlanSchema::from_schema(&schema);
        // Include fresh per-pivot/materialization ticks and constant-key ticks.
        // This conservative gate also bounds *cold* tracked computation. Tight
        // requests use the same fresh planner, never a cached failure result.
        let n = shape.positives.len();
        let bound = shape
            .work_bound()
            .and_then(|w| w.checked_add(n.checked_mul(n)?))
            .and_then(|w| {
                shape
                    .positives
                    .iter()
                    .try_fold(w, |w, a| w.checked_add(a.len()))
            });
        self.stats.projection_ns += start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        if bound.is_none_or(|w| w > remaining) {
            self.stats.fallback += 1;
            return Ok(None);
        }
        if self.max_entries == 0 || self.max_bytes < 512 {
            self.stats.bypassed += 1;
            return Ok(None);
        }
        let start = Instant::now();
        if self.clock == u64::MAX {
            self.clear();
        }
        self.clock += 1;
        let slot = if let Some(e) = self.entries.get(&key) {
            e.slot
        } else if let Some(slot) = self.free.pop() {
            slot
        } else if self.allocated < self.max_entries && (self.allocated + 1) * 512 <= self.max_bytes
        {
            self.allocated += 1;
            SchemaInput::new(&self.db, None)
        } else if let Some(victim) = self.victim(None) {
            self.remove(&victim)
        } else {
            self.stats.bypassed += 1;
            return Ok(None);
        };
        // Setting an equal input is handled by Salsa; there is no host-side
        // semantic equality lookup or stored plan value in Entry.
        let schema = Arc::new(schema);
        slot.set_schema(&mut self.db).to(Some(schema.clone()));
        let before = self.db.executions.load(Ordering::Relaxed);
        let time_before = self.db.execution_ns.load(Ordering::Relaxed);
        let value = plan(&self.db, slot).clone()?;
        let executed = self.db.executions.load(Ordering::Relaxed) - before;
        let value = value.ok_or(CheckError::Internal("missing tracked plan"))?;
        self.stats.execution_ns +=
            (self.db.execution_ns.load(Ordering::Relaxed) - time_before) as u64;
        self.stats.queries += 1;
        self.stats.executed += executed;
        self.stats.reused += usize::from(executed == 0);
        if executed == 0 {
            self.stats.reused_work += value
                .work()
                .ok_or(CheckError::Receipts(ReceiptError::Overflow))?;
        }
        let bytes = crate::retention::bytes(&key)
            .saturating_add(crate::retention::bytes(&schema))
            // Backdating can retain an older equal schema allocation alongside
            // the current input. Count both conservatively, even when shared.
            .saturating_add(crate::retention::bytes(rule_schema(&self.db, slot)))
            .saturating_add(crate::retention::bytes(&value));
        self.entries.insert(
            key.clone(),
            Entry {
                slot,
                touched: self.clock,
                bytes,
            },
        );
        if bytes.saturating_add(self.allocated * 512) > self.max_bytes {
            let slot = self.remove(&key);
            self.free.push(slot);
            self.stats.bypassed += 1;
        } else {
            while self.bytes() > self.max_bytes {
                let victim = self.victim(Some(&key)).expect("current entry fits");
                let slot = self.remove(&victim);
                self.free.push(slot);
            }
        }
        self.refresh();
        self.stats.query_ns += start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[salsa::tracked]
    fn consumer(db: &dyn Db, input: SchemaInput) -> usize {
        db.downstream();
        plan(db, input)
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap()
            .work()
            .unwrap()
    }
    fn schema(name: &str) -> RuleSchema {
        let rule = RuleKey::Library(QualifiedKey::new("test", "rule"));
        let atom = AtomSchema {
            relation: RelationKey::Named(QualifiedKey::new("test", name)),
            occurrence: OccurrenceKey::Library {
                rule,
                atom: 0,
                argument: None,
            },
            arguments: Vec::new(),
        };
        RuleSchema {
            head: atom.clone(),
            body: vec![(false, atom); MIN_POSITIVE_LITERALS],
        }
    }
    #[test]
    fn salsa_executes_validates_and_backdates_owned_plans() {
        let mut db = Database::default();
        let input = SchemaInput::new(&db, Some(Arc::new(schema("a"))));
        let unrelated = SchemaInput::new(&db, None);
        let expected = *consumer(&db, input);
        assert_eq!(db.executions.load(Ordering::Relaxed), 1);
        unrelated
            .set_schema(&mut db)
            .to(Some(Arc::new(schema("unrelated"))));
        assert_eq!(*consumer(&db, input), expected);
        assert_eq!(db.executions.load(Ordering::Relaxed), 1);
        assert_eq!(db.downstreams.load(Ordering::Relaxed), 1);
        input.set_schema(&mut db).to(Some(Arc::new(schema("a"))));
        assert_eq!(*consumer(&db, input), expected);
        assert_eq!(db.executions.load(Ordering::Relaxed), 1);
        // Different semantic relation, identical positional plan. Salsa reruns
        // the planner but backdates its equal result; its consumer does not run.
        input.set_schema(&mut db).to(Some(Arc::new(schema("b"))));
        assert_eq!(*consumer(&db, input), expected);
        assert_eq!(db.executions.load(Ordering::Relaxed), 2);
        assert_eq!(db.downstreams.load(Ordering::Relaxed), 1);
        let mut changed = schema("b");
        changed.body.push(changed.body[0].clone());
        input.set_schema(&mut db).to(Some(Arc::new(changed)));
        assert_ne!(*consumer(&db, input), expected);
        assert_eq!(db.executions.load(Ordering::Relaxed), 3);
        assert_eq!(db.downstreams.load(Ordering::Relaxed), 2);
    }
    #[test]
    fn small_positive_bodies_bypass_slots_even_with_many_negative_literals() {
        let mut cache = PlanCache::default();
        cache.begin(512, 8 * 1024 * 1024);
        for positives in 0..MIN_POSITIVE_LITERALS {
            let mut rule = schema("small");
            let atom = rule.head.clone();
            rule.body = vec![(false, atom.clone()); positives];
            rule.body.extend(vec![(true, atom); 20]);
            assert!(
                cache
                    .plan(
                        RuleKey::Library(QualifiedKey::new("test", "small")),
                        rule,
                        usize::MAX,
                    )
                    .unwrap()
                    .is_none()
            );
        }
        assert_eq!(cache.stats.small_rules, MIN_POSITIVE_LITERALS);
        assert_eq!(cache.stats.queries, 0);
        assert_eq!(cache.stats.retained_entries, 0);
        assert_eq!(cache.stats.retained_bytes, 0);
        let key = RuleKey::Library(QualifiedKey::new("test", "eligible"));
        assert!(
            cache
                .plan(key.clone(), schema("eligible"), usize::MAX)
                .unwrap()
                .is_some()
        );
        assert!(
            cache
                .plan(key, schema("eligible"), usize::MAX)
                .unwrap()
                .is_some()
        );
        assert_eq!(cache.stats.executed, 1);
        assert_eq!(cache.stats.reused, 1);
    }

    #[test]
    fn plan_slots_recycle_and_oversized_values_release_storage() {
        let mut cache = PlanCache::default();
        cache.begin(2, 1_000_000);
        for i in 0..20 {
            let name = format!("r{i}");
            let key = RuleKey::Library(QualifiedKey::new("test", name.clone()));
            cache.plan(key, schema(&name), usize::MAX).unwrap().unwrap();
            assert!(cache.allocated <= 2);
        }
        assert_eq!(cache.stats.evicted, 18);
        assert_eq!(cache.entries.len(), 2);
        cache.begin(2, 1024);
        cache
            .plan(
                RuleKey::Library(QualifiedKey::new("test", "large")),
                schema("large"),
                usize::MAX,
            )
            .unwrap();
        assert_eq!(cache.stats.bypassed, 1);
        assert!(cache.stats.retained_bytes <= 1024);
        assert!(cache.entries.is_empty());
    }
}
