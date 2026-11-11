//! Deterministic query receipts, independent of semantic equality and cache residency.
use crate::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    result::Result,
};

/// Keys are scoped by the request and semantic program inputs. They are not
/// standalone cache keys: a driver must also validate those inputs and limits.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum QueryKey {
    AssumptionValidation,
    FixedFacts,
    FixedRuntime,
    FixedBinding,
    Preparation,
    Grounding(GroundingKey),
    Admission,
    Symbolic,
    CoverageMeaning,
    Coverage(denotate_ir::ObligationKey),
    Emptiness(denotate_ir::ObligationKey),
    Notice(denotate_ir::NoticeKey),
    ConeIndex,
    ConeDiscovery(GroupKey),
    RegionDiscovery(ComponentKey),
    ConeEvaluation(GroupKey),
    RegionEvaluation(ComponentKey),
    FindingContext,
    FindingConversion(GroupKey),
    Property(GroupKey),
    Witness(GroupKey),
    Completion(ComponentKey),
    Certification(GroupKey),
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResourceKey {
    pub phase: String,
    pub resource: String,
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WorkCharges {
    pub work: usize,
    pub by_phase: BTreeMap<String, usize>,
    /// Conservative high-water observations, including rejected attempts.
    /// These are logical resource counts, not measured allocations/RSS.
    pub resource_peaks: BTreeMap<ResourceKey, usize>,
    pub rejected_work: BTreeMap<String, usize>,
    /// Accounting only: optional work may exhaust while the result stays conclusive.
    /// Cache logic must read the result variant, not infer it from this set.
    pub exhausted: BTreeSet<ResourceKey>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkReceipt {
    pub allowance: DeterministicLimits,
    pub own: WorkCharges,
    /// Resolve current receipts by key, never a stale embedded child receipt.
    pub dependencies: BTreeSet<QueryKey>,
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WorkReceipts {
    entries: BTreeMap<QueryKey, WorkReceipt>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReceiptError {
    Missing(QueryKey),
    Cycle(QueryKey),
    Conflicting(QueryKey),
    Overflow,
    InvalidCharges(QueryKey),
}
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AggregateWork {
    /// Each reachable query appears once, in canonical key order.
    pub queries: Vec<QueryKey>,
    pub work: usize,
    pub by_phase: BTreeMap<String, usize>,
    /// Sum of per-query conservative resource peaks. Shared queries count once.
    pub resource_totals: BTreeMap<ResourceKey, usize>,
    pub rejected_work: BTreeMap<String, usize>,
}
/// Cache/reuse boundaries compare this value, not just its semantic payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Accounted<T> {
    pub value: T,
    pub receipts: WorkReceipts,
}
impl WorkReceipts {
    pub fn entries(&self) -> impl Iterator<Item = (&QueryKey, &WorkReceipt)> {
        self.entries.iter()
    }
    pub fn get(&self, key: &QueryKey) -> Option<&WorkReceipt> {
        self.entries.get(key)
    }
    pub fn record(&mut self, key: QueryKey, receipt: WorkReceipt) -> Result<(), ReceiptError> {
        let sum = receipt
            .own
            .by_phase
            .values()
            .try_fold(0usize, |a, b| a.checked_add(*b))
            .ok_or(ReceiptError::Overflow)?;
        if sum != receipt.own.work || receipt.own.work > receipt.allowance.max_work {
            return Err(ReceiptError::InvalidCharges(key));
        }
        if let Some(old) = self.entries.get(&key) {
            if old != &receipt {
                return Err(ReceiptError::Conflicting(key));
            }
        }
        self.entries.insert(key, receipt);
        Ok(())
    }
    /// Value eviction must retain receipts. Invalidation must remove the old
    /// receipt even if the recomputed semantic value later compares equal.
    pub fn invalidate(&mut self, key: &QueryKey) {
        self.entries.remove(key);
    }
    pub fn required(
        &self,
        roots: impl IntoIterator<Item = QueryKey>,
    ) -> Result<Self, ReceiptError> {
        let mut required = BTreeSet::new();
        let mut active = BTreeSet::new();
        // Iterative walk also handles deep retained dependency chains.
        let roots: BTreeSet<_> = roots.into_iter().collect();
        let mut pending: Vec<_> = roots.into_iter().rev().map(|k| (k, false)).collect();
        while let Some((key, exit)) = pending.pop() {
            if exit {
                active.remove(&key);
                required.insert(key);
                continue;
            }
            if required.contains(&key) {
                continue;
            }
            if !active.insert(key.clone()) {
                return Err(ReceiptError::Cycle(key));
            }
            let receipt = self
                .entries
                .get(&key)
                .ok_or_else(|| ReceiptError::Missing(key.clone()))?;
            pending.push((key, true));
            pending.extend(
                receipt
                    .dependencies
                    .iter()
                    .rev()
                    .cloned()
                    .map(|k| (k, false)),
            );
        }
        Ok(Self {
            entries: required
                .into_iter()
                .map(|k| (k.clone(), self.entries[&k].clone()))
                .collect(),
        })
    }
    pub fn aggregate(
        &self,
        roots: impl IntoIterator<Item = QueryKey>,
    ) -> Result<AggregateWork, ReceiptError> {
        let required = self.required(roots)?;
        let mut out = AggregateWork::default();
        for (key, receipt) in required.entries {
            out.queries.push(key);
            out.work = out
                .work
                .checked_add(receipt.own.work)
                .ok_or(ReceiptError::Overflow)?;
            add(&mut out.by_phase, &receipt.own.by_phase)?;
            add(&mut out.resource_totals, &receipt.own.resource_peaks)?;
            add(&mut out.rejected_work, &receipt.own.rejected_work)?;
        }
        Ok(out)
    }
    pub fn total(&self) -> Result<AggregateWork, ReceiptError> {
        self.aggregate(self.entries.keys().cloned())
    }
}
fn add<K: Ord + Clone>(
    to: &mut BTreeMap<K, usize>,
    from: &BTreeMap<K, usize>,
) -> Result<(), ReceiptError> {
    for (key, value) in from {
        let count = to.entry(key.clone()).or_default();
        *count = count.checked_add(*value).ok_or(ReceiptError::Overflow)?;
    }
    Ok(())
}

impl GroupKey {
    pub(crate) fn from_group(
        keys: &denotate_ir::SemanticKeys,
        group: &AtMostOneGroup,
    ) -> Result<Self, CheckError> {
        Ok(Self {
            obligation: keys
                .obligation(group.obligation)
                .map_err(CheckError::Keys)?
                .clone(),
            tuple: group
                .key
                .iter()
                .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                .collect::<Result<_, _>>()?,
        })
    }
}

/// One request's fresh query execution. No cache or request-level ceiling.
/// Group/region execution is canonical; receipt storage/aggregation is order-free.
pub(crate) struct QueryRun<'a> {
    pub keys: &'a denotate_ir::SemanticKeys,
    pub ground: &'a GroundKeyIndex,
    pub receipts: &'a mut WorkReceipts,
}
impl QueryRun<'_> {
    pub fn group(&self, group: &AtMostOneGroup) -> Result<GroupKey, CheckError> {
        GroupKey::from_group(self.keys, group)
    }
    pub fn component(&self, id: ComponentId) -> Result<ComponentKey, CheckError> {
        self.ground
            .components
            .get(&id)
            .cloned()
            .ok_or(CheckError::Internal("missing receipt component key"))
    }
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static TEST_SCHEDULE: std::cell::RefCell<Option<(bool,Vec<QueryKey>)>> = const { std::cell::RefCell::new(None) };
}
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn test_schedule<T>(values: &mut [T]) {
    TEST_SCHEDULE.with(|s| {
        if s.borrow().as_ref().is_some_and(|(reverse, _)| *reverse) {
            values.reverse();
        }
    });
}
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn test_trace(key: &QueryKey) {
    TEST_SCHEDULE.with(|s| {
        if let Some((_, trace)) = s.borrow_mut().as_mut() {
            trace.push(key.clone());
        }
    });
}
#[cfg(any(test, feature = "test-support"))]
pub fn with_test_schedule<T>(reverse: bool, run: impl FnOnce() -> T) -> (T, Vec<QueryKey>) {
    struct Restore(Option<(bool, Vec<QueryKey>)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TEST_SCHEDULE.with(|s| *s.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(TEST_SCHEDULE.with(|s| s.replace(Some((reverse, vec![])))));
    let result = run();
    let trace = TEST_SCHEDULE.with(|s| s.borrow().as_ref().unwrap().1.clone());
    (result, trace)
}
