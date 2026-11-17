//! One shared reservation, not an owned waiting pair on every recursive frame.
//! IDs live only in this search over an immutable component and summary snapshot.
use super::*;

pub(super) struct ScoredCone<'a> {
    pub cone: Arc<BorrowedCone<'a>>,
    pub cyclic: usize,
}

#[derive(Default)]
pub(super) struct Cones<'a> {
    pub reserved: usize,
    pub(super) used: usize,
    pub(super) next_id: usize,
    pub(super) entries: BTreeMap<usize, ScoredCone<'a>>,
}

impl<'a> Cones<'a> {
    pub fn reserve(&mut self, retained: &mut usize, budget: &mut Budget<'_>) -> Result<()> {
        // A fixed, charged reservation keeps accounting independent of which
        // cached child is consumed or displaced during recursive unwinding.
        let allowance = (budget.limits.max_condition_nodes / 64).min(65_536);
        if retained.saturating_add(allowance) <= budget.limits.max_condition_nodes {
            self.reserved = allowance;
            *retained = crate::symbolic::retain(*retained, 0, allowance, budget)?;
        }
        Ok(())
    }
    pub fn clear(&mut self, stats: &mut SplitConeProgress) {
        stats.discarded += self.entries.len();
        self.entries.clear();
        self.used = 0;
    }
    pub fn release(&mut self, retained: &mut usize, stats: &mut SplitConeProgress) {
        self.clear(stats);
        *retained -= std::mem::take(&mut self.reserved);
    }
    pub fn discard(&mut self, ids: [Option<usize>; 2], stats: &mut SplitConeProgress) {
        for id in ids {
            stats.discarded += usize::from(self.take(id).is_some());
        }
    }
    pub fn keep(&mut self, value: ScoredCone<'a>) -> Option<usize> {
        let nodes = value.cone.temporary_nodes() + 2;
        if nodes > self.reserved.saturating_sub(self.used) {
            return None;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.entries.insert(id, value);
        self.used += nodes;
        Some(id)
    }
    pub fn take(&mut self, id: Option<usize>) -> Option<ScoredCone<'a>> {
        let value = self.entries.remove(&id?)?;
        self.used -= value.cone.temporary_nodes() + 2;
        Some(value)
    }
}
