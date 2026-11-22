//! Opt-in, bounded completion size observations. Never semantic evidence or cache identity.
use crate::{CheckError, GroundAtom};
use denotate_ir::RelationId;
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

#[derive(Debug, Clone, Default)]
pub struct PossibilityRelation {
    pub observed: usize,
    pub fixed: bool,
    pub round: usize,
    pub least: usize,
    pub circular: Option<usize>,
    pub example: Option<GroundAtom>,
}
#[derive(Debug, Clone, Default)]
pub struct CompletionPreparationSize {
    pub static_provider: bool,
    pub provider: Option<RelationId>,
    pub work: usize,
    pub work_by_stage: BTreeMap<&'static str, usize>,
    pub error: Option<CheckError>,
    pub complete: bool,
    pub atoms: usize,
    pub rules: usize,
    /// Peak candidate count checked by the GFP atom allowance, including a
    /// rejected insertion. Not the sum over rounds or a byte-memory peak.
    pub peak_possibility_atoms: usize,
    pub least_complete: bool,
    pub least_error: Option<CheckError>,
    pub relations: BTreeMap<RelationId, PossibilityRelation>,
    pub components: Vec<Vec<RelationId>>,
}
#[derive(Debug, Clone, Default)]
pub struct CompletionEncodingSize {
    pub purpose: &'static str,
    pub complete: bool,
    pub atoms: usize,
    pub input_atoms: usize,
    pub folded_true: usize,
    pub folded_false: usize,
    pub variables: usize,
    pub clauses: usize,
}
#[derive(Debug, Clone)]
pub struct CompletionSearchSize {
    pub phase: &'static str,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    /// Encoding attempts, including a partially built last copy on exhaustion.
    pub encodings: usize,
    pub encoding_details: Vec<CompletionEncodingSize>,
    pub omitted_encodings: usize,
}
/// One preparation budget, including work outside grounding attempts. Attempt
/// records are a breakdown of this total, not additional work. Diagnostic LFP
/// and subsequent checking searches have separate budgets and are excluded.
#[derive(Debug, Clone, Default)]
pub struct CompletionPreparationWork {
    pub work: usize,
    pub by_stage: BTreeMap<&'static str, usize>,
    pub by_phase: BTreeMap<&'static str, usize>,
    /// Charges refused by the work allowance; not included in `work`.
    pub rejected_by_phase: BTreeMap<&'static str, usize>,
    pub last_stage: &'static str,
}
pub(crate) struct PreparationWorkMonitor {
    sink: CompletionSizes,
    pub data: CompletionPreparationWork,
}
impl PreparationWorkMonitor {
    pub fn new(sink: CompletionSizes) -> Self {
        Self {
            sink,
            data: CompletionPreparationWork::default(),
        }
    }
    pub fn charge(&mut self, amount: usize, phase: &'static str) {
        self.data.work += amount;
        *self.data.by_phase.entry(phase).or_default() += amount;
        *self.data.by_stage.entry(self.data.last_stage).or_default() += amount;
    }
}
impl Drop for PreparationWorkMonitor {
    fn drop(&mut self) {
        self.sink.0.lock().unwrap().preparation_work = Some(std::mem::take(&mut self.data));
    }
}
#[derive(Debug, Clone, Default)]
pub struct CompletionSizeSnapshot {
    pub preparation_work: Option<CompletionPreparationWork>,
    pub preparations: Vec<CompletionPreparationSize>,
    pub searches: Vec<CompletionSearchSize>,
    pub omitted_preparations: usize,
    pub omitted_searches: usize,
}
/// Explicit per-run observation sink. Clones share only measurements. Create a
/// fresh sink for each verification; disabled checking performs no LFP comparison.
#[derive(Debug, Clone, Default)]
pub struct CompletionSizes(Arc<Mutex<CompletionSizeSnapshot>>);
impl CompletionSizes {
    pub fn snapshot(&self) -> CompletionSizeSnapshot {
        self.0.lock().unwrap().clone()
    }
    pub(crate) fn preparation(&self, value: CompletionPreparationSize) {
        let mut s = self.0.lock().unwrap();
        if s.preparations.len() < 128 {
            s.preparations.push(value);
        } else {
            s.omitted_preparations += 1;
        }
    }
    pub(crate) fn search(&self, value: CompletionSearchSize) {
        let mut s = self.0.lock().unwrap();
        if s.searches.len() < 1024 {
            s.searches.push(value);
        } else {
            s.omitted_searches += 1;
        }
    }
}
