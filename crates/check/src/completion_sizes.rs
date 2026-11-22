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
#[derive(Debug, Clone, Default)]
pub struct CompletionSizeSnapshot {
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
