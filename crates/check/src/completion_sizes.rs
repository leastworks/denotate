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
    pub complete: bool,
    pub atoms: usize,
    pub rules: usize,
    pub least_complete: bool,
    pub least_error: Option<CheckError>,
    pub relations: BTreeMap<RelationId, PossibilityRelation>,
    pub components: Vec<Vec<RelationId>>,
}
#[derive(Debug, Clone)]
pub struct CompletionSearchSize {
    pub phase: &'static str,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    /// Encoding attempts, including a partially built last copy on exhaustion.
    pub encodings: usize,
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
