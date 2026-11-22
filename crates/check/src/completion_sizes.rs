//! Opt-in, bounded completion size observations. Never semantic evidence or cache identity.
use crate::{CheckError, GroundAtom};
use denotate_ir::{RelationId, RuleId};
use std::{
    collections::{BTreeMap, HashMap},
    sync::{Arc, Mutex},
    time::{Duration, Instant},
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
    pub least_enabled: bool,
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
    pub elapsed: Duration,
    /// Query-scope work including construction; unavailable if construction failed
    /// before a Run existed. Nested query scopes may overlap; do not sum them.
    pub work: Option<usize>,
    pub phase: &'static str,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    /// Encoding attempts, including a partially built last copy on exhaustion.
    pub encodings: usize,
    pub encoding_details: Vec<CompletionEncodingSize>,
    pub omitted_encodings: usize,
}
#[derive(Debug, Clone, Copy, Default)]
pub struct CompletionJoinWork {
    pub work: usize,
    pub calls: usize,
}
/// One preparation budget, including work outside grounding attempts. Attempt
/// records are a breakdown of this total, not additional work. Diagnostic LFP
/// and subsequent checking searches have separate budgets and are excluded.
#[derive(Debug, Clone, Default)]
pub struct CompletionPreparationWork {
    pub work: usize,
    pub by_stage: BTreeMap<&'static str, usize>,
    pub by_phase: BTreeMap<&'static str, usize>,
    pub time_by_stage: BTreeMap<&'static str, Duration>,
    /// Actual join/planning/index work, aggregated by authored rule and stage.
    pub join_rules: BTreeMap<(RuleId, &'static str), CompletionJoinWork>,
    /// Charges refused by the work allowance; not included in `work`.
    pub rejected_by_phase: BTreeMap<&'static str, usize>,
    pub last_stage: &'static str,
}
pub(crate) struct PreparationWorkMonitor {
    sink: CompletionSizes,
    pub data: CompletionPreparationWork,
    pub join_work: usize,
    stage_start: Instant,
    stage_work: usize,
    phases: Vec<(&'static str, usize, bool)>,
    phase_ids: HashMap<(usize, usize), usize>,
    // Static string addresses avoid hashing/comparing phase text in hot charges.
    phase_cache: [(usize, usize, usize); 8],
    cache_next: usize,
}
impl PreparationWorkMonitor {
    pub fn new(sink: CompletionSizes) -> Self {
        Self {
            sink,
            data: CompletionPreparationWork {
                last_stage: "setup",
                ..Default::default()
            },
            join_work: 0,
            stage_start: Instant::now(),
            stage_work: 0,
            phases: Vec::new(),
            phase_ids: HashMap::new(),
            phase_cache: [(0, 0, 0); 8],
            cache_next: 0,
        }
    }
    pub fn stage(&mut self, stage: &'static str) {
        *self.data.by_stage.entry(self.data.last_stage).or_default() += self.stage_work;
        self.stage_work = 0;
        *self
            .data
            .time_by_stage
            .entry(self.data.last_stage)
            .or_default() += self.stage_start.elapsed();
        self.stage_start = Instant::now();
        self.data.last_stage = stage;
    }
    pub fn exclude_elapsed(&mut self, elapsed: Duration) {
        self.stage_start += elapsed;
    }
    pub fn charge(&mut self, amount: usize, phase: &'static str) {
        self.data.work += amount;
        self.stage_work += amount;
        let key = (phase.as_ptr() as usize, phase.len());
        let id = if let Some((_, _, id)) = self.phase_cache.iter().find(|(p, n, _)| (*p, *n) == key)
        {
            *id
        } else {
            let id = *self.phase_ids.entry(key).or_insert_with(|| {
                self.phases.push((
                    phase,
                    0,
                    matches!(
                        phase,
                        "completion joins"
                            | "completion join planning"
                            | "completion join index"
                            | "completion bindings"
                    ),
                ));
                self.phases.len() - 1
            });
            self.phase_cache[self.cache_next] = (key.0, key.1, id);
            self.cache_next = (self.cache_next + 1) % self.phase_cache.len();
            id
        };
        self.phases[id].1 += amount;
        if self.phases[id].2 {
            self.join_work += amount;
        }
    }
}
impl Drop for PreparationWorkMonitor {
    fn drop(&mut self) {
        self.stage(self.data.last_stage);
        for &(phase, work, _) in &self.phases {
            *self.data.by_phase.entry(phase).or_default() += work;
        }
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
pub struct CompletionSizes(Arc<Mutex<CompletionSizeSnapshot>>, bool);
impl CompletionSizes {
    /// Explicitly enable the independent, bounded diagnostic LFP comparison.
    pub fn with_least_analysis() -> Self {
        Self(Default::default(), true)
    }
    pub fn least_analysis_enabled(&self) -> bool {
        self.1
    }
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
