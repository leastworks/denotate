//! Opt-in observations, outside receipts, semantic keys and cached results.
//! Callbacks own delivery and OS measurements. The checker performs no IO here.
use std::{
    collections::BTreeMap,
    fmt,
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy, Default)]
pub struct BddStorage {
    pub references: usize,
    pub distinct_arrays: usize,
    pub nodes: usize,
    /// Occupied node payload only; excludes vector capacity and allocator overhead.
    pub node_bytes: usize,
}
#[derive(Debug, Clone)]
pub struct ProfileEvent {
    pub id: u64,
    pub stage: &'static str,
    pub round: Option<usize>,
    pub finished: bool,
    pub elapsed: Duration,
    /// Newly wrapped BDD results, not allocator calls or solver temporary storage.
    pub bdd_results: u64,
    pub bdd_result_nodes: u64,
    pub bdd_result_node_bytes: u64,
    pub retained: Option<BddStorage>,
    /// Maximum accepted retained-condition accounting observed inside this span.
    /// Not heap bytes or peak live solver nodes; rejected demands are excluded.
    pub peak_accounted_condition_nodes: usize,
}
/// Optional detailed observations. Atom handles belong to the current invocation;
/// drivers resolve them to authored/semantic identities before storing the stream.
#[derive(Debug, Clone)]
pub enum ConditionObservation {
    BindDeclarations {
        relations: Vec<(denotate_ir::RelationId, denotate_ir::RelationKey)>,
        constants: Vec<(denotate_ir::ConstantId, denotate_ir::ConstantKey)>,
    },
    UnbindDeclarations {
        ids: Vec<denotate_ir::OccurrenceId>,
    },
    InputOrder {
        atoms: Vec<crate::GroundAtom>,
        report: crate::InputOrderReport,
    },
    /// A condition retained at a completed component boundary, not a recursive
    /// approximation. Values below 64 nodes are omitted from this diagnostic stream.
    Retained {
        atom: crate::GroundAtom,
        nodes: usize,
    },
    AssumptionStep {
        kind: &'static str,
        group: usize,
        atom: Option<crate::GroundAtom>,
        seen_nodes: usize,
        permitted_nodes: usize,
    },
    FailedOperation {
        operation: [Option<bool>; 4],
        left_nodes: usize,
        right_nodes: Option<usize>,
        error: crate::CheckError,
    },
}
#[derive(Debug, Clone)]
pub struct ConditionProfileEvent {
    pub stages: Vec<&'static str>,
    pub target: Option<crate::GroundAtom>,
    pub observation: ConditionObservation,
}
type Observer = dyn Fn(ConditionProfileEvent) + Send + Sync;
struct State {
    send: Box<dyn Fn(ProfileEvent) + Send + Sync>,
    next: AtomicU64,
    results: AtomicU64,
    nodes: AtomicU64,
    condition_peaks: Mutex<BTreeMap<u64, (&'static str, usize)>>,
    observer: OnceLock<Box<Observer>>,
    targets: Mutex<BTreeMap<u64, crate::GroundAtom>>,
}
#[derive(Clone, Default)]
pub struct Profile(Option<Arc<State>>);
impl fmt::Debug for Profile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Profile").field(&self.enabled()).finish()
    }
}
impl Profile {
    pub fn new(send: impl Fn(ProfileEvent) + Send + Sync + 'static) -> Self {
        Self(Some(Arc::new(State {
            send: Box::new(send),
            next: AtomicU64::new(1),
            results: AtomicU64::new(0),
            nodes: AtomicU64::new(0),
            condition_peaks: Default::default(),
            observer: OnceLock::new(),
            targets: Default::default(),
        })))
    }
    pub fn enabled(&self) -> bool {
        self.0.is_some()
    }
    pub(crate) fn bdd_created(&self, nodes: usize) {
        if let Some(s) = &self.0 {
            s.results.fetch_add(1, Ordering::Relaxed);
            s.nodes.fetch_add(nodes as u64, Ordering::Relaxed);
        }
    }
    pub(crate) fn retained_conditions(&self, nodes: usize) {
        if let Some(s) = &self.0 {
            for (_, peak) in s.condition_peaks.lock().unwrap().values_mut() {
                *peak = (*peak).max(nodes);
            }
        }
    }
    /// Install once before checking on an enabled Profile; clones share the first
    /// observer. Create a fresh Profile for a new observation sink. Detailed
    /// observation is opt-in independently of memory spans; disabled runs do no
    /// atom cloning or per-producer locking.
    pub fn observe_conditions(&self, send: impl Fn(ConditionProfileEvent) + Send + Sync + 'static) {
        if let Some(s) = &self.0 {
            let _ = s.observer.set(Box::new(send));
        }
    }
    pub fn conditions_enabled(&self) -> bool {
        self.0.as_ref().is_some_and(|s| s.observer.get().is_some())
    }
    pub(crate) fn condition(&self, make: impl FnOnce() -> ConditionObservation) {
        if let Some(s) = &self.0 {
            if let Some(send) = s.observer.get() {
                let stages = s
                    .condition_peaks
                    .lock()
                    .unwrap()
                    .values()
                    .map(|(stage, _)| *stage)
                    .collect();
                let target = s
                    .targets
                    .lock()
                    .unwrap()
                    .last_key_value()
                    .map(|(_, a)| a.clone());
                send(ConditionProfileEvent {
                    stages,
                    target,
                    observation: make(),
                });
            }
        }
    }
    pub(crate) fn declarations(
        &self,
        make: impl FnOnce() -> (
            Vec<(denotate_ir::RelationId, denotate_ir::RelationKey)>,
            Vec<(denotate_ir::ConstantId, denotate_ir::ConstantKey)>,
        ),
    ) -> ProfileDeclarations {
        let mut ids = Vec::new();
        if self.conditions_enabled() {
            let (relations, constants) = make();
            ids.extend(
                relations
                    .iter()
                    .map(|(id, _)| denotate_ir::OccurrenceId::from(*id)),
            );
            ids.extend(
                constants
                    .iter()
                    .map(|(id, _)| denotate_ir::OccurrenceId::from(*id)),
            );
            self.condition(|| ConditionObservation::BindDeclarations {
                relations,
                constants,
            });
        }
        ProfileDeclarations {
            profile: self.clone(),
            ids,
        }
    }
    pub(crate) fn target(&self, atom: &crate::GroundAtom) -> ConditionTarget {
        let state = self
            .0
            .as_ref()
            .filter(|_| self.conditions_enabled())
            .map(|s| {
                let id = s.next.fetch_add(1, Ordering::Relaxed);
                s.targets.lock().unwrap().insert(id, atom.clone());
                (s.clone(), id)
            });
        ConditionTarget(state)
    }
    pub fn span(&self, stage: &'static str, round: Option<usize>) -> ProfileSpan {
        let state = self.0.as_ref().map(|s| {
            let id = s.next.fetch_add(1, Ordering::Relaxed);
            s.condition_peaks.lock().unwrap().insert(id, (stage, 0));
            (s.send)(ProfileEvent {
                id,
                stage,
                round,
                finished: false,
                elapsed: Duration::ZERO,
                bdd_results: 0,
                bdd_result_nodes: 0,
                bdd_result_node_bytes: 0,
                retained: None,
                peak_accounted_condition_nodes: 0,
            });
            (
                s.clone(),
                id,
                Instant::now(),
                s.results.load(Ordering::Relaxed),
                s.nodes.load(Ordering::Relaxed),
            )
        });
        ProfileSpan {
            state,
            stage,
            round,
            retained: None,
        }
    }
}
pub(crate) struct ProfileDeclarations {
    profile: Profile,
    ids: Vec<denotate_ir::OccurrenceId>,
}
impl Drop for ProfileDeclarations {
    fn drop(&mut self) {
        if !self.ids.is_empty() {
            let ids = std::mem::take(&mut self.ids);
            self.profile
                .condition(|| ConditionObservation::UnbindDeclarations { ids });
        }
    }
}
pub(crate) struct ConditionTarget(Option<(Arc<State>, u64)>);
impl Drop for ConditionTarget {
    fn drop(&mut self) {
        if let Some((s, id)) = &self.0 {
            s.targets.lock().unwrap().remove(id);
        }
    }
}
pub struct ProfileSpan {
    state: Option<(Arc<State>, u64, Instant, u64, u64)>,
    stage: &'static str,
    round: Option<usize>,
    retained: Option<BddStorage>,
}
impl ProfileSpan {
    pub fn retained(&mut self, value: BddStorage) {
        self.retained = Some(value);
    }
}
impl Drop for ProfileSpan {
    fn drop(&mut self) {
        if let Some((s, id, start, results, nodes)) = &self.state {
            let nodes = s.nodes.load(Ordering::Relaxed).saturating_sub(*nodes);
            let peak = s
                .condition_peaks
                .lock()
                .unwrap()
                .remove(id)
                .map_or(0, |(_, peak)| peak);
            (s.send)(ProfileEvent {
                id: *id,
                stage: self.stage,
                round: self.round,
                finished: true,
                elapsed: start.elapsed(),
                bdd_results: s.results.load(Ordering::Relaxed).saturating_sub(*results),
                bdd_result_nodes: nodes,
                bdd_result_node_bytes: nodes
                    .saturating_mul(std::mem::size_of::<biodivine_lib_bdd::BddNode>() as u64),
                retained: self.retained,
                peak_accounted_condition_nodes: peak,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Limits, limits::Budget, symbolic::retain};

    #[test]
    fn condition_peaks_are_scoped_and_exclude_rejected_storage() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let profile = Profile::new(move |event| out.lock().unwrap().push(event));
        let limits = Limits {
            max_condition_nodes: 20,
            profile: profile.clone(),
            ..Limits::default()
        };
        let mut budget = Budget::new(&limits);
        {
            let _outer = profile.span("outer", None);
            retain(0, 0, 7, &mut budget).unwrap();
            {
                let _inner = profile.span("inner", None);
                retain(0, 0, 12, &mut budget).unwrap();
                assert!(retain(12, 0, 9, &mut budget).is_err());
            }
            retain(0, 0, 3, &mut budget).unwrap();
        }
        drop(profile.span("later", None));
        let events = events.lock().unwrap();
        let peaks: Vec<_> = events
            .iter()
            .filter(|e| e.finished)
            .map(|e| (e.stage, e.peak_accounted_condition_nodes))
            .collect();
        assert_eq!(peaks, [("inner", 12), ("outer", 12), ("later", 0)]);
    }
}
