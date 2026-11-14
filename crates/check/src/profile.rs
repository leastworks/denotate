//! Opt-in observations, outside receipts, semantic keys and cached results.
//! Callbacks own delivery and OS measurements. The checker performs no IO here.
use std::{
    collections::BTreeMap,
    fmt,
    sync::{
        Arc, Mutex,
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
struct State {
    send: Box<dyn Fn(ProfileEvent) + Send + Sync>,
    next: AtomicU64,
    results: AtomicU64,
    nodes: AtomicU64,
    condition_peaks: Mutex<BTreeMap<u64, usize>>,
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
            for peak in s.condition_peaks.lock().unwrap().values_mut() {
                *peak = (*peak).max(nodes);
            }
        }
    }
    pub fn span(&self, stage: &'static str, round: Option<usize>) -> ProfileSpan {
        let state = self.0.as_ref().map(|s| {
            let id = s.next.fetch_add(1, Ordering::Relaxed);
            s.condition_peaks.lock().unwrap().insert(id, 0);
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
            let peak = s.condition_peaks.lock().unwrap().remove(id).unwrap_or(0);
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
