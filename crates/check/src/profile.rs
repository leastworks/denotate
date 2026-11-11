//! Opt-in observations, outside receipts, semantic keys and cached results.
//! Callbacks own delivery and OS measurements. The checker performs no IO here.
use std::{
    fmt,
    sync::{
        Arc,
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
}
struct State {
    send: Box<dyn Fn(ProfileEvent) + Send + Sync>,
    next: AtomicU64,
    results: AtomicU64,
    nodes: AtomicU64,
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
    pub fn span(&self, stage: &'static str, round: Option<usize>) -> ProfileSpan {
        let state = self.0.as_ref().map(|s| {
            let id = s.next.fetch_add(1, Ordering::Relaxed);
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
            });
        }
    }
}
