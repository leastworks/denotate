//! Serial checking mechanics. The owner supplies context identities, immutable
//! payloads, checking and publication policy. No language or LSP concepts here.
use crossbeam_channel::{bounded, unbounded, Receiver, Sender};
use denotate_check::{Cancellation, Limits};
use denotate_check_session::Session;
use std::{
    collections::{BTreeMap, VecDeque},
    io,
    thread::JoinHandle,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ticket<K, M = ()> {
    pub key: K,
    pub revision: u64,
    pub metadata: M,
}
pub struct Job<K, P, M = ()> {
    pub ticket: Ticket<K, M>,
    pub payload: P,
    pub limits: Limits,
}
/// DuringCheck is reached explicitly by the supplied check closure; BeforeResult
/// is always after that closure, including its final cancellation check.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HoldStage {
    DuringCheck,
    BeforeResult,
}
pub enum Event<K, O, M = ()> {
    Checkpoint(Ticket<K, M>),
    Finished(Ticket<K, M>, O),
}
struct Hold {
    stage: HoldStage,
    release: Receiver<()>,
}
enum Command<K, P, M> {
    Check(Job<K, P, M>, Option<Hold>),
    Close(K),
    Reset,
}
struct Active<K, M> {
    ticket: Ticket<K, M>,
    cancellation: Cancellation,
}

pub struct Scheduler<K, P, O, M = ()> {
    jobs: Option<Sender<Command<K, P, M>>>,
    events: Receiver<Event<K, O, M>>,
    thread: Option<JoinHandle<()>>,
    pending: VecDeque<Job<K, P, M>>,
    active: Option<Active<K, M>>,
    revision: u64,
    next_hold: Option<HoldStage>,
    releases: BTreeMap<u64, Sender<()>>,
}
fn stopped() -> io::Error {
    io::Error::new(io::ErrorKind::BrokenPipe, "Checking worker stopped")
}
impl<K, P, O, M> Scheduler<K, P, O, M>
where
    K: Ord + Clone + Send + 'static,
    P: Send + 'static,
    O: Send + 'static,
    M: Clone + Send + 'static,
{
    pub fn spawn(
        name: &str,
        mut check: impl FnMut(&Job<K, P, M>, &mut Session, &dyn Fn()) -> O + Send + 'static,
    ) -> io::Result<Self> {
        let (jobs, pending) = unbounded::<Command<K, P, M>>();
        let (send, events) = unbounded();
        let thread = std::thread::Builder::new()
            .name(name.into())
            .spawn(move || {
                let mut sessions = BTreeMap::<K, Session>::new();
                for command in pending {
                    let (job, hold) = match command {
                        Command::Close(key) => {
                            sessions.remove(&key);
                            continue;
                        }
                        Command::Reset => {
                            sessions.clear();
                            continue;
                        }
                        Command::Check(job, hold) => (job, hold),
                    };
                    let checkpoint = |stage| {
                        if let Some(hold) = &hold {
                            if hold.stage == stage {
                                let _ = send.send(Event::Checkpoint(job.ticket.clone()));
                                let _ = hold.release.recv();
                            }
                        }
                    };
                    let output = check(
                        &job,
                        sessions.entry(job.ticket.key.clone()).or_default(),
                        &|| checkpoint(HoldStage::DuringCheck),
                    );
                    checkpoint(HoldStage::BeforeResult);
                    if send.send(Event::Finished(job.ticket, output)).is_err() {
                        break;
                    }
                }
            })?;
        Ok(Self {
            jobs: Some(jobs),
            events,
            thread: Some(thread),
            pending: VecDeque::new(),
            active: None,
            revision: 0,
            next_hold: None,
            releases: BTreeMap::new(),
        })
    }
    pub fn events(&self) -> &Receiver<Event<K, O, M>> {
        &self.events
    }
    /// Allocate an observation identity before frontend preparation. This cancels
    /// active work but preserves the queued context's position. In the same owner
    /// turn, enqueue the prepared payload or cancel the uncheckable context.
    pub fn ticket(&mut self, key: K, metadata: M) -> Ticket<K, M> {
        self.cancel_active(&key);
        self.revision = self
            .revision
            .checked_add(1)
            .expect("Checking revision overflow");
        Ticket {
            key,
            revision: self.revision,
            metadata,
        }
    }
    fn cancel_active(&self, key: &K) {
        if let Some(a) = &self.active {
            if &a.ticket.key == key {
                a.cancellation.cancel();
            }
        }
    }
    pub fn enqueue(&mut self, job: Job<K, P, M>) {
        self.cancel_active(&job.ticket.key);
        // Replacing a pending job preserves FIFO position. A replacement for
        // an active context joins the tail behind other waiting contexts.
        if let Some(pending) = self
            .pending
            .iter_mut()
            .find(|p| p.ticket.key == job.ticket.key)
        {
            *pending = job;
        } else {
            self.pending.push_back(job);
        }
    }
    /// Cancel work without releasing the context's warm session.
    pub fn cancel(&mut self, key: &K) {
        self.cancel_active(key);
        self.pending.retain(|p| &p.ticket.key != key);
    }
    pub fn close(&mut self, key: &K) -> io::Result<()> {
        self.cancel(key);
        self.send(Command::Close(key.clone()))
    }
    pub fn pending(&self) -> impl Iterator<Item = &Job<K, P, M>> {
        self.pending.iter()
    }
    /// Operational-limit injection for deterministic deadline tests.
    pub fn pending_limits_mut(&mut self, key: &K) -> Option<&mut Limits> {
        self.pending
            .iter_mut()
            .find(|p| &p.ticket.key == key)
            .map(|p| &mut p.limits)
    }
    pub fn is_idle(&self) -> bool {
        self.active.is_none() && self.pending.is_empty()
    }
    pub fn start(&mut self) -> io::Result<Option<Ticket<K, M>>> {
        if self.active.is_some() {
            return Ok(None);
        }
        let Some(job) = self.pending.pop_front() else {
            return Ok(None);
        };
        let ticket = job.ticket.clone();
        let hold = self.next_hold.take().map(|stage| {
            let (send, release) = bounded(1);
            self.releases.insert(ticket.revision, send);
            Hold { stage, release }
        });
        self.active = Some(Active {
            ticket: ticket.clone(),
            cancellation: job.limits.cancellation.clone(),
        });
        self.send(Command::Check(job, hold))?;
        Ok(Some(ticket))
    }
    /// Call at the publication boundary, after processing queued edits. Completion
    /// is distinct from checking-idle: other contexts may still be queued. The
    /// frontend predicate validates current observations; the caller publishes.
    pub fn complete(
        &mut self,
        ticket: &Ticket<K, M>,
        still_current: impl FnOnce() -> bool,
    ) -> bool {
        let active = self
            .active
            .take()
            .expect("Checking result without an active job");
        assert!(
            active.ticket.key == ticket.key && active.ticket.revision == ticket.revision,
            "Checking result does not match the active job"
        );
        self.releases.remove(&ticket.revision);
        still_current()
    }
    pub fn hold_next(&mut self, stage: HoldStage) {
        self.next_hold = Some(stage);
    }
    pub fn release(&mut self, revision: u64) -> bool {
        self.releases.remove(&revision).is_some_and(|send| {
            let _ = send.send(());
            true
        })
    }
    pub fn reset_sessions(&mut self) -> io::Result<()> {
        if !self.is_idle() {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "Checking must be idle before resetting sessions",
            ));
        }
        self.send(Command::Reset)
    }
    fn send(&self, command: Command<K, P, M>) -> io::Result<()> {
        self.jobs
            .as_ref()
            .ok_or_else(stopped)?
            .send(command)
            .map_err(|_| stopped())
    }
}
impl<K, P, O, M> Scheduler<K, P, O, M> {
    /// Also releases held test checkpoints, so shutdown never waits for a client.
    pub fn stop(&mut self) {
        if let Some(a) = &self.active {
            a.cancellation.cancel();
        }
        self.pending.clear();
        self.next_hold = None;
        self.releases.clear();
        self.jobs.take();
        if let Some(thread) = self.thread.take() {
            if thread.join().is_err() {
                eprintln!("Checking worker panicked");
            }
        }
    }
}
impl<K, P, O, M> Drop for Scheduler<K, P, O, M> {
    fn drop(&mut self) {
        self.stop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    type TestScheduler = Scheduler<&'static str, usize, (usize, bool, usize)>;
    fn scheduler() -> TestScheduler {
        Scheduler::spawn(
            "checking-test",
            |job: &Job<&'static str, usize>, session, checkpoint| {
                checkpoint();
                let visits = session.stats().resets;
                session.reset();
                (
                    job.payload,
                    job.limits.cancellation.check().is_err(),
                    visits,
                )
            },
        )
        .unwrap()
    }
    fn enqueue(s: &mut TestScheduler, key: &'static str, value: usize) -> Ticket<&'static str> {
        let ticket = s.ticket(key, ());
        s.enqueue(Job {
            ticket: ticket.clone(),
            payload: value,
            limits: Limits::default(),
        });
        ticket
    }
    fn finished(s: &TestScheduler) -> (Ticket<&'static str>, (usize, bool, usize)) {
        match s.events().recv_timeout(Duration::from_secs(5)).unwrap() {
            Event::Finished(ticket, output) => (ticket, output),
            _ => panic!("expected completed check"),
        }
    }
    #[test]
    fn fifo_replacement_cancellation_and_publication_gate_are_independent_of_idle() {
        let mut s = scheduler();
        let first = enqueue(&mut s, "a", 1);
        s.hold_next(HoldStage::DuringCheck);
        s.start().unwrap();
        assert!(
            matches!(s.events().recv_timeout(Duration::from_secs(5)).unwrap(), Event::Checkpoint(t) if t == first)
        );
        enqueue(&mut s, "b", 2);
        enqueue(&mut s, "c", 3);
        enqueue(&mut s, "b", 4);
        let latest = enqueue(&mut s, "a", 5);
        assert!(latest.revision > first.revision);
        assert_eq!(
            s.pending().map(|j| j.payload).collect::<Vec<_>>(),
            [4, 3, 5]
        );
        assert!(s.reset_sessions().is_err());
        assert!(s.start().unwrap().is_none());
        assert!(s.release(first.revision));
        let (ticket, output) = finished(&s);
        assert!(output.1, "active check observes cancellation");
        assert!(!s.complete(&ticket, || ticket == latest));
        assert!(!s.is_idle(), "finished is not checking-idle");
        for expected in [4, 3, 5] {
            s.start().unwrap();
            let (ticket, output) = finished(&s);
            assert_eq!(output.0, expected);
            assert!(!output.1);
            assert!(s.complete(&ticket, || true));
        }
        assert!(s.is_idle());
    }
    #[test]
    fn completed_before_cancellation_still_needs_the_publication_predicate() {
        let mut s = scheduler();
        let old = enqueue(&mut s, "a", 1);
        s.hold_next(HoldStage::BeforeResult);
        s.start().unwrap();
        assert!(
            matches!(s.events().recv_timeout(Duration::from_secs(5)).unwrap(), Event::Checkpoint(t) if t == old)
        );
        let new = s.ticket("a", ());
        s.cancel(&"a");
        s.release(old.revision);
        let (ticket, output) = finished(&s);
        assert!(!output.1, "result completed before the edit");
        assert!(!s.complete(&ticket, || ticket == new));
        assert!(s.is_idle());
    }
    #[test]
    fn cancellation_keeps_sessions_but_close_and_cold_reset_release_them() {
        let mut s = scheduler();
        for (value, expected_visits) in [(1, 0), (2, 1), (3, 0), (4, 0)] {
            enqueue(&mut s, "a", value);
            s.start().unwrap();
            let (ticket, output) = finished(&s);
            assert_eq!(output.2, expected_visits);
            s.complete(&ticket, || true);
            match value {
                1 => {
                    enqueue(&mut s, "a", 99);
                    s.cancel(&"a");
                }
                2 => s.close(&"a").unwrap(),
                3 => s.reset_sessions().unwrap(),
                _ => (),
            }
        }
    }
    #[test]
    fn shutdown_releases_both_checkpoint_stages_and_queued_work() {
        for stage in [HoldStage::DuringCheck, HoldStage::BeforeResult] {
            let mut s = scheduler();
            enqueue(&mut s, "a", 1);
            enqueue(&mut s, "b", 2);
            s.hold_next(stage);
            s.start().unwrap();
            assert!(matches!(
                s.events().recv_timeout(Duration::from_secs(5)).unwrap(),
                Event::Checkpoint(_)
            ));
            s.stop();
            assert_eq!(s.pending().count(), 0);
            let (_, output) = finished(&s);
            assert_eq!(output.0, 1);
            assert!(s.events().recv().is_err());
        }
    }
}
