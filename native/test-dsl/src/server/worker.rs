//! One serial checking worker. The server owns coalescing, cancellation and publication.
use crossbeam_channel::{Receiver, Sender, unbounded};
use denotate_check::Limits;
use denotate_test_dsl::analysis::{Failure, Output, Program};
use lsp_types::Url;
use std::thread::{self, JoinHandle};
use std::time::Instant;

#[derive(Clone)]
pub struct Identity {
    pub uri: Url,
    pub revision: u64,
    pub version: i32,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HoldStage {
    AfterPrepare,
    BeforeResult,
}
pub struct Hold {
    pub stage: HoldStage,
    pub release: Receiver<()>,
}
pub struct Job {
    pub id: Identity,
    pub program: Program,
    pub limits: Limits,
    /// Test-only checkpoint, assigned by the server only in explicit test mode.
    pub hold: Option<Hold>,
    pub measure: bool,
}
pub enum Event {
    Checkpoint(Identity),
    Finished(Identity, Result<Output, Failure>, Option<u64>),
}
pub struct Worker {
    pub jobs: Sender<Job>,
    pub events: Receiver<Event>,
    thread: JoinHandle<()>,
}
impl Worker {
    pub fn spawn() -> std::io::Result<Self> {
        let (jobs, pending) = unbounded::<Job>();
        let (send, events) = unbounded();
        let thread = thread::Builder::new()
            .name("inputmapping-check".into())
            .spawn(move || {
                for job in pending {
                    let checkpoint = |stage| {
                        if let Some(hold) = &job.hold {
                            if hold.stage == stage {
                                let _ = send.send(Event::Checkpoint(job.id.clone()));
                                let _ = hold.release.recv();
                            }
                        }
                    };
                    let start = job.measure.then(Instant::now);
                    let result = job
                        .program
                        .check(&job.limits, || checkpoint(HoldStage::AfterPrepare));
                    let check_ns =
                        start.map(|t| t.elapsed().as_nanos().min(u64::MAX as u128) as u64);
                    // Deliberately after checking's final cancellation test: exercises
                    // the publication gate even if a result completed before an edit.
                    checkpoint(HoldStage::BeforeResult);
                    if send
                        .send(Event::Finished(job.id, result, check_ns))
                        .is_err()
                    {
                        break;
                    }
                }
            })?;
        Ok(Self {
            jobs,
            events,
            thread,
        })
    }
    pub fn join(self) {
        drop(self.jobs);
        if self.thread.join().is_err() {
            eprintln!("InputMapping worker panicked");
        }
    }
}
