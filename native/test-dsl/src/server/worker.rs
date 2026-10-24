//! InputMapping's check payload and closure; scheduling is shared editor machinery.
use crate::analysis::{Failure, Output, Program};
use denotate_editor::checking::{self, Scheduler, Ticket};
use lsp_types::Url;
use std::time::Instant;

pub type Identity = Ticket<Url, i32>;
pub struct Payload {
    pub program: Program,
    pub backend: denotate_check::BackendIdentity,
    pub measure: bool,
}
type Checked = (Result<Output, Failure>, Option<u64>);
pub type Event = checking::Event<Url, Checked, i32>;
pub type Worker = Scheduler<Url, Payload, Checked, i32>;

pub fn spawn() -> std::io::Result<Worker> {
    Worker::spawn(
        "inputmapping-check",
        |job: &checking::Job<Url, Payload, i32>, session, checkpoint| {
            let start = job.payload.measure.then(Instant::now);
            let result = job.payload.program.check_with_backend(
                &job.limits,
                checkpoint,
                job.payload.backend.clone(),
                Some(session),
            );
            let check_ns = start.map(|t| t.elapsed().as_nanos().min(u64::MAX as u128) as u64);
            (result, check_ns)
        },
    )
}
