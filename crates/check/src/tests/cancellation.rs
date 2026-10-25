use crate::*;
use denotate_ir::Corpus;

#[test]
fn cancellation_propagates_without_becoming_inconclusive_even_on_empty_phases() {
    let corpus = Corpus::new();
    let limits = Limits::default();
    let ground = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
    let meaning = ground.symbolic(&limits).unwrap();
    let cancelled = Limits::default();
    cancelled.cancellation.cancel();
    macro_rules! cancelled {
        ($value:expr) => {
            assert!(matches!($value, Err(CheckError::Cancelled)));
        };
    }
    cancelled!(GroundProgram::prepare_checked(
        &corpus,
        &Domains::new(),
        &cancelled
    ));
    cancelled!(ground.symbolic_checked(&cancelled));
    cancelled!(ground.evaluate([], &cancelled));
    cancelled!(ground.certify_observation([], &cancelled));
    cancelled!(meaning.verify_checked(&cancelled));
    cancelled!(meaning.verify_with_phase_limits(&limits, &cancelled, &limits));
    cancelled!(meaning.verify_with_phase_limits(&limits, &limits, &cancelled));
    cancelled!(AnalysisOutcome::<()>::from_result(Err(
        CheckError::Cancelled
    )));
    assert!(meaning.verify_checked(&limits).is_ok()); // A separate run is unaffected.
    cancelled!(ground.admit(&cancelled));
}

#[test]
fn cancellation_from_another_thread_is_seen_at_the_next_budget_charge() {
    let limits = Limits::default();
    let token = limits.cancellation.clone();
    let (started, ready) = std::sync::mpsc::channel();
    let (resume, wait) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let mut budget = crate::limits::Budget::new(&limits);
        budget.tick("first work item").unwrap();
        started.send(()).unwrap();
        wait.recv().unwrap();
        budget.charge(0, "next checkpoint")
    });
    ready.recv().unwrap();
    token.cancel();
    resume.send(()).unwrap();
    assert_eq!(worker.join().unwrap(), Err(CheckError::Cancelled));
}
