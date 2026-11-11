use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load};
use std::sync::{Arc, Mutex};

fn program(text: &str) -> LoadedProgram {
    let file = SourceFile::new("file:///progress.den", 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

#[test]
fn checking_progress_preserves_cold_warm_results_receipts_and_releases_sink() {
    let p = program(
        "sort S; const a,b:S; input i(x:S); relation r(x:S); r(X):-i(X); obligation e:empty(r); obligation c:at_least_one(r,group_by:()); obligation u:at_most_one(r,group_by:()); relation any(); any():-r(X); notice n:varies(any); verification v{assumptions:[];obligations:[e,c,u];notices:[n];}",
    );
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    let ops = OperationalLimits::from(&limits);
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let mut session = Session::default();
    let LocalCheckOutcome::Complete(quiet) = session.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    for session in [&mut session, &mut Session::default()] {
        let events = Arc::new(Mutex::new(Vec::new()));
        let weak = Arc::downgrade(&events);
        let send = events.clone();
        let observed = OperationalLimits {
            progress: CheckingProgress::new(move |e| send.lock().unwrap().push(e)),
            ..ops.clone()
        };
        let LocalCheckOutcome::Complete(actual) = session.verify(&prepared, &observed).unwrap()
        else {
            panic!()
        };
        assert_eq!(actual.checked.results, quiet.checked.results);
        for stage in [
            "uniqueness",
            "emptiness",
            "coverage",
            "notice",
            "replay",
            "certification",
        ] {
            assert!(
                events.lock().unwrap().iter().any(|e| e.stage == stage),
                "{stage}"
            );
        }
        assert!(
            events
                .lock()
                .unwrap()
                .iter()
                .any(|e| matches!(e.target, Some(CheckingTarget::Obligation(_))))
        );
        assert!(
            events.lock().unwrap().iter().all(|e| match e.target {
                Some(CheckingTarget::Obligation(id)) => p.corpus.obligation(id).is_some(),
                Some(CheckingTarget::Notice(id)) => p.corpus.notice(id).is_some(),
                _ => true,
            }),
            "private runtimes must keep source-bound targets"
        );
        drop(observed);
        drop(events);
        assert!(
            weak.upgrade().is_none(),
            "session must not retain the progress callback"
        );
    }
    let CheckOutcome::Complete(quiet) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let events = Arc::new(Mutex::new(Vec::new()));
    let send = events.clone();
    let observed = OperationalLimits {
        progress: CheckingProgress::new(move |e| send.lock().unwrap().push(e)),
        ..ops
    };
    let CheckOutcome::Complete(actual) = prepared.verify(&observed).unwrap() else {
        panic!()
    };
    assert_eq!(actual.results, quiet.results);
    assert!(
        events
            .lock()
            .unwrap()
            .iter()
            .any(|e| e.stage == "emptiness")
    );
}

#[test]
fn checking_exhaustion_is_reported_before_the_next_region_including_cached_results() {
    let p = program(
        "relation a(); a():-!a(); relation b(); b():-!b(); verification v{assumptions:[];obligations:[];}",
    );
    let mut exercised = false;
    for nodes in 0..160 {
        let limits = Limits {
            max_condition_nodes: nodes,
            ..Limits::default()
        };
        let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
        let ops = OperationalLimits::from(&limits);
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            continue;
        };
        let prepared = prepared.admit(&ops).unwrap();
        let mut session = Session::default();
        let quiet = session.verify(&prepared, &ops).unwrap();
        let LocalCheckOutcome::Complete(quiet) = quiet else {
            continue;
        };
        for session in [&mut session, &mut Session::default()] {
            let events = Arc::new(Mutex::new(Vec::new()));
            let send = events.clone();
            let observed = OperationalLimits {
                progress: CheckingProgress::new(move |e| send.lock().unwrap().push(e)),
                ..ops.clone()
            };
            let LocalCheckOutcome::Complete(actual) = session.verify(&prepared, &observed).unwrap()
            else {
                panic!()
            };
            assert_eq!(actual.checked.results, quiet.checked.results);
            let events = events.lock().unwrap();
            for (index, event) in events.iter().enumerate() {
                let Some(CheckingTarget::Component(first)) = &event.target else {
                    continue;
                };
                if event.state != "exhausted" {
                    continue;
                }
                if events[index+1..].iter().any(|e|e.state=="started" && matches!(&e.target,Some(CheckingTarget::Component(c)) if c.index!=first.index)) {
                    assert!(event.continues);
                    assert!(matches!(event.failure,Some(CheckError::LimitExceeded{..})));
                    exercised=true;
                }
            }
        }
        if exercised {
            break;
        }
    }
    assert!(
        exercised,
        "exercise a region exhaustion before the next region starts"
    );
}

#[test]
fn checking_deadline_reports_stop_and_does_not_retain_the_sink() {
    let p = program(
        "relation r(); obligation e:empty(r); verification v{assumptions:[];obligations:[e];}",
    );
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    let ops = OperationalLimits::from(&limits);
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let events = Arc::new(Mutex::new(Vec::new()));
    let send = events.clone();
    let weak = Arc::downgrade(&events);
    let observed = OperationalLimits {
        timeout: std::time::Duration::ZERO,
        progress: CheckingProgress::new(move |e| send.lock().unwrap().push(e)),
        ..ops
    };
    let mut session = Session::default();
    assert!(matches!(
        session.verify(&prepared, &observed),
        Err(CheckError::Deadline { .. })
    ));
    assert!(events.lock().unwrap().iter().any(|e| e.state == "exhausted"
        && !e.continues
        && matches!(e.failure, Some(CheckError::Deadline { .. }))));
    drop(observed);
    drop(events);
    assert!(weak.upgrade().is_none());
}
