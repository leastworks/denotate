use super::*;

#[test]
fn exploration_agrees_with_enumeration_for_signed_loops_and_hypotheses() {
    for left in 0..6 {
        for right in 0..6 {
            let mut c = Corpus::new();
            let i = rel(&mut c, "i", true);
            let x = rel(&mut c, "x", false);
            let y = rel(&mut c, "y", false);
            for (head, other, choice) in [(x, y, left), (y, x, right)] {
                match choice {
                    0 => (),
                    1 => {
                        rule(&mut c, head, &[]);
                    }
                    2 => {
                        rule(&mut c, head, &[(i, false)]);
                    }
                    3 => {
                        rule(&mut c, head, &[(head, false)]);
                    }
                    4 => {
                        rule(&mut c, head, &[(other, true)]);
                    }
                    _ => {
                        rule(&mut c, head, &[(i, false), (head, true)]);
                    }
                }
            }
            for h in [None, Some(x)] {
                let v = verification(&mut c, h, &[]);
                let mut e = prepare(&c, v, &Default::default());
                let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
                let normal = e.check(&keys(&c), &Default::default()).unwrap();
                scale::same_report(&normal, &expected);
                e.limits.completion_exploration = true;
                for force in [false, true] {
                    let options = CheckOptions {
                        prune: true,
                        force,
                        split_depth: 2,
                        ..Default::default()
                    };
                    for (explore, probe) in [
                        (false, 0),
                        (true, 0),
                        (true, Limits::default().completion_probe_work),
                    ] {
                        e.limits.completion_exploration = explore;
                        e.limits.completion_probe_work = probe;
                        for _ in 0..2 {
                            // Invocation-local views must not leak across repeated checks.
                            let got = e.check(&keys(&c), &options).unwrap();
                            scale::same_report(&got, &expected);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn exploration_keeps_deadlines_and_explicit_work_limits() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(x, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.max_work = 0;
    let got = e.check(&keys(&c), &CheckOptions::default());
    assert!(got.is_err() || got.unwrap().is_incomplete());
    e.limits.max_work = Limits::default().max_work;
    e.limits.run_deadline = Some(Instant::now());
    let got = e.check(
        &keys(&c),
        &CheckOptions {
            prune: true,
            split_depth: 2,
            ..Default::default()
        },
    );
    assert!(got.is_err() || got.unwrap().is_incomplete());
}

#[test]
fn exploration_reports_live_work_and_honours_cancellation_during_non_sat_work() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(x, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    let cancellation = e.limits.cancellation.clone();
    let seen = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let flag = seen.clone();
    e.limits.progress = crate::CheckingProgress::new(move |event| {
        if event.state == "progress"
            && matches!(
                event.target,
                Some(crate::CheckingTarget::CompletionExploration {
                    resource: "work",
                    ..
                })
            )
        {
            flag.store(true, std::sync::atomic::Ordering::Relaxed);
            cancellation.cancel();
        }
    });
    // Budget checks publish while the pass is running, before a final report.
    let result = Budget::new(&e.limits).charge(1, "exploration work test");
    assert!(seen.load(std::sync::atomic::Ordering::Relaxed));
    assert!(matches!(result, Err(CheckError::Cancelled)));
}

#[test]
fn exploration_classification_existence_runs_after_gating_questions() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(i, false)]);
    let v = verification(&mut c, Some(h), &[]);
    for explore in [false, true] {
        let mut e = prepare(&c, v, &Default::default());
        e.limits.completion_exploration = explore;
        let events = Arc::new(std::sync::Mutex::new(Vec::new()));
        let sink = events.clone();
        e.limits.progress = crate::CheckingProgress::new(move |event| {
            sink.lock().unwrap().push((event.stage, event.state));
        });
        let got = e.check(&keys(&c), &Default::default()).unwrap();
        scale::same_report(
            &got,
            &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
        );
        let events = events.lock().unwrap();
        let first = |phase| events.iter().position(|(p, _)| *p == phase).unwrap();
        assert_eq!(
            first("completion classification existence") > first("completion processing ambiguity"),
            explore,
            "{events:?}"
        );
    }
}
