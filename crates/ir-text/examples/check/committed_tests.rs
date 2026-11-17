use super::*;
use std::{fs, io::Write};
use tests::Fixture;

const CYCLE: &str = "input x(); relation a(); relation b(); a() :- x(), !b(); b() :- !x(), !a();
    relation bad(); obligation clean: empty(bad); notice varies: varies(a);
    verification checks { assumptions: []; obligations: [clean]; notices: [varies]; }";

#[test]
fn committed_cli_stop_without_progress_is_incomplete_and_resumes() {
    let source = Fixture::new(CYCLE);
    let destination = Fixture::new("");
    let file = destination.0.join("committed.den");
    let (status, output, trace) = source.traced(&[
        "--no-progress",
        "--export-committed",
        file.to_str().unwrap(),
        "--stop-after-round",
        "1",
    ]);
    assert_eq!(status.as_ref().err().map(|e| e.0), Some(2));
    assert!(status.unwrap_err().1.contains("Stopped after round 1"));
    assert!(
        !output.contains("proved"),
        "checking must not run after an intentional stop"
    );
    assert!(trace.contains("Committed export:"));
    let text = fs::read_to_string(&file).unwrap();
    assert!(text.contains("\"state\":\"stopped\""));
    assert!(text.contains("\"checkerCommit\":"));
    let (code, output) = destination.run(&["--no-progress", "--json"]);
    assert_eq!(
        code, 0,
        "already-applied rewrite warnings are absent on resume"
    );
    assert!(output.contains("\"state\": \"proved\""));
    assert!(output.contains("\"outcome\": \"proved\""));

    // A round with no commit still has a boundary; stopping must not depend
    // on receiving a commit event or on having progress enabled.
    let unresolved = Fixture::new(
        "relation a(); relation b(); a() :- !b(); b() :- !a(); verification checks { assumptions: []; obligations: []; }",
    );
    let destination = Fixture::new("");
    let file = destination.0.join("committed.den");
    let (status, _, _) = unresolved.traced(&[
        "--no-progress",
        "--export-committed",
        file.to_str().unwrap(),
        "--stop-after-round",
        "1",
    ]);
    assert!(status.unwrap_err().1.contains("Stopped after round 1"));
    assert!(
        fs::read_to_string(file)
            .unwrap()
            .contains("\"state\":\"stopped\"")
    );
}

#[test]
fn committed_cli_single_selection_early_completion_and_export_failures() {
    let source = Fixture::new(
        "relation r(); obligation o: empty(r); verification v { assumptions: []; obligations: [o]; }",
    );
    let destination = Fixture::new("");
    let file = destination.0.join("committed.den");
    let path = file.to_str().unwrap();
    let (code, text) = source.run(&[
        "--no-progress",
        "--export-committed",
        path,
        "--stop-after-round",
        "4",
    ]);
    assert_eq!(code, 0, "{text}");
    assert!(
        fs::read_to_string(&file)
            .unwrap()
            .contains("\"state\":\"complete\"")
    );
    let before = fs::read(&file).unwrap();
    assert_eq!(
        source.run(&["--no-progress", "--export-committed", path]).0,
        0,
        "export failure does not change verdict"
    );
    assert_eq!(fs::read(&file).unwrap(), before, "no overwrite");
    fs::remove_file(&file).unwrap();
    for flag in [
        "--export-max-bytes",
        "--export-max-work",
        "--export-timeout-ms",
    ] {
        let (code, _, trace) =
            source.traced(&["--no-progress", "--export-committed", path, flag, "0"]);
        assert_eq!(code.unwrap(), 0);
        assert!(trace.contains("Committed export failed:"));
        assert!(!file.exists());
    }
    assert_eq!(
        fs::read_dir(&destination.0).unwrap().count(),
        2,
        "no temporary file remains"
    );
    let multi = Fixture::new(
        "verification a { assumptions: []; obligations: []; } verification b { assumptions: []; obligations: []; }",
    );
    let (code, text) = multi.run(&["--no-progress", "--export-committed", path]);
    assert_eq!(code, 2);
    assert!(text.contains("exactly one verification"));
    assert!(!file.exists());
    let (code, _) = multi.run(&[
        "--no-progress",
        "--export-committed",
        path,
        "--verification",
        "b",
    ]);
    assert_eq!(code, 2, "existing partial-run policy");
    let text = fs::read_to_string(file).unwrap();
    assert!(text.contains("verification b"));
    assert!(!text.contains("verification a"));
    assert!(
        source
            .run(&["--stop-after-round", "1"])
            .1
            .contains("requires --export-committed")
    );
}

#[test]
fn committed_atomic_publication_cancellation_during_streaming_leaves_nothing() {
    let source = Fixture::new(CYCLE);
    let (membership, sources) = filesystem::discover(&source.0).unwrap();
    let p = denotate_ir_text::load(&membership, &sources).unwrap();
    let limits = Limits::default();
    let ops = (&limits).into();
    let req = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = req.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let destination = Fixture::new("");
    let file = destination.0.join("committed.den");
    let export_limits = denotate_ir_text::committed::ExportLimits::default();
    struct CancelAfterWrite<'a, W> {
        writer: W,
        token: &'a denotate_check::Cancellation,
    }
    impl<W: Write> Write for CancelAfterWrite<'_, W> {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            let n = self.writer.write(bytes)?;
            self.token.cancel();
            Ok(n)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.writer.flush()
        }
    }
    let result = committed::publish(&file, &export_limits, |writer| {
        denotate_ir_text::committed::write_committed(
            CancelAfterWrite {
                writer,
                token: &export_limits.cancellation,
            },
            &p.corpus,
            prepared.program(),
            p.corpus.verifications().next().unwrap(),
            &denotate_ir_text::committed::Metadata {
                source_digest: "test",
                checker_commit: "test",
                round: 0,
                state: "test",
            },
            &export_limits,
        )
    });
    assert!(result.unwrap_err().to_string().contains("Cancelled"));
    assert!(!file.exists());
    assert_eq!(fs::read_dir(&destination.0).unwrap().count(), 2);
}

#[test]
fn committed_export_has_its_own_deadline_after_admission_deadline() {
    let source = Fixture::new(CYCLE);
    let (membership, sources) = filesystem::discover(&source.0).unwrap();
    let p = denotate_ir_text::load(&membership, &sources).unwrap();
    let limits = Limits::default();
    let ops = (&limits).into();
    let req = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = req.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let mut expired = OperationalLimits::from(&limits);
    expired.timeout = std::time::Duration::ZERO;
    let destination = Fixture::new("");
    let file = destination.0.join("committed.den");
    let dump = |e: denotate_check::AdmissionDump<'_>| {
        if let denotate_check::AdmissionDumpEvent::Graph {
            state,
            round,
            error,
        } = e.event
        {
            assert!(matches!(error, Some(CheckError::Deadline { .. })));
            committed::publish(&file, &Default::default(), |w| {
                denotate_ir_text::committed::write_committed(
                    w,
                    &p.corpus,
                    e.program,
                    p.corpus.verifications().next().unwrap(),
                    &denotate_ir_text::committed::Metadata {
                        source_digest: "test",
                        checker_commit: "test",
                        round,
                        state,
                    },
                    &Default::default(),
                )
            })
            .unwrap();
        }
    };
    assert!(matches!(
        prepared.admit_with_diagnostics(&expired, None, None, Some(&dump)),
        Err(CheckError::Deadline { .. })
    ));
    assert_eq!(
        destination.run(&["--no-progress"]).0,
        source.run(&["--no-progress"]).0
    );
}
