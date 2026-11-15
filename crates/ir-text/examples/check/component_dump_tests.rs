use super::{component_dump::Dump, tests::Fixture, trace::Trace};
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use serde_json::Value;
use std::{
    cell::{Cell, RefCell},
    fs,
    path::Path,
    time::Duration,
};

const CYCLE: &str = "relation a(); relation b(); a():-!b();b():-!a();\nrelation bad();obligation clean:empty(bad);\nsort S;const left,right:S;input choice(s:S);assumption exclusive:at_most_one(choice,group_by:());\nverification free{assumptions:[];obligations:[clean];} verification selected{assumptions:[exclusive];obligations:[clean];}";
const CHAIN: &str = include_str!("../../tests/fixtures/guarded-chain.den");
fn records(path: &Path) -> Vec<Value> {
    fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect()
}
fn normalized(mut records: Vec<Value>) -> Vec<Value> {
    for r in &mut records {
        r.as_object_mut().unwrap().remove("snapshot");
    }
    records
}
fn loaded(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///dump.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
}

#[test]
fn component_dump_multiple_contexts_determinism_and_output_parity() {
    let f = Fixture::new(CYCLE);
    let (code, output, _) = f.traced(&["--json", "--no-progress"]);
    let mut runs = Vec::new();
    for name in ["first.jsonl", "second.jsonl"] {
        let file = f.0.join(name);
        let (got, text, trace) = f.traced(&[
            "--json",
            "--no-progress",
            "--dump-component",
            file.to_str().unwrap(),
        ]);
        assert_eq!(got, code);
        assert_eq!(text, output);
        assert!(trace.is_empty(), "{trace}");
        runs.push(normalized(records(&file)));
    }
    assert_eq!(runs[0], runs[1]);
    let r = &runs[0];
    assert_eq!(
        r.iter()
            .filter(|r| r["record"] == "graph-end" && r["complete"] == true)
            .count(),
        2
    );
    assert_eq!(r.iter().filter(|r| r["record"] == "component").count(), 2);
    let groups = r
        .iter()
        .filter(|r| r["record"] == "exclusive-group")
        .collect::<Vec<_>>();
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0]["members"].as_array().unwrap().len(), 2);
    assert!(
        r.iter()
            .any(|r| r["record"] == "dependency" && r["premise"]["polarity"] == "negative")
    );
    assert!(
        r.iter()
            .any(|r| r["record"] == "rule" && r["rule"]["source"]["uri"].is_string())
    );
}

#[test]
fn component_dump_guard_pruning_and_sources_are_from_the_attempt_snapshot() {
    let f = Fixture::new(CHAIN);
    let file = f.0.join("attempts.jsonl");
    let baseline = f.run(&["--json", "--no-progress"]);
    assert_eq!(
        baseline,
        f.run(&[
            "--json",
            "--no-progress",
            "--dump-component",
            file.to_str().unwrap()
        ])
    );
    let r = records(&file);
    assert!(!r.iter().any(|r| r["record"] == "truncated"));
    assert!(
        r.iter()
            .any(|r| r["record"] == "attempt" && r["impliedGuard"].is_object())
    );
    assert!(r.iter().any(|r| r["record"] == "attempt"
        && r["before"]["atoms"].as_u64() > r["after"]["atoms"].as_u64()));
    assert!(
        r.iter()
            .any(|r| r["record"] == "dead-producer" && r["reason"]["kind"] == "positive-premise")
    );
    assert!(r.iter().any(|r| r["record"] == "implied-source"));
    assert!(r.iter().any(|r| r["record"] == "pruning-source"));
    assert!(
        r.iter()
            .any(|r| r["record"] == "attempt-outcome" && r["state"] == "settled")
    );
    // Retained attempted cones preceded the final graph: do not reconstruct them
    // from the completely admitted result, where no unresolved component remains.
    assert_eq!(
        r.iter().find(|r| r["record"] == "graph-end").unwrap()["components"],
        0
    );
    assert!(r.iter().any(|r| r["record"] == "cone-atom"));
}

#[test]
fn component_dump_truncation_and_creation_failure_do_not_change_exit_codes() {
    for text in [
        CYCLE,
        CHAIN,
        "relation bad();bad();obligation clean:empty(bad);verification v{assumptions:[];obligations:[clean];}",
        "relation bad();obligation clean:empty(bad);verification v{assumptions:[];obligations:[clean];}",
    ] {
        let f = Fixture::new(text);
        let file = f.0.join("bounded.jsonl");
        let expected = f.traced(&["--json", "--no-progress"]);
        let got = f.traced(&[
            "--json",
            "--no-progress",
            "--dump-component",
            file.to_str().unwrap(),
            "--dump-component-limit",
            "1",
        ]);
        assert_eq!((&got.0, &got.1), (&expected.0, &expected.1));
        assert!(got.2.contains("truncated"));
        let r = records(&file);
        assert!(r.iter().any(|r|r["record"]=="truncated" && r["omittedRecords"]["kind"]=="lower-bound"));
        let saved = fs::read(&file).unwrap();
        let failed = f.traced(&[
            "--json",
            "--no-progress",
            "--dump-component",
            file.to_str().unwrap(),
        ]);
        assert_eq!((&failed.0, &failed.1), (&expected.0, &expected.1));
        assert!(failed.2.contains("dump unavailable"));
        assert_eq!(fs::read(file).unwrap(), saved);
    }
}

#[test]
fn component_dump_fresh_cold_warm_and_reused_graphs_agree() {
    let f = Fixture::new(CYCLE);
    let p = loaded(CYCLE);
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let v = p.corpus.verifications().find(|v| v.name == "free").unwrap();
    let mut session = Session::default();
    let fixed = session
        .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
        .unwrap();
    let mut graphs = Vec::new();
    for mode in ["fresh", "cold", "warm", "reused"] {
        let file = f.0.join(format!("{mode}.jsonl"));
        let dump = RefCell::new(
            Dump::open(
                file.to_str().unwrap(),
                100_000,
                &Trace::new(Vec::new(), false),
            )
            .unwrap(),
        );
        let prepared = if mode == "fresh" {
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        } else {
            session
                .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
                .unwrap()
        };
        let RequestPreparation::Complete(prepared) = prepared else {
            panic!()
        };
        let observer = |e: AdmissionDump<'_>| dump.borrow_mut().capture(&p, v, e);
        prepared
            .admit_with_diagnostics(&ops, None, None, Some(&observer))
            .unwrap();
        drop(dump);
        let mut r = normalized(records(&file));
        let state = r.iter().find(|r| r["record"] == "graph-begin").unwrap()["state"].clone();
        assert_eq!(
            state,
            if mode == "warm" || mode == "reused" {
                "reused"
            } else {
                "complete"
            }
        );
        if state == "reused" {
            assert!(!r.iter().any(|r| r["record"] == "attempt"));
        }
        r.iter_mut()
            .filter(|r| r["record"] == "graph-begin")
            .for_each(|r| {
                r["state"] = Value::Null;
            });
        let begin = r.iter().position(|r| r["record"] == "graph-begin").unwrap();
        graphs.push(r.split_off(begin));
    }
    for graph in &graphs[1..] {
        assert_eq!(&graphs[0], graph);
    }
}

#[test]
fn component_dump_survives_admission_deadline_and_mid_attempt_cancellation() {
    let f = Fixture::new(CHAIN);
    let p = loaded(CHAIN);
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let v = p.corpus.verifications().next().unwrap();
    for mode in ["deadline", "cancel"] {
        let file = f.0.join(format!("{mode}.jsonl"));
        let dump = RefCell::new(
            Dump::open(
                file.to_str().unwrap(),
                100_000,
                &Trace::new(Vec::new(), false),
            )
            .unwrap(),
        );
        let RequestPreparation::Complete(prepared) = request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!()
        };
        let mut ops = OperationalLimits::from(&limits);
        if mode == "deadline" {
            ops.timeout = Duration::ZERO;
        }
        let seen = Cell::new(false);
        let observer = |e: AdmissionDump<'_>| {
            let attempt = matches!(e.event, AdmissionDumpEvent::Guarded { .. });
            dump.borrow_mut().capture(&p, v, e);
            if attempt && mode == "cancel" {
                seen.set(true);
                ops.cancellation.cancel();
            }
        };
        let result = prepared.admit_with_diagnostics(&ops, None, None, Some(&observer));
        assert!(matches!(
            result,
            Err(CheckError::Deadline { .. } | CheckError::Cancelled)
        ));
        if mode == "cancel" {
            assert!(seen.get());
        }
        drop(dump);
        let r = records(&file);
        assert!(
            r.iter()
                .any(|r| r["record"] == "graph-begin" && r["state"] == "interrupted")
        );
        assert!(
            r.iter()
                .any(|r| r["record"] == "graph-end" && r["complete"] == true)
        );
        assert!(r.iter().any(|r| r["record"] == "rule"));
        if mode == "cancel" {
            assert!(r.iter().any(|r| r["record"] == "attempt-data-end"));
        }
    }
}

#[test]
fn component_dump_small_guarded_hub_has_signed_guards_and_pruning() {
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/bench-den-zoo.mjs");
    let generated=std::process::Command::new("node").args(["--input-type=module","-e","import {pathToFileURL} from 'node:url'; const {source}=await import(pathToFileURL(process.argv[1])); process.stdout.write(source('guarded-hub',4,{hubWriters:2,hubReaders:2,hubValues:1}));"]).arg(script).output().unwrap();
    assert!(generated.status.success());
    let f = Fixture::new(std::str::from_utf8(&generated.stdout).unwrap());
    let file = f.0.join("hub.jsonl");
    let expected = f.run(&["--json", "--no-progress"]);
    assert_eq!(
        expected,
        f.run(&[
            "--json",
            "--no-progress",
            "--dump-component",
            file.to_str().unwrap()
        ])
    );
    let r = records(&file);
    assert!(!r.iter().any(|r| r["record"] == "truncated"));
    assert!(
        r.iter()
            .any(|r| r["record"] == "dead-producer" && r["reason"]["kind"] == "positive-premise")
    );
    assert!(
        r.iter()
            .any(|r| r["record"] == "attempt" && r["impliedGuard"].is_object())
    );
    let rules = r.iter().filter_map(|r| r.get("producer"));
    assert!(
        rules
            .filter_map(|r| r["settledPremises"].as_array())
            .flatten()
            .any(|p| p["polarity"] == "negative")
    );
    assert!(
        r.iter()
            .any(|r| r["record"] == "graph-end" && r["complete"] == true)
    );
}

#[test]
fn component_dump_write_failure_and_exhausted_recording_do_not_change_results() {
    struct Broken;
    impl std::io::Write for Broken {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("simulated full disk"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let p = loaded(CHAIN);
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let verification = p.corpus.verifications().next().unwrap();
    let mut results = Vec::new();
    for mode in ["off", "broken", "exhausted"] {
        let trace = Trace::new(Vec::new(), false);
        let dump = RefCell::new(if mode == "broken" {
            Dump::new(Broken, 100_000, &trace)
        } else {
            Dump::new(Vec::new(), 0, &trace)
        });
        let RequestPreparation::Complete(raw) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let observer =
            |event: AdmissionDump<'_>| dump.borrow_mut().capture(&p, verification, event);
        let prepared = raw
            .admit_with_diagnostics(&ops, None, None, (mode != "off").then_some(&observer))
            .unwrap();
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!()
        };
        results.push(report.results.value.clone());
    }
    assert_eq!(results[0], results[1]);
    assert_eq!(results[0], results[2]);
}

#[test]
fn component_dump_preserves_helper_and_constant_spelling() {
    let f = Fixture::new(
        "namespace 'space name' { sort S; const 'F2', -7:S; input flag(); relation $helper(); relation other(s:S); $helper():-flag(),!other('F2'),!other(-7);other('F2'):-!$helper();other(-7):-!$helper();verification v{assumptions:[];obligations:[];} }",
    );
    let path = f.0.join("names.jsonl");
    let checked = f.run(&["--no-progress", "--dump-component", path.to_str().unwrap()]);
    let r = records(&path);
    assert!(
        r.iter().any(|r| r["record"] == "graph-begin"),
        "{checked:?}"
    );
    let names = r
        .iter()
        .filter(|r| r["record"] == "atom")
        .map(|r| r["atom"]["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert!(names.contains(&"'space name'::$helper()"), "{names:?}");
    assert!(
        names.contains(&"'space name'::other('space name'::'F2')"),
        "{names:?}"
    );
    assert!(
        names.contains(&"'space name'::other('space name'::-7)"),
        "{names:?}"
    );
}
