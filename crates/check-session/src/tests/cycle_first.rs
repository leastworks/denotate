use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load, presentation};

fn source(unsupported: bool) -> String {
    let mut text = String::from(
        "sort V; const first, second: V; input value(v: V); input flag();\nrelation a(); relation b(); a() :- flag(), !b(); b() :- !flag(), !a();\nassumption exclusive: at_most_one(value, group_by: ());\nverification checks { assumptions: [exclusive]; obligations: []; }\n",
    );
    if unsupported {
        text.push_str("relation u(); relation v(); u() :- !v(); v() :- !u();\n");
    }
    for n in 0..80 {
        text.push_str(&format!(
            "relation guard{n}(); guard{n}() :- value(first), !value(second);\n"
        ));
    }
    text
}
fn load_source(text: String, revision: u64) -> LoadedProgram {
    let file = SourceFile::new("file:///cycle-first.den", revision, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}
fn check(
    p: &LoadedProgram,
    session: &mut Session,
    limits: &Limits,
) -> Option<(bool, ScopedResults, serde_json::Value)> {
    let ops = limits.into();
    let request = p.verification_requests(limits).unwrap().pop().unwrap().1;
    let fixed = session
        .prepare_fixed(&p.corpus, &p.keys, &p.domains, limits)
        .unwrap();
    let RequestPreparation::Complete(prepared) = session
        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        return None;
    };
    let prepared = prepared.admit(&ops).unwrap();
    if prepared.program().downstream_incomplete().is_none() {
        return None;
    }
    assert!(prepared.program().admission_limit().is_none());
    let admitted = prepared.program().is_admitted();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        return None;
    };
    let presented = presentation::present(p, &report.checked).unwrap();
    assert!(presented.status["downstreamIncomplete"].is_object());
    assert!(
        presented
            .diagnostics
            .iter()
            .any(|d| d.kind.code() == "incomplete-downstream-work")
    );
    assert!(
        report
            .checked
            .results
            .value
            .regions
            .values()
            .all(|r| matches!(r.outcome, ScopedResult::Unsupported(_)))
    );
    let value = report.checked.results.value;
    // Shared admission within a checking run reuses the same graph AND marker.
    let RequestPreparation::Complete(again) = session
        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!("same attachment");
    };
    let reused = std::cell::Cell::new(false);
    let again = again
        .admit_with_progress(
            &ops,
            Some(&|e| {
                if e.stage == "reused" {
                    reused.set(true);
                }
            }),
        )
        .unwrap();
    assert!(reused.get());
    assert_eq!(
        again.program().downstream_incomplete(),
        prepared.program().downstream_incomplete()
    );
    let LocalCheckOutcome::Complete(report) = session.verify(&again, &ops).unwrap() else {
        panic!("same outcome");
    };
    assert_eq!(value, report.checked.results.value);
    Some((admitted, value, presented.status))
}
#[test]
fn cycle_first_incomplete_downstream_work_survives_reuse_and_warm_edits() {
    for unsupported in [false, true] {
        let p = load_source(source(unsupported), 0);
        let mut selected = None;
        for max_work in (2_000..50_000).step_by(1_000) {
            let limits = Limits {
                max_work,
                ..Limits::default()
            };
            if let Some(result) = check(&p, &mut Session::default(), &limits) {
                assert_eq!(result.0, !unsupported);
                selected = Some(limits);
                break;
            }
        }
        let limits = selected.expect("exercise phase B exhaustion after preparation succeeds");
        let mut warm = Session::default();
        for (revision, text) in [
            source(unsupported),
            format!("// shifted origins\n{}", source(unsupported)),
            source(unsupported),
        ]
        .into_iter()
        .enumerate()
        {
            let p = load_source(text, revision as u64);
            let cold = check(&p, &mut Session::default(), &limits).unwrap();
            assert_eq!(cold, check(&p, &mut warm, &limits).unwrap());
            assert_eq!(cold, check(&p, &mut warm, &limits).unwrap());
            // Fresh preparation is also equivalent to the session path.
            let ops = (&limits).into();
            let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
            let RequestPreparation::Complete(prepared) =
                request.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!();
            };
            let prepared = prepared.admit(&ops).unwrap();
            let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
                panic!();
            };
            assert_eq!(cold.1, report.results.value);
            assert_eq!(cold.2, presentation::present(&p, &report).unwrap().status);
        }
    }
}
