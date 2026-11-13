use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load, presentation};
use serde_json::{Value, json};
use std::cell::RefCell;

#[test]
fn completed_negative_attempts_agree_fresh_cold_warm_and_after_edits() {
    let base = "input i(); input j();
relation a(); relation b(); a():-i(); a():-!b(); b():-!a();
relation kept(); relation term(); kept():-j(); kept():-!j(); kept():-term(); term():-i(),!kept();
relation x(); relation y(); x():-j(),!y(); y():-!j(),!x();
relation absent(); obligation no_absent:empty(absent);
verification first{assumptions:[];obligations:[no_absent];}
verification second{assumptions:[];obligations:[no_absent];}";
    let mut warm = Session::default();
    let mut exercised = false;
    for (revision, text) in [
        base.to_owned(),
        format!("// moved\n{base}"),
        base.replace("a():-i()", "a():-j()"),
        base.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new(
            format!("file:///revision-{revision}/negative.den"),
            revision as u64,
            text,
        );
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = (&limits).into();
        let mut run = |mut session: Option<&mut Session>| {
            let fixed = session.as_deref_mut().map(|s| {
                s.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                    .unwrap()
            });
            let mut out = Vec::new();
            for (_, request) in p.verification_requests(&limits).unwrap() {
                let prepared = if let Some(fixed) = &fixed {
                    session
                        .as_deref_mut()
                        .unwrap()
                        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, fixed)
                        .unwrap()
                } else {
                    request.prepare(&p.corpus, &p.keys, &ops).unwrap()
                };
                let RequestPreparation::Complete(prepared) = prepared else {
                    panic!("preparation")
                };
                let events = RefCell::new(Vec::new());
                let prepared = prepared
                    .admit_with_progress(&ops, Some(&|e| events.borrow_mut().push(e.clone())))
                    .unwrap();
                exercised |= events
                    .borrow()
                    .iter()
                    .any(|e| e.attempts.values().any(|a| a.reused_negative > 0));
                assert!(prepared.program().admission_limit().is_none());
                assert_eq!(prepared.program().admission_skips().count(), 0);
                let checked = if let Some(s) = session.as_deref_mut() {
                    s.verify(&prepared, &ops).unwrap()
                } else {
                    prepared.verify_local(&ops).unwrap()
                };
                let LocalCheckOutcome::Complete(report) = checked else {
                    panic!("checking")
                };
                let shown = presentation::present(&p, &report.checked).unwrap();
                let diagnostics: Vec<_> = shown.diagnostics.iter().map(|d| json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"range":d.primary.byte_range(),"related":d.related.iter().map(|r|json!({"range":r.span.byte_range(),"label":r.label})).collect::<Vec<_>>()})).collect();
                out.push((
                    report.checked.results.value,
                    json!({"status":shown.status,"diagnostics":diagnostics}),
                ));
            }
            out
        };
        let fresh = run(None);
        let cold = run(Some(&mut Session::default()));
        let current = run(Some(&mut warm));
        assert_eq!(fresh, cold);
        assert_eq!(cold, current);
        assert_eq!(current, run(Some(&mut warm)));
    }
    assert!(exercised);
}

const SOURCE: &str = "
input p(); input q(); input r(); input s();
relation a(); relation b(); relation d();
a():-p(),q(),!b(),!d(); b():-!p(),!a(); d():-r(),s(),!a();
relation u(); relation v(); u():-!v(); v():-!u();
relation wide(); wide():-p(); wide():-q(); wide():-r(); wide():-s(); wide():-u();
relation absent(); obligation no_absent:empty(absent);
verification first{assumptions:[];obligations:[no_absent];}
verification second{assumptions:[];obligations:[no_absent];}
";

fn run(
    p: &LoadedProgram,
    mut session: Option<&mut Session>,
) -> (Vec<ScopedResults>, Vec<Value>, Vec<WorkReceipts>) {
    let limits = Limits {
        max_bdd_tasks: 2,
        ..Limits::default()
    };
    let ops = (&limits).into();
    let fixed = session.as_deref_mut().map(|s| {
        s.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            .unwrap()
    });
    let mut results = Vec::new();
    let mut displays = Vec::new();
    let mut receipts = Vec::new();
    for (index, (_, request)) in p
        .verification_requests(&limits)
        .unwrap()
        .into_iter()
        .enumerate()
    {
        let prepared = if let Some(fixed) = &fixed {
            session
                .as_deref_mut()
                .unwrap()
                .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, fixed)
                .unwrap()
        } else {
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        };
        let RequestPreparation::Complete(prepared) = prepared else {
            panic!("preparation exhausted")
        };
        let events = RefCell::new(Vec::new());
        let prepared = prepared
            .admit_with_progress(&ops, Some(&|e| events.borrow_mut().push(e.clone())))
            .unwrap();
        assert!(prepared.program().admission_limit().is_none());
        assert!(prepared.program().admission_skips().next().is_some());
        if fixed.is_some() && index == 1 {
            assert_eq!(events.borrow().last().unwrap().stage, "reused");
            assert!(events.borrow().last().unwrap().skipped_attempts > 0);
        }
        let checked = if let Some(s) = session.as_deref_mut() {
            s.verify(&prepared, &ops).unwrap()
        } else {
            prepared.verify_local(&ops).unwrap()
        };
        let LocalCheckOutcome::Complete(report) = checked else {
            panic!("checking exhausted")
        };
        let presented = presentation::present(p, &report.checked).unwrap();
        assert!(
            presented.status["admissionSkips"]
                .as_array()
                .is_some_and(|s| !s.is_empty())
        );
        assert!(
            report
                .checked
                .results
                .value
                .regions
                .values()
                .any(|r| !r.admission_skips.is_empty())
        );
        assert!(
            report
                .checked
                .results
                .value
                .regions
                .values()
                .any(|r| r.admission_skips.is_empty())
        );
        assert!(
            presented
                .diagnostics
                .iter()
                .any(|d| d.notes.iter().any(|n| n.contains("Admission skipped")))
        );
        assert!(presented.diagnostics.iter().any(|d| {
            d.related
                .iter()
                .any(|r| r.label.contains("skipped admission proof attempt"))
        }));
        let diagnostics:Vec<_>=presented.diagnostics.iter().map(|d| {
            let source=p.sources.snapshot(d.primary.snapshot()).unwrap();
            assert!(source.text.get(d.primary.byte_range()).is_some());
            json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"uri":source.uri,"range":d.primary.byte_range()})
        }).collect();
        displays.push(json!({"status":presented.status,"diagnostics":diagnostics}));
        receipts.push(report.checked.results.receipts);
        results.push(report.checked.results.value);
    }
    (results, displays, receipts)
}

#[test]
fn admission_skips_survive_reuse_and_warm_edits_with_current_diagnostics() {
    let mut warm = Session::default();
    for (revision, text) in [
        SOURCE.to_owned(),
        format!("// moved\n\n{SOURCE}"),
        SOURCE.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new(
            format!("file:///revision-{revision}/skips.den"),
            revision as u64,
            text,
        );
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let fresh = run(&p, None);
        let cold = run(&p, Some(&mut Session::default()));
        let current = run(&p, Some(&mut warm));
        assert_eq!((&fresh.0, &fresh.1), (&cold.0, &cold.1));
        assert_eq!(cold, current);
        assert_eq!(current, run(&p, Some(&mut warm)));
    }
}

#[test]
fn precise_retries_agree_fresh_cold_warm_after_dependency_and_source_edits() {
    let base = "input p(); input q(); input r(); input s(); input t(); input extra();
relation a(); relation b(); relation x(); relation y(); relation u(); relation v(); relation wide();
a():-p(),q(),!b(); b():-r(),s(),!x(),!a(); b():-t(),!x(),!a();
x():-p(),!y(); y():-!p(),!x(); u():-!v(); v():-!u();
wide():-!p(); wide():-!q(); wide():-!r(); wide():-!s(); wide():-!t(); wide():-extra(); wide():-a(),u();
relation absent(); obligation no_absent:empty(absent);
verification first{assumptions:[];obligations:[no_absent];}
verification second{assumptions:[];obligations:[no_absent];}";
    let base = format!(
        "sort S; const {}: S; input choice(item:S); wide():-choice(X);\n{base}",
        (0..16)
            .map(|i| format!("c{i}"))
            .collect::<Vec<_>>()
            .join(",")
    );
    let mut warm = Session::default();
    for (revision, text) in [
        base.to_owned(),
        format!("// moved\n{base}"),
        base.replace("wide():-a(),u()", "wide():-u(); wide():-a()"),
        base.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new(
            format!("file:///revision-{revision}/retry.den"),
            revision as u64,
            text,
        );
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let limits = Limits {
            max_bdd_tasks: 8,
            ..Limits::default()
        };
        let ops = (&limits).into();
        let run = |mut session: Option<&mut Session>| {
            let fixed = session.as_deref_mut().map(|s| {
                s.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                    .unwrap()
            });
            let mut out = Vec::new();
            for (_, request) in p.verification_requests(&limits).unwrap() {
                let prepared = if let Some(fixed) = &fixed {
                    session
                        .as_deref_mut()
                        .unwrap()
                        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, fixed)
                        .unwrap()
                } else {
                    request.prepare(&p.corpus, &p.keys, &ops).unwrap()
                };
                let RequestPreparation::Complete(prepared) = prepared else {
                    panic!("preparation")
                };
                let events = RefCell::new(Vec::new());
                let prepared = prepared
                    .admit_with_progress(&ops, Some(&|e| events.borrow_mut().push(e.clone())))
                    .unwrap();
                assert!(prepared.program().admission_limit().is_none());
                if events.borrow().last().unwrap().stage != "reused" && revision != 2 {
                    let failures = events
                        .borrow()
                        .iter()
                        .filter(|e| {
                            e.skipped
                                .as_ref()
                                .is_some_and(|s| s.kind == AdmissionAttemptKind::Coverage)
                        })
                        .count();
                    assert_eq!(
                        failures, 1,
                        "one failed coverage across several graph commits"
                    );
                }
                let checked = if let Some(s) = session.as_deref_mut() {
                    s.verify(&prepared, &ops).unwrap()
                } else {
                    prepared.verify_local(&ops).unwrap()
                };
                let LocalCheckOutcome::Complete(report) = checked else {
                    panic!("checking")
                };
                let shown = presentation::present(&p, &report.checked).unwrap();
                let diagnostics:Vec<_> = shown.diagnostics.iter().map(|d|json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"primary":d.primary.byte_range(),"related":d.related.iter().map(|r|json!({"range":r.span.byte_range(),"label":r.label})).collect::<Vec<_>>()})).collect();
                out.push((
                    report.checked.results.value,
                    json!({"status":shown.status,"diagnostics":diagnostics}),
                ));
            }
            out
        };
        let fresh = run(None);
        let cold = run(Some(&mut Session::default()));
        let current = run(Some(&mut warm));
        assert_eq!(fresh, cold);
        assert_eq!(cold, current);
        assert_eq!(current, run(Some(&mut warm)));
    }
}
