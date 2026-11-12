use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load, presentation};
use serde_json::{Value, json};
use std::cell::RefCell;

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
