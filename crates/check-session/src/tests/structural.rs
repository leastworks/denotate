use crate::Session;
use denotate_check::*;
use denotate_ir_text::{ProgramMembership, SourceFile, load, presentation};
use serde_json::json;

#[test]
fn transitive_support_edits_invalidate_warm_queries_without_changing_warning_identity() {
    let base =
        "relation leaf(); relation other(); other(); relation missing(); relation bridge(); relation kept(); relation term();
leaf(); bridge():-leaf(); kept():-bridge(); kept():-term(); term():-!kept();
sort S; const a,b:S; relation result(s:S); result(a); result(b):-term();
obligation unique:at_most_one(result, group_by:()); verification checks{assumptions:[];obligations:[unique];}";
    let mut session = Session::default();
    let mut identity = None;
    for (revision, source) in [
        base.to_owned(),
        base.replace("leaf(); bridge", "leaf():-other(); bridge"),
        base.replace("leaf(); bridge", "leaf():-missing(); bridge"),
        base.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new("file:///program.den", revision as u64, source);
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = (&limits).into();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let run = |s: &mut Session| {
            let fixed = s
                .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                .unwrap();
            let RequestPreparation::Complete(prepared) = s
                .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
                .unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(report) = s.verify(&prepared, &ops).unwrap() else {
                panic!()
            };
            let shown = presentation::present_with_rewrite_detail(
                &p,
                &report.checked,
                presentation::RewriteDetail::Full,
            )
            .unwrap();
            let warning = shown
                .diagnostics
                .iter()
                .find(|d| {
                    d.evidence["kind"] == "rewrite-proof"
                        && p.sources.text(d.primary).unwrap() == "kept():-term();"
                })
                .map(|d| d.data(&p.keys).unwrap()["finding"].clone());
            let diagnostics: Vec<_> = shown.diagnostics.iter().map(|d|json!({"data":d.data(&p.keys).unwrap(),"notes":d.notes,"primary":p.sources.text(d.primary).unwrap(),"related":d.related.iter().map(|r|p.sources.text(r.span).unwrap()).collect::<Vec<_>>()})).collect();
            (
                report.checked.results.value,
                shown.status,
                diagnostics,
                warning,
            )
        };
        let fresh = run(&mut Session::default());
        assert_eq!(run(&mut session), fresh);
        assert_eq!(run(&mut session), fresh);
        if revision == 2 {
            assert!(fresh.3.is_none());
        } else if let Some(previous) = &identity {
            assert_eq!(fresh.3.as_ref(), Some(previous));
        } else {
            identity = fresh.3;
            assert!(identity.is_some());
        }
    }
}

#[test]
fn structural_rewrites_agree_fresh_cold_warm_and_locate_current_sources() {
    let base = "input i(); relation field(); relation outer(); relation inner(); relation term(); relation constraint(); relation kept();
field():-outer(); field():-inner(); outer():-i(); inner():-outer(),term();
term():-!constraint(); constraint():-!kept(); kept():-!field();
relation bad(); obligation clean:empty(bad);
verification first{assumptions:[];obligations:[clean];}
verification second{assumptions:[];obligations:[clean];}";
    let mut warm = Session::default();
    for (version, text) in [
        base.to_owned(),
        format!("// moved\n\n{base}"),
        base.replace("inner():-outer(),term()", "inner():-term()"),
        base.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new(
            format!("file:///revision-{version}/program.den"),
            version as u64,
            text,
        );
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let limits = Limits::default();
        let ops = (&limits).into();
        let run = |mut session: Option<&mut Session>| {
            let fixed = session.as_deref_mut().map(|s| {
                s.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                    .unwrap()
            });
            let mut output = Vec::new();
            for (_, request) in p.verification_requests(&limits).unwrap() {
                let prepared = if let Some(f) = &fixed {
                    session
                        .as_deref_mut()
                        .unwrap()
                        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, f)
                        .unwrap()
                } else {
                    request.prepare(&p.corpus, &p.keys, &ops).unwrap()
                };
                let RequestPreparation::Complete(prepared) = prepared else {
                    panic!()
                };
                let prepared = prepared.admit(&ops).unwrap();
                let checked = if let Some(s) = session.as_deref_mut() {
                    s.verify(&prepared, &ops).unwrap()
                } else {
                    prepared.verify_local(&ops).unwrap()
                };
                let LocalCheckOutcome::Complete(report) = checked else {
                    panic!()
                };
                let shown = presentation::present(&p, &report.checked).unwrap();
                if version != 2 {
                    assert!(prepared.program().is_admitted());
                    let warning = shown
                        .diagnostics
                        .iter()
                        .find(|d| {
                            d.notes
                                .iter()
                                .any(|n| n.contains("unfolding single-producer"))
                        })
                        .unwrap();
                    assert!(
                        warning
                            .related
                            .iter()
                            .any(|r| r.label == "direct rewrite justification")
                    );
                    assert_eq!(
                        p.sources.text(warning.primary).unwrap(),
                        "field():-inner();"
                    );
                }
                let diagnostics:Vec<_>=shown.diagnostics.iter().map(|d|json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"primary":d.primary.byte_range(),"related":d.related.iter().map(|r|json!({"range":r.span.byte_range(),"label":r.label})).collect::<Vec<_>>()})).collect();
                output.push((
                    report.checked.results.value,
                    json!({"status":shown.status,"diagnostics":diagnostics}),
                ));
            }
            output
        };
        let fresh = run(None);
        let cold = run(Some(&mut Session::default()));
        let current = run(Some(&mut warm));
        assert_eq!(fresh, cold);
        assert_eq!(cold, current);
        assert_eq!(current, run(Some(&mut warm)));
    }
}
