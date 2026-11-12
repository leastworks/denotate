use crate::Session;
use denotate_check::*;
use denotate_ir_text::{ProgramMembership, SourceFile, load, presentation};
use serde_json::json;

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
                            .any(|r| r.label == "supporting rewrite proof")
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
