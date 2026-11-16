use crate::Session;
use denotate_check::*;
use denotate_ir_text::{ProgramMembership, SourceFile, load, presentation};
use serde_json::json;

#[test]
fn pruned_transitive_sources_remain_local_query_dependencies_after_edits() {
    let base = include_str!("../../../ir-text/tests/fixtures/guarded-chain.den")
        .replace("obligations: [no_bad]", "obligations: [no_bad, unique]")
        + "\nsort Mark; const left,right: Mark; relation selected(mark: Mark);\nselected(left):-hazard_claim(); selected(right):-hazard_claim();\nobligation unique:at_most_one(selected,group_by:());";
    let edited = base.replace(
        "hc_type_ok() :- declared(hazardous);",
        "hc_type_ok() :- declared(hazardous), priority_call();",
    );
    let limits = Limits::default();
    let ops = (&limits).into();
    let mut warm = Session::default();
    let mut previous = None;
    for (version, text) in [&base, &edited, &base].into_iter().enumerate() {
        let file = SourceFile::new("file:///chain.den", version as u64, text.clone());
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let run = |mut session: Option<&mut Session>| {
            let raw = match session.as_deref_mut() {
                Some(s) => s.prepare(&request, &p.corpus, &p.keys, &ops).unwrap(),
                None => request.prepare(&p.corpus, &p.keys, &ops).unwrap(),
            };
            let RequestPreparation::Complete(raw) = raw else {
                panic!()
            };
            let prepared = raw.admit(&ops).unwrap();
            assert!(prepared.program().is_admitted());
            assert!(
                prepared
                    .program()
                    .rewrite_proofs()
                    .filter_map(|p| p.guarded_settlement())
                    .any(|p| p
                        .certificate
                        .bounds()
                        .any(|b| !b.cone.pruning.sources.is_empty()))
            );
            let report = match session.as_deref_mut() {
                Some(s) => s.verify(&prepared, &ops).unwrap(),
                None => prepared.verify_local(&ops).unwrap(),
            };
            let LocalCheckOutcome::Complete(report) = report else {
                panic!()
            };
            let inputs: Vec<_> = report.queries.values().map(|q| q.input.clone()).collect();
            assert!(!inputs.is_empty());
            assert!(inputs.iter().any(|q| {
                q.rewrites
                    .iter()
                    .any(|r| matches!(r.kind, KeyedRewriteKind::GuardedSettlement(_)))
            }));
            let shown = presentation::present_with_rewrite_detail(
                &p,
                &report.checked,
                presentation::RewriteDetail::Full,
            )
            .unwrap();
            let details: Vec<_> = shown.diagnostics.iter().map(|d| json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap()})).collect();
            (report.checked.results.value, inputs, details)
        };
        let fresh = run(None);
        if let Some(previous) = previous {
            assert_ne!(
                fresh.1, previous,
                "transitive support edit changes query input"
            );
        }
        assert_eq!(fresh, run(Some(&mut Session::default())));
        assert_eq!(fresh, run(Some(&mut warm)));
        assert_eq!(fresh, run(Some(&mut warm)));
        previous = Some(fresh.1);
    }
}

#[test]
fn guarded_proof_owns_its_snapshot_after_later_commits_and_local_queries() {
    let base = "input kind(); input ready(); input priority();
relation booked(); relation fails(); relation claim(); relation inspected(); relation held(); relation cleared();
booked():-kind(),cleared(); fails():-ready(),!booked(); claim():-!kind(),!fails();
inspected():-kind(); inspected():-claim(); held():-priority(),inspected(); cleared():-ready(),!held();
relation a(); relation b(); a():-!b(); b():-!a();
relation out(); out():-claim(); out():-!kind(),!ready(),a();
sort Mark; const left,right: Mark; relation selected(mark: Mark);
selected(left):-claim(); selected(right):-claim();
obligation unique:at_most_one(selected,group_by:());
verification checks{assumptions:[];obligations:[unique];}";
    let limits = Limits::default();
    let ops = (&limits).into();
    let mut warm = Session::default();
    for (version, text) in [
        base.to_owned(),
        base.replace("fails():-ready()", "fails():-priority()")
            .replace("!ready(),a()", "!priority(),a()"),
        base.to_owned(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = SourceFile::new(
            format!("file:///v{version}/proof.den"),
            version as u64,
            text,
        );
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let run = |mut session: Option<&mut Session>| {
            let prepared = match session.as_deref_mut() {
                Some(session) => session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap(),
                None => request.prepare(&p.corpus, &p.keys, &ops).unwrap(),
            };
            let RequestPreparation::Complete(prepared) = prepared else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let first = prepared
                .program()
                .rewrite_proofs()
                .find(|p| p.guarded_settlement().is_some())
                .unwrap();
            assert!(
                prepared
                    .program()
                    .rewrite_proofs()
                    .any(|p| p.snapshot > first.snapshot),
                "version {version}: {:?}",
                prepared
                    .program()
                    .rewrite_proofs()
                    .map(|p| (p.snapshot, &p.kind, p.candidate().source))
                    .collect::<Vec<_>>()
            );
            let proof = first.guarded_settlement().unwrap();
            assert!(
                proof
                    .certificate
                    .bounds()
                    .next()
                    .unwrap()
                    .cone
                    .producers
                    .iter()
                    .any(|p| !p.live && !p.condition.is_false())
            );
            assert!(!proof.proof.candidate.rule.body.is_empty());
            let current = prepared
                .program()
                .rules()
                .find(|r| r.id == proof.proof.candidate.rule.id)
                .unwrap();
            assert_ne!(current.body, proof.proof.candidate.rule.body);
            // The round, its summaries and temporary cone cache are already gone.
            // Both local input projection and full evidence read owned snapshots.
            let report = match session.as_deref_mut() {
                Some(session) => session.verify(&prepared, &ops).unwrap(),
                None => prepared.verify_local(&ops).unwrap(),
            };
            let LocalCheckOutcome::Complete(report) = report else {
                panic!()
            };
            let inputs: Vec<_> = report.queries.values().map(|q| q.input.clone()).collect();
            assert!(inputs.iter().any(|i| {
                i.rewrites
                    .iter()
                    .any(|r| matches!(r.kind, KeyedRewriteKind::GuardedSettlement(_)))
            }));
            let shown = presentation::present_with_rewrite_detail(
                &p,
                &report.checked,
                presentation::RewriteDetail::Full,
            )
            .unwrap();
            assert!(
                shown
                    .diagnostics
                    .iter()
                    .any(|d| d.notes.iter().any(|n| n.starts_with("Settlement step")))
            );
            let diagnostics: Vec<_> = shown.diagnostics.iter().map(|d| json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap()})).collect();
            (report.checked.results.value, inputs, diagnostics)
        };
        let fresh = run(None);
        assert_eq!(fresh, run(Some(&mut Session::default())));
        assert_eq!(fresh, run(Some(&mut warm)));
        assert_eq!(fresh, run(Some(&mut warm)));
    }
}

#[test]
fn guard_live_ring_agrees_fresh_cold_warm_and_after_edits_at_tight_limits() {
    let mut base = String::from("input kind(); relation bad();\n");
    for i in 0..8 {
        base += &format!(
            "input priority{i}(); input ready{i}();
relation booked{i}(); relation fails{i}(); relation claim{i}();
relation inspected{i}(); relation held{i}(); relation cleared{i}();
booked{i}():-kind(),ready{i}(),priority{i}(),cleared{i}();
booked{i}():-kind(),!ready{i}(),booked{}();
fails{i}():-ready{i}(),!booked{i}(); claim{i}():-!kind(),!fails{i}();
inspected{i}():-kind(); inspected{i}():-claim{i}();
held{i}():-priority{i}(),inspected{i}(); cleared{i}():-ready{i}(),!held{i}();\n",
            (i + 1) % 8
        );
    }
    base += "obligation clean:empty(bad);
verification first{assumptions:[];obligations:[clean];}
verification second{assumptions:[];obligations:[clean];}";
    let limits = Limits {
        max_bdd_nodes: 128,
        ..Limits::default()
    };
    let edited = base.replace("fails0():-ready0()", "fails0():-priority0()");
    guarded_edits_agree(base, edited, limits);
}

#[test]
fn guarded_component_chain_agrees_fresh_cold_warm_and_after_upstream_edits() {
    let mut base = String::from("relation bad();\n");
    for prefix in ["up", "mid"] {
        base += &format!(
            "input {prefix}_kind(); input {prefix}_ready(); input {prefix}_priority();
relation {prefix}_booked(); relation {prefix}_fails(); relation {prefix}_claim();
relation {prefix}_inspected(); relation {prefix}_held(); relation {prefix}_cleared();
{prefix}_booked():-{prefix}_kind(),{prefix}_cleared();
{prefix}_fails():-{prefix}_ready(),!{prefix}_booked();
{prefix}_claim():-!{prefix}_kind(),!{prefix}_fails();
{prefix}_inspected():-{prefix}_kind(); {prefix}_inspected():-{prefix}_claim();
{prefix}_held():-{prefix}_priority(),{prefix}_inspected();
{prefix}_cleared():-{prefix}_ready(),!{prefix}_held();\n"
        );
    }
    base += "mid_booked():-mid_kind(),up_claim();
obligation clean:empty(bad);
verification first{assumptions:[];obligations:[clean];}
verification second{assumptions:[];obligations:[clean];}";
    let edited = base.replace("up_fails():-up_ready()", "up_fails():-up_priority()");
    guarded_edits_agree(base, edited, Limits::default());
}

fn guarded_edits_agree(base: String, edited: String, limits: Limits) {
    let ops = (&limits).into();
    let mut warm = Session::default();
    for (version, text) in [base.clone(), format!("// moved\n{base}"), edited, base]
        .into_iter()
        .enumerate()
    {
        let file = SourceFile::new(format!("file:///v{version}/ring.den"), version as u64, text);
        let p = load(
            &ProgramMembership::single("root", [file.uri.clone()]),
            &[file],
        )
        .unwrap();
        let run = |mut session: Option<&mut Session>| {
            let fixed = session.as_deref_mut().map(|s| {
                s.prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                    .unwrap()
            });
            let mut results = Vec::new();
            for (_, request) in p.verification_requests(&limits).unwrap() {
                let prepared = match &fixed {
                    Some(fixed) => session
                        .as_deref_mut()
                        .unwrap()
                        .prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, fixed)
                        .unwrap(),
                    None => request.prepare(&p.corpus, &p.keys, &ops).unwrap(),
                };
                let RequestPreparation::Complete(prepared) = prepared else {
                    panic!()
                };
                let prepared = prepared.admit(&ops).unwrap();
                assert!(prepared.program().is_admitted());
                assert!(
                    prepared
                        .program()
                        .rewrite_proofs()
                        .any(|p| p.guarded_settlement().is_some())
                );
                let report = match session.as_deref_mut() {
                    Some(s) => s.verify(&prepared, &ops).unwrap(),
                    None => prepared.verify_local(&ops).unwrap(),
                };
                let LocalCheckOutcome::Complete(report) = report else {
                    panic!()
                };
                let shown = presentation::present(&p, &report.checked).unwrap();
                let diagnostics: Vec<_> = shown.diagnostics.iter().map(|d| json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"primary":p.sources.text(d.primary).unwrap(),"related":d.related.iter().map(|r|json!({"source":p.sources.text(r.span).unwrap(),"label":r.label})).collect::<Vec<_>>()})).collect();
                results.push((report.checked.results.value, shown.status, diagnostics));
            }
            results
        };
        let fresh = run(None);
        assert_eq!(fresh, run(Some(&mut Session::default())));
        assert_eq!(fresh, run(Some(&mut warm)));
        assert_eq!(fresh, run(Some(&mut warm)));
    }
}
