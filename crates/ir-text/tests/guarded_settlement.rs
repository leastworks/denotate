use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use std::collections::BTreeSet;

const MAIN: &str = include_str!("fixtures/guarded-settlement.den");
const BOOLEAN: &str = include_str!("fixtures/guarded-settlement-boolean.den");
const PRODUCERS: &str = include_str!("fixtures/guarded-settlement-producers.den");

fn loaded(text: &str, version: u64) -> LoadedProgram {
    let file = SourceFile::new(
        format!("file:///revision-{version}/guard.den"),
        version,
        text,
    );
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

#[test]
fn guarded_settlement_variants_preserve_models_and_notice_results() {
    use test_support::rewrites::{compare_permitted, subsets, supported_models};
    for text in [MAIN, BOOLEAN, PRODUCERS] {
        let p = loaded(text, 0);
        let limits = Limits::default();
        let ops = (&limits).into();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(raw) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        assert!(!raw.program().is_admitted());
        let prepared = raw.admit(&ops).unwrap();
        let ground = prepared.program();
        assert!(ground.is_admitted(), "{:?}", ground.admission_limit());
        assert!(
            ground
                .rewrite_proofs()
                .any(|p| p.guarded_settlement().is_some())
        );
        let declared = p
            .corpus
            .relations()
            .find(|r| r.name == "declared")
            .map(|r| r.id);
        let permitted = |world: &BTreeSet<GroundAtom>| {
            declared.is_none_or(|r| world.iter().filter(|a| a.relation == r).count() <= 1)
        };
        compare_permitted(&p.corpus, &p.domains, ground, permitted);
        for world in subsets(&ground.input_atoms().cloned().collect::<Vec<_>>())
            .into_iter()
            .filter(permitted)
        {
            assert_eq!(
                supported_models(
                    ground,
                    &ground.original_rules().cloned().collect::<Vec<_>>(),
                    &world
                ),
                supported_models(ground, &ground.rules().cloned().collect::<Vec<_>>(), &world)
            );
        }
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!()
        };
        let shown = presentation::present(&p, &report).unwrap();
        assert_eq!(shown.status["state"], "proved");
        assert_eq!(shown.status["notices"][0]["result"]["state"], "varying");
        assert!(
            shown
                .diagnostics
                .iter()
                .any(|d| d.kind == denotate_presentation::Kind::GuardedSettlement)
        );
    }
}

fn check(p: &LoadedProgram, session: Option<&mut Session>) -> (ScopedResults, serde_json::Value) {
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let mut session = session;
    let prepared = if let Some(s) = session.as_deref_mut() {
        let fixed = s
            .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            .unwrap();
        s.prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
            .unwrap()
    } else {
        request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    };
    let RequestPreparation::Complete(prepared) = prepared else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let result = if let Some(s) = session {
        s.verify(&prepared, &ops).unwrap()
    } else {
        prepared.verify_local(&ops).unwrap()
    };
    let LocalCheckOutcome::Complete(report) = result else {
        panic!()
    };
    let shown = presentation::present(p, &report.checked).unwrap();
    let diagnostics = shown.diagnostics.iter().map(|d| serde_json::json!({"message":d.message,"notes":d.notes,"data":d.data(&p.keys).unwrap(),"range":d.primary.byte_range(),"related":d.related.iter().map(|r|serde_json::json!({"range":r.span.byte_range(),"label":r.label})).collect::<Vec<_>>()})).collect::<Vec<_>>();
    (
        report.checked.results.value,
        serde_json::json!({"status":shown.status,"diagnostics":diagnostics}),
    )
}

#[test]
fn guarded_settlement_replays_counterexamples_and_agrees_fresh_cold_warm_after_edits() {
    let text = MAIN
        .replace(
            "notice cleared_varies",
            "obligation no_bookings: empty(reefer_booked);\nnotice cleared_varies",
        )
        .replace("obligations: []", "obligations: [no_bookings]");
    let mut warm = Session::default();
    for (revision, text) in [
        text.clone(),
        format!("// shifted\n{text}"),
        text.replace(
            "declared(perishable), cleared()",
            "declared(hazardous), cleared()",
        ),
        text.clone(),
    ]
    .iter()
    .enumerate()
    {
        let p = loaded(text, revision as u64);
        let fresh = check(&p, None);
        assert_eq!(fresh, check(&p, Some(&mut Session::default())));
        assert_eq!(fresh, check(&p, Some(&mut warm)));
        assert_eq!(fresh, check(&p, Some(&mut warm)));
        if revision != 2 {
            assert_eq!(fresh.1["status"]["state"], "findings");
            assert!(
                fresh.1["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|d| d["data"]["evidence"]["kind"] == "replayed-counterexample")
            );
        }
    }
}

#[test]
fn guarded_settlement_local_uniqueness_and_coverage_reconstruct_executable_conditions() {
    let text = MAIN.replace("notice cleared_varies", "sort Slot; const a, b: Slot; relation output(slot: Slot); output(a) :- reefer_booked(); output(b) :- reefer_booked(); obligation unique_output: at_most_one(output, group_by: ()); obligation covered: at_least_one(output, group_by: ());\nnotice cleared_varies").replace("obligations: []", "obligations: [unique_output, covered]");
    let mut session = Session::default();
    for revision in 0..3 {
        let p = loaded(&text, revision);
        let fresh = check(&p, None);
        assert_eq!(fresh, check(&p, Some(&mut Session::default())));
        assert_eq!(fresh, check(&p, Some(&mut session)));
        assert_eq!(fresh, check(&p, Some(&mut session)));
        assert_eq!(fresh.1["status"]["state"], "findings");
        let diagnostics = fresh.1["diagnostics"].as_array().unwrap();
        assert!(
            diagnostics
                .iter()
                .any(|d| d["data"]["evidence"]["kind"] == "replayed-counterexample"),
            "{}",
            fresh.1
        );
    }
}

#[test]
fn guarded_settlement_leaves_live_and_external_unresolved_cycles_unsupported() {
    for text in [
        MAIN.replace("assumptions: [one_class]", "assumptions: []"),
        BOOLEAN.replace("input docked();", "relation external_a(); relation external_b(); external_a() :- !external_b(); external_b() :- !external_a(); relation docked(); docked() :- external_a();"),
    ] {
        let p = loaded(&text, 0);
        let limits = Limits::default();
        let ops = (&limits).into();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(raw) = request.prepare(&p.corpus, &p.keys, &ops).unwrap() else { panic!() };
        let admitted = raw.admit(&ops).unwrap();
        assert!(!admitted.program().is_admitted());
        test_support::rewrites::compare(&p.corpus, &p.domains, admitted.program());
    }
}

#[test]
fn guarded_settlement_remains_executable_in_a_local_completion_cone() {
    let text = format!(
        "{BOOLEAN}\nrelation impossible(); impossible() :- reefer_booked(), !impossible();\n"
    );
    let p = loaded(&text, 0);
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    assert!(!prepared.program().is_admitted());
    assert!(
        prepared
            .program()
            .rewrite_proofs()
            .any(|p| p.guarded_settlement().is_some())
    );
    let CheckOutcome::Complete(global) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    assert!(
        global
            .results
            .value
            .regions
            .values()
            .any(|r| matches!(r.completion, RegionCompletion::NoMeaning { .. }))
    );
    let fresh = check(&p, None);
    assert_eq!(global.results.value, fresh.0);
    let mut session = Session::default();
    assert_eq!(fresh, check(&p, Some(&mut session)));
    assert_eq!(fresh, check(&p, Some(&mut session)));
}
