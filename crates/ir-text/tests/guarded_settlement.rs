use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use std::collections::BTreeSet;

const HUB: &str = include_str!("fixtures/implied-guard.den");

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
    let sparse = HUB.replace(
        "hc_unsat() :- !hc_type_ok();",
        "relation never(); hc_unsat() :- !hc_type_ok(), !never();",
    );
    let sparse_replacement = HUB.replace(
        "claim_fails() :- docked(), !tagged();",
        "relation never(); claim_fails() :- docked(), !tagged(), !never();",
    );
    for text in [MAIN, BOOLEAN, PRODUCERS, HUB, &sparse, &sparse_replacement] {
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
        if text == HUB {
            let reader = p
                .corpus
                .relations()
                .find(|r| r.name == "hazard_claim")
                .unwrap()
                .id;
            let proofs = ground
                .rewrite_proofs()
                .filter_map(|p| p.guarded_settlement())
                .collect::<Vec<_>>();
            assert_eq!(proofs.len(), 1);
            assert_eq!(proofs[0].proof.candidate.rule.head.atom.relation, reader);
            assert!(proofs[0].implied_guard.is_some());
            // Neither declared class is present. Dropping I while retaining only
            // !docked would invent a claim here.
            assert_eq!(
                ground
                    .evaluate([], &limits)
                    .unwrap()
                    .fact(&GroundAtom::new(reader, []))
                    .unwrap(),
                FactState::Settled(false)
            );
        }
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
        if text == HUB {
            let direct = shown
                .diagnostics
                .iter()
                .find(|d| d.kind == denotate_presentation::Kind::GuardedSettlement)
                .unwrap();
            assert!(
                direct
                    .notes
                    .iter()
                    .any(|n| n.contains("Implied guard retained"))
            );
            assert!(
                !direct
                    .notes
                    .iter()
                    .any(|n| n.starts_with("Implied-guard producer"))
            );
            let full = presentation::present_with_rewrite_detail(
                &p,
                &report,
                denotate_presentation::RewriteDetail::Full,
            )
            .unwrap();
            let full = full
                .diagnostics
                .iter()
                .find(|d| d.kind == denotate_presentation::Kind::GuardedSettlement)
                .unwrap();
            assert!(
                full.notes
                    .iter()
                    .any(|n| n.starts_with("Implied-guard producer") && n.contains("hc_type_ok"))
            );
            assert_eq!(
                direct.data(&p.keys).unwrap()["finding"],
                full.data(&p.keys).unwrap()["finding"]
            );
        }
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

#[test]
fn implied_guard_support_edits_strengthen_and_weaken_with_reader_unchanged() {
    let text = HUB
        .replace("input docked();", "input extra(); input docked();")
        .replace(
            "obligations: [no_bad]",
            "obligations: [no_bad, unique_extra, unique_classless]",
        )
        + r#"
sort Output; const left, right: Output;
relation extra_claim(output: Output);
extra_claim(left) :- hazard_claim(), extra();
extra_claim(right) :- hazard_claim(), extra();
relation classless_claim(output: Output);
classless_claim(left) :- hazard_claim(), !declared(hazardous);
classless_claim(right) :- hazard_claim(), !declared(hazardous);
obligation unique_extra: at_most_one(extra_claim, group_by: ());
obligation unique_classless: at_most_one(classless_claim, group_by: ());
"#;
    let strengthened = text.replace(
        "hc_type_ok() :- declared(hazardous);",
        "hc_type_ok() :- declared(hazardous), !extra();",
    );
    let weakened = text.replace(
        "hc_unsat() :- !hc_type_ok();",
        "hc_unsat() :- !hc_type_ok(), extra();",
    );
    let mut warm = Session::default();
    let mut previous = None;
    for (revision, text) in [text.clone(), strengthened, text.clone(), weakened, text]
        .iter()
        .enumerate()
    {
        let p = loaded(text, revision as u64);
        let fresh = check(&p, None);
        assert_eq!(fresh, check(&p, Some(&mut Session::default())));
        assert_eq!(fresh, check(&p, Some(&mut warm)));
        assert_eq!(fresh, check(&p, Some(&mut warm)));
        // Exercise keyed local query reuse with actual verdict changes, not only
        // different warning notes or a notice that stays varying throughout.
        let failures = fresh
            .0
            .groups
            .values()
            .filter(|r| matches!(r, ScopedResult::Counterexample(..)))
            .count();
        assert_eq!(failures, [1, 0, 1, 0, 1][revision]);
        if revision == 3 {
            // Removing the class guarantee lets the cyclic producer coexist
            // with its reader again. Fresh and warm must both retract admission.
            assert!(
                fresh
                    .0
                    .groups
                    .values()
                    .all(|r| matches!(r, ScopedResult::Unsupported(_)))
            );
        }
        let diagnostics = fresh.1["diagnostics"].as_array().unwrap();
        if revision < 3 {
            let d = diagnostics
                .iter()
                .find(|d| {
                    d["notes"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|n| n.as_str().unwrap().contains("Implied guard retained"))
                })
                .unwrap();
            let identity = d["data"]["finding"].clone();
            if let Some(old) = previous.replace(identity.clone()) {
                assert_eq!(old, identity);
            }
        }
    }
}

#[test]
fn implied_guard_positive_reader_owns_support_and_preserves_models() {
    use test_support::rewrites::{compare_permitted, subsets, supported_models};
    let text=HUB.replace("relation hazard_claim();", "relation hazard_claim(); relation hc_read_ok(); hazard_claim() :- hc_read_ok();")
        .replace("relation hc_type_ok(); relation hc_read_ok(); relation hc_unsat();", "")
        .replace("hc_type_ok() :- declared(hazardous); hc_read_ok() :- !claim_fails();", "hc_read_ok() :- declared(hazardous), !claim_fails();")
        .replace("hc_unsat() :- !hc_type_ok(); hc_unsat() :- !hc_read_ok(); hazard_claim() :- !hc_unsat();", "");
    let p = loaded(&text, 0);
    let l = Limits::default();
    let ops = (&l).into();
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let g = prepared.program();
    assert!(g.is_admitted());
    let implied = g
        .rewrite_proofs()
        .filter_map(|p| p.guarded_settlement())
        .find_map(|p| p.implied_guard.as_ref())
        .unwrap();
    assert!(
        implied
            .premises
            .iter()
            .any(|p| p.literal.polarity == Polarity::Positive && !p.producers.is_empty())
    );
    let declared = p
        .corpus
        .relations()
        .find(|r| r.name == "declared")
        .unwrap()
        .id;
    let permitted =
        |world: &BTreeSet<GroundAtom>| world.iter().filter(|a| a.relation == declared).count() <= 1;
    compare_permitted(&p.corpus, &p.domains, g, permitted);
    for world in subsets(&g.input_atoms().cloned().collect::<Vec<_>>())
        .into_iter()
        .filter(permitted)
    {
        assert_eq!(
            supported_models(g, &g.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(g, &g.rules().cloned().collect::<Vec<_>>(), &world)
        );
    }
    let fresh = check(&p, None);
    let mut warm = Session::default();
    assert_eq!(fresh, check(&p, Some(&mut warm)));
    assert_eq!(fresh, check(&p, Some(&mut warm)));
}

#[test]
fn implied_guard_owns_producers_outside_the_replaced_premise_cone() {
    let text = HUB.replace(
        "hazard_claim() :- !hc_unsat();",
        "hazard_claim() :- !hc_unsat(), !other();",
    ) + "\ninput extra(); relation other(); relation other_b(); other() :- extra(); other() :- !other_b(); other_b() :- !other();\n";
    let p = loaded(&text, 0);
    let l = Limits::default();
    let ops = (&l).into();
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let proof = prepared
        .program()
        .rewrite_proofs()
        .filter_map(|p| p.guarded_settlement())
        .find(|p| p.implied_guard.is_some())
        .unwrap();
    let other = p.corpus.relations().find(|r| r.name == "other").unwrap().id;
    let source = proof
        .implied_guard
        .as_ref()
        .unwrap()
        .premises
        .iter()
        .find(|p| p.literal.term.atom.relation == other)
        .unwrap()
        .producers
        .first()
        .unwrap();
    assert!(
        !proof
            .bounds
            .cone
            .producers
            .iter()
            .any(|p| p.rule.id == source.rule.id)
    );
    let source_key = prepared.key_view().instance(source.rule.id).unwrap();
    assert!(
        prepared
            .key_view()
            .rewrites()
            .unwrap()
            .values()
            .any(|p| p.producers.contains(&source_key))
    );
    let mut warm = Session::default();
    for (revision, text) in [
        text.clone(),
        text.replace("other() :- extra();", "other() :- !extra();"),
        text,
    ]
    .iter()
    .enumerate()
    {
        let p = loaded(text, revision as u64);
        let fresh = check(&p, None);
        assert_eq!(fresh, check(&p, Some(&mut warm)));
        assert_eq!(fresh, check(&p, Some(&mut warm)));
    }
}
