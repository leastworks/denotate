use super::*;
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile};
use driver::{Run, measure};
use outcomes::{Outcomes, Scope};
use serde_json::{Value, json};
use std::{collections::BTreeMap, path::PathBuf, time::Duration};

const ALL: &str = r#"
sort Group; const a, b: Group;
sort Value; const x, y: Value;
relation produced(g: Group, v: Value);
produced(a, x); produced(a, y);
relation singleton(g: Group, v: Value); singleton(a, x);
obligation unique: at_most_one(produced, group_by: (g));
obligation covered: at_least_one(produced, group_by: (g));
obligation exact: exactly_one(produced, group_by: (g));
obligation absent: empty(produced);
obligation trivial: at_most_one(singleton, group_by: (g));
input selected(); input eligible();
relation parent_scope(); parent_scope() :- selected(), eligible();
relation not_selected(); not_selected() :- !selected();
relation unreachable();
notice outer: varies(selected);
notice repeated: varies(selected, within: parent_scope);
notice incompatible: varies(not_selected, within: parent_scope);
notice suppressed: varies(selected, within: unreachable);
verification checks {
 assumptions: []; obligations: [unique, covered, exact, absent, trivial];
 notices: [outer, repeated, incompatible, suppressed];
}
"#;
fn snapshot(text: &str) -> Snapshot {
    Snapshot {
        membership: ProgramMembership::single(
            "file:///score",
            ["file:///score/program.den".into()],
        ),
        sources: vec![SourceFile::new("file:///score/program.den", 1, text)],
    }
}
fn config() -> Config {
    Config::parse(["/score".into(), "--samples".into(), "1".into()]).unwrap()
}
#[test]
fn invalid_unselected_assumptions_are_not_silently_scored_as_unconfigured() {
    let source = snapshot("relation p(); p():-!p(); assumption a:empty(p);");
    let error = driver::collect(&config(), &source, None).unwrap_err();
    assert!(
        error.contains("Assumption validation") && error.contains("invalid-assumption"),
        "{error}"
    );
}
fn run(text: &str, mode: &str) -> Run {
    let p = snapshot(text).load(false).unwrap();
    let c = config();
    let request = p.verification_requests(&c.limits).unwrap().remove(0).1;
    measure(
        &p,
        &request,
        mode,
        &mut scorecard_support::session(mode, false),
        &c.limits,
    )
}
fn obligation<'a>(o: &'a Outcomes, name: &str) -> &'a Value {
    o.keyed
        .iter()
        .find_map(|(k, v)| matches!(k,Scope::Obligation(k) if k.0.name.as_ref()==name).then_some(v))
        .unwrap()
}
fn ordinary(
    p: &LoadedProgram,
    request: &CheckRequest,
    limits: &Limits,
) -> (Accounted<ScopedResults>, Value) {
    let ops = OperationalLimits::from(limits);
    let mut s = Session::default();
    let RequestPreparation::Complete(prepared) =
        s.prepare(request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("preparation")
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = s.verify(&prepared, &ops).unwrap() else {
        panic!("check")
    };
    let status = denotate_ir_text::presentation::present(p, &report.checked)
        .unwrap()
        .status;
    (report.checked.results, status)
}
#[test]
fn all_kinds_count_authored_obligations_and_both_exact_components() {
    for mode in scorecard_support::MODES {
        let r = run(ALL, mode);
        let o = r.outcomes.as_ref().unwrap();
        assert_eq!(
            r.row["outcomes"]["obligations"].as_array().unwrap().len(),
            5
        );
        for name in ["unique", "covered", "exact", "absent"] {
            assert_eq!(obligation(o, name)["state"], "counterexample");
        }
        let exact = obligation(o, "exact");
        assert_eq!(exact["components"]["coverage"]["state"], "counterexample");
        assert_eq!(exact["components"]["uniqueness"]["state"], "counterexample");
        assert_eq!(exact["findings"], 2);
        assert_eq!(obligation(o, "trivial")["state"], "proved");
        assert_eq!(
            obligation(o, "trivial")["components"]["uniqueness"]["implicit_proved_groups"],
            2
        );
        assert_eq!(
            r.row["outcomes"]["notices_by_state"],
            json!({"always-true":1,"impossible":1,"parent-unreachable":1,"varying":1})
        );
        assert!(r.row["timings_ns"]["notices"].is_number());
        assert_eq!(
            r.row["verification_call_ns"].as_u64().unwrap(),
            r.row["timings_ns"]["checking"].as_u64().unwrap()
                + r.row["timings_ns"]["notices"].as_u64().unwrap()
        );
        let p = snapshot(ALL).load(false).unwrap();
        let l = config().limits;
        let req = p.verification_requests(&l).unwrap().remove(0).1;
        let (results, status) = ordinary(&p, &req, &l);
        assert_eq!(o, &Outcomes::from_results(&p, &results.value));
        assert_eq!(r.row["outcomes"]["state"], status["state"]);
    }
}
#[test]
fn inconsistent_context_and_consistency_only_are_not_vacuous_proofs() {
    let text = "relation r(); r(); assumption impossible: empty(r); obligation none: empty(r); notice n: varies(r); verification v { assumptions: [impossible]; obligations: [none]; notices: [n]; }";
    for mode in scorecard_support::MODES {
        let r = run(text, mode);
        let o = r.outcomes.as_ref().unwrap();
        assert_eq!(o.consistency, "inconsistent");
        assert_eq!(obligation(o, "none")["state"], "not-checked");
        assert!(r.row["timings_ns"]["notices"].is_null());
        if mode != "global-bdd" {
            assert_eq!(r.row["effective_path"], "global-bdd-general-assumptions");
        }
        assert_eq!(r.row["outcomes"]["state"], "inconsistent-assumptions");
    }
    let r = run(
        "verification v { assumptions: []; obligations: []; }",
        "cached-bdd",
    );
    assert_eq!(r.row["outcomes"]["state"], "proved");
    assert_eq!(r.row["outcomes"]["obligations"], json!([]));
}
#[test]
fn notices_unknown_and_regions_do_not_become_proofs() {
    let text = "relation r(); r() :- !r(); obligation absent: empty(r); notice n: varies(r); verification v { assumptions: []; obligations: [absent]; notices: [n]; }";
    let p = snapshot(text).load(false).unwrap();
    let l = config().limits;
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let (_, status) = ordinary(&p, &req, &l);
    for mode in scorecard_support::MODES {
        let r = run(text, mode);
        assert_eq!(r.row["outcomes"]["state"], status["state"]);
        assert_ne!(r.row["outcomes"]["state"], "proved");
        assert_eq!(r.row["outcomes"]["notices_by_state"], json!({"unknown":1}));
        assert!(
            r.row["outcomes"]["regions"]["unsupported"]
                .as_u64()
                .unwrap()
                > 0
        );
        assert!(r.row["outcomes"]["regions"]["no_meaning"].as_u64().unwrap() > 0);
    }
}
#[test]
fn instrumentation_preserves_results_receipts_and_resets_after_early_returns() {
    let p = snapshot(ALL).load(false).unwrap();
    let l = config().limits;
    let ops = OperationalLimits::from(&l);
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = req.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let mut metrics = VerificationMetrics::default();
    let CheckOutcome::Complete(plain) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let CheckOutcome::Complete(measured) =
        prepared.verify_with_metrics(&ops, &mut metrics).unwrap()
    else {
        panic!()
    };
    assert_eq!(plain.results, measured.results);
    assert!(metrics.notices.is_some());
    let mut s = Session::default();
    let LocalCheckOutcome::Complete(plain) = s.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    let LocalCheckOutcome::Complete(measured) = s
        .verify_with_metrics(&prepared, &ops, &mut metrics)
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(plain.checked.results, measured.checked.results);
    assert!(metrics.notices.is_some());
    let cancelled = OperationalLimits::from(&l);
    cancelled.cancellation.cancel();
    assert!(
        s.verify_with_metrics(&prepared, &cancelled, &mut metrics)
            .is_err()
    );
    assert!(metrics.notices.is_none());
    // Use an independent token; clone above deliberately shared only its fresh Limits token.
    let ops = OperationalLimits::from(&Limits::default());
    metrics.notices = Some(Duration::from_secs(1));
    let p = snapshot("verification v { assumptions: []; obligations: []; }")
        .load(false)
        .unwrap();
    let req = p
        .verification_requests(&Limits::default())
        .unwrap()
        .remove(0)
        .1;
    let RequestPreparation::Complete(prepared) = req.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    prepared
        .admit(&ops)
        .unwrap()
        .verify_with_metrics(&ops, &mut metrics)
        .unwrap();
    assert!(metrics.notices.is_none());
}
#[test]
fn preparation_exhaustion_keeps_unreached_metrics_unavailable() {
    let p = snapshot(ALL).load(false).unwrap();
    let mut l = config().limits;
    let mut s = scorecard_support::session("cached-bdd", false);
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let warm = measure(&p, &request, "cached-bdd", &mut s, &l);
    assert!(warm.row["cache"].is_object());
    l.max_atoms = 0;
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let exhausted = measure(&p, &request, "cached-bdd", &mut s, &l);
    assert_eq!(exhausted.row["outcomes"]["state"], "incomplete");
    assert!(
        !exhausted.row["outcomes"]["inconclusive"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(exhausted.row["outcomes"]["consistency"], "unknown");
    for stage in ["admission", "checking", "notices"] {
        assert!(exhausted.row["timings_ns"][stage].is_null());
    }
    for field in ["cache", "size"] {
        assert!(exhausted.row[field].is_null());
    }
    l.cancellation.cancel();
    let interrupted = measure(&p, &request, "cached-bdd", &mut s, &l);
    assert!(interrupted.row["error"].is_object());
    assert!(interrupted.row["preparation_cache"].is_null());
}
#[test]
fn missing_edit_is_omitted_and_warm_uses_new_handles() {
    let report = driver::collect(&config(), &snapshot(ALL), None).unwrap();
    assert_eq!(report["failures"], json!([]));
    for mode in scorecard_support::MODES {
        let row = &report["verifications"][0]["samples"][0][mode];
        assert!(row.get("edit").is_none());
        assert_eq!(row["warm"]["warm_equals_cold"], true);
    }
    assert!(!report.to_string().contains("\"observation\":"));
    assert!(!report.to_string().contains("produced(a, x)"));
}
#[test]
fn trivia_file_move_and_changed_selection_match_fresh_controls() {
    let base = snapshot(ALL);
    let mut edited = snapshot(&format!(
        "// moved\n{}",
        ALL.replace(
            "obligations: [unique, covered, exact, absent, trivial]",
            "obligations: [trivial]"
        )
    ));
    edited.sources[0].uri = "file:///elsewhere/renamed.den".into();
    edited.membership =
        ProgramMembership::single("file:///elsewhere", [edited.sources[0].uri.clone()]);
    let report = driver::collect(&config(), &base, Some(&edited)).unwrap();
    assert_eq!(report["failures"], json!([]));
    assert_eq!(report["verifications"][0]["change"], "retained");
    for mode in scorecard_support::MODES {
        let row = &report["verifications"][0]["samples"][0][mode];
        assert_eq!(row["cold"]["outcomes"]["state"], "findings");
        assert_eq!(row["edit"]["outcomes"]["state"], "proved");
        assert_eq!(row["edit"]["matches_fresh_control"], true);
    }
    // File movement and trivia alone preserve the complete keyed projection.
    edited.sources[0].text = format!("\n// moved\n{ALL}").into();
    let p = base.load(false).unwrap();
    let e = edited.load(false).unwrap();
    let l = config().limits;
    let r = p.verification_requests(&l).unwrap().remove(0).1;
    let er = e.verification_requests(&l).unwrap().remove(0).1;
    assert_eq!(r, er);
    let (a, _) = ordinary(&p, &r, &l);
    let (b, _) = ordinary(&e, &er, &l);
    assert_eq!(
        Outcomes::from_results(&p, &a.value),
        Outcomes::from_results(&e, &b.value)
    );
}
#[test]
fn added_removed_and_unconfigured_are_explicit() {
    let base = snapshot("verification old { assumptions: []; obligations: []; }");
    let edited = snapshot("verification new { assumptions: []; obligations: []; }");
    let report = driver::collect(&config(), &base, Some(&edited)).unwrap();
    assert_eq!(report["failures"], json!([]));
    let list = report["verifications"].as_array().unwrap();
    assert_eq!(list.len(), 2);
    for v in list {
        for mode in scorecard_support::MODES {
            let row = &v["samples"][0][mode];
            if v["change"] == "added" {
                assert!(row.get("cold").is_none());
                assert!(row.get("warm").is_none());
                assert!(row.get("edit").is_some());
            } else {
                assert_eq!(v["change"], "removed");
                assert!(row.get("edit").is_none());
            }
        }
    }
    let unconfigured = driver::collect(
        &config(),
        &snapshot("relation r(); obligation o: empty(r);"),
        None,
    )
    .unwrap();
    assert_eq!(
        unconfigured["configuration"]["base"]["state"],
        "unconfigured"
    );
    assert_eq!(
        unconfigured["configuration"]["base"]["unchecked_obligations"],
        json!(["o"])
    );
    assert_eq!(unconfigured["verifications"], json!([]));
}
#[test]
fn keyed_comparison_detects_swapped_failures_with_equal_totals() {
    let source = "relation a(); relation b(); a(); obligation first: empty(a); obligation second: empty(b); verification v { assumptions: []; obligations: [first, second]; }";
    let a = run(source, "global-bdd").outcomes.unwrap();
    let b = run(&source.replace("b(); a();", "b(); b();"), "global-bdd")
        .outcomes
        .unwrap();
    assert_eq!(
        a.json()["obligations_by_kind"],
        b.json()["obligations_by_kind"]
    );
    assert_ne!(a, b);
    assert!(a.contradicts(&b));
}
#[test]
fn in_repo_examples_match_check_den_presentation() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    for root in [
        "editors/den/examples/library-and-app/app",
        "editors/den/examples/library-and-app/lib",
        "editors/den/examples/semantic-checking",
        "editors/den/examples/condition-notices",
    ] {
        let p = Snapshot::discover(&repo.join(root))
            .unwrap()
            .load(false)
            .unwrap();
        let l = config().limits;
        for (_, request) in p.verification_requests(&l).unwrap() {
            let (plain, status) = ordinary(&p, &request, &l);
            for mode in scorecard_support::MODES {
                let r = measure(
                    &p,
                    &request,
                    mode,
                    &mut scorecard_support::session(mode, false),
                    &l,
                );
                assert_eq!(r.row["outcomes"]["state"], status["state"], "{root}/{mode}");
                let expected = Outcomes::from_results(&p, &plain.value);
                assert!(!r.outcomes.as_ref().unwrap().contradicts(&expected));
            }
        }
    }
}
#[test]
fn exported_test_dsl_regression_matches_check_den() {
    let text = include_str!("../../../test-dsl/fixtures/corpus.txt")
        .split("\n---")
        .next()
        .unwrap();
    let assembled = denotate_test_dsl::export::assemble(&[SourceFile::new(
        "file:///regression.testdsl",
        1,
        text,
    )])
    .unwrap();
    let paths = assembled
        .sources
        .snapshots()
        .map(|s| (s.id, "program.den".into()))
        .collect::<BTreeMap<_, _>>();
    let bundle = denotate_test_dsl::export::bundle(
        &assembled.program,
        &assembled.sources,
        &paths,
        denotate_ir_text::PrintOptions {
            embedded_origins: false,
        },
    )
    .unwrap();
    let (membership, sources) = bundle.documents("file:///export");
    let snapshot = Snapshot {
        membership,
        sources,
    };
    let p = snapshot.load(false).unwrap();
    let l = config().limits;
    let requests = p.verification_requests(&l).unwrap();
    assert_eq!(requests.len(), 1);
    let (plain, status) = ordinary(&p, &requests[0].1, &l);
    let report = driver::collect(&config(), &snapshot, None).unwrap();
    assert_eq!(report["failures"], json!([]));
    for mode in scorecard_support::MODES {
        let r = measure(
            &p,
            &requests[0].1,
            mode,
            &mut scorecard_support::session(mode, false),
            &l,
        );
        assert_eq!(r.row["outcomes"]["state"], status["state"]);
        assert_eq!(
            r.outcomes.unwrap(),
            Outcomes::from_results(&p, &plain.value)
        );
    }
}
#[test]
fn arguments_keep_retention_separate_from_logical_limits_and_protect_sources() {
    let c = Config::parse(
        [
            "root",
            "--samples",
            "2",
            "--unconstrained",
            "--json",
            "root/program.den",
        ]
        .map(String::from),
    )
    .unwrap();
    assert_eq!(
        DeterministicLimits::from(&c.limits),
        DeterministicLimits::from(&Limits::default())
    );
    assert!(c.validate_output(&snapshot(ALL), None).is_err());
    for args in [
        vec!["root", "--samples", "0"],
        vec!["root", "--timeout-ms", "0"],
        vec!["root", "--edit"],
        vec!["root", "--help"],
    ] {
        assert!(Config::parse(args.into_iter().map(String::from)).is_err());
    }
}

#[test]
fn general_assumption_fallback_keeps_instrumentation_observational() {
    let text = "input enabled(); assumption required: at_least_one(enabled, group_by: ()); obligation off: empty(enabled); notice n: varies(enabled); verification v { assumptions: [required]; obligations: [off]; notices: [n]; }";
    let p = snapshot(text).load(false).unwrap();
    let l = config().limits;
    let ops = OperationalLimits::from(&l);
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let mut session = Session::default();
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(plain) = session.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    let mut metrics = VerificationMetrics::default();
    let LocalCheckOutcome::Complete(measured) = session
        .verify_with_metrics(&prepared, &ops, &mut metrics)
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(plain.checked.results, measured.checked.results);
    assert!(metrics.notices.is_some());
    let r = run(text, "cached-bdd");
    assert_eq!(r.row["effective_path"], "global-bdd-general-assumptions");
    assert_eq!(r.row["outcomes"]["state"], "findings");
    assert_eq!(
        r.row["outcomes"]["notices_by_state"],
        json!({"always-true":1})
    );
    assert_eq!(r.row["cache"]["verdict_hits"], 0);
}

#[test]
fn symbolic_exhaustion_keeps_independent_notice_pass_visible() {
    let p=snapshot("input a(); input b(); relation both(); both() :- a(), b(); obligation absent: empty(both); notice n: varies(both); verification v { assumptions: []; obligations: [absent]; notices: [n]; }").load(false).unwrap();
    // Each input condition fits; their conjunction does not. This is a bounded
    // outcome test, not an assertion about an exact node count or work receipt.
    let l = Limits {
        max_bdd_nodes: 3,
        ..Limits::default()
    };
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let r = measure(&p, &request, "global-bdd", &mut None, &l);
    assert_eq!(r.row["outcomes"]["state"], "incomplete");
    assert_eq!(r.row["outcomes"]["consistency"], "consistent");
    assert!(r.row["timings_ns"]["checking"].is_number());
    assert!(r.row["timings_ns"]["notices"].is_number());
    assert_eq!(r.row["outcomes"]["notices_by_state"], json!({"unknown":1}));
    assert!(
        r.row["outcomes"]["inconclusive"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["resource"] == "BDD nodes")
    );
}

#[test]
fn known_exactly_one_failure_survives_incomplete_other_component() {
    let p = snapshot(ALL).load(false).unwrap();
    let l = config().limits;
    let request = p.verification_requests(&l).unwrap().remove(0).1;
    let (mut result, _) = ordinary(&p, &request, &l);
    // The checker already tests how partial reports arise. Here the projection
    // must preserve their two independent facts: known failure and incompleteness.
    let key = result
        .value
        .coverage
        .keys()
        .find(|k| k.0.name.as_ref() == "exact")
        .unwrap()
        .clone();
    let coverage = result.value.coverage.get_mut(&key).unwrap();
    coverage.missing = 0;
    coverage.examined = 0;
    coverage.examples.clear();
    coverage.inconclusive = Some(Inconclusive {
        phase: "coverage",
        resource: "work",
        details: Default::default(),
    });
    let o = Outcomes::from_results(&p, &result.value);
    assert_eq!(obligation(&o, "exact")["state"], "counterexample");
    assert_eq!(obligation(&o, "exact")["complete"], false);
    assert_eq!(obligation(&o, "exact")["findings"], 1);
    assert_eq!(
        obligation(&o, "exact")["components"]["coverage"]["state"],
        "inconclusive"
    );
    assert_eq!(
        obligation(&o, "exact")["components"]["coverage"]["count_kind"],
        "lower-bound"
    );
}
