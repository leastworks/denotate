use super::tests::Fixture;
use super::{Limits, filesystem, options, sat};

#[test]
fn completion_cli_all_rejected_and_explicit_rejection_obligation() {
    for (declaration, selection, exit) in [
        ("", "", 0),
        ("obligation total:no_rejections(h);", "total", 1),
    ] {
        let f = Fixture::new(&format!(
            "relation h();{declaration}verification v{{semantics:completion;hypothesis:h;assumptions:[];obligations:[{selection}];}}"
        ));
        for json in [false, true] {
            let mut flags = vec!["--engine", "sat", "--no-progress"];
            if json {
                flags.push("--json");
            }
            let (code, out) = f.run(&flags);
            assert_eq!(code, exit, "{out}");
            assert!(out.contains("all-rejected"), "{out}");
            assert!(out.contains("not-applicable"), "{out}");
            if !json {
                assert!(out.contains("Semantics: completion"));
                assert!(!out.contains("Result: proved"));
            }
        }
    }
}
#[test]
fn completion_cli_evidence_meaning_and_mixed_semantics() {
    let f = Fixture::new(
        "relation p();p():-p();relation h();h():-p();relation odd();odd():-!odd();obligation clean:empty(p);verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[clean];}verification stable{assumptions:[];obligations:[];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("Present tuple: p()"), "{out}");
    assert!(out.contains("no-meaning"));
    assert!(out.contains("Verification ::stable"));
    let (code, out) = f.run(&["--engine", "sat", "--no-progress", "--json"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("original-completion-v1"));
    assert!(out.contains("original-stable-v1"));
    assert!(out.contains("completion-model"));
    assert!(!out.contains("circular-support"));
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--completion-circular-support",
    ]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("circular-support"));
    assert_eq!(
        f.run(&["--engine", "sat", "--no-progress", "--sat-meaning", "none"])
            .0,
        2
    );
    assert_eq!(
        f.run(&["--engine", "sat", "--no-progress", "--verification", "v"])
            .0,
        2
    );
    assert_eq!(f.run(&["--no-progress"]).0, 2);
}
#[test]
fn completion_cli_symbolic_worlds_cutoffs_and_assumption_diagnostics() {
    let f = Fixture::new(
        "input i();relation h();obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[total];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--sat-max-worlds", "1", "--no-progress"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("counterexample"), "{out}");
    assert!(out.contains("all-rejected"), "{out}");
    let (code, out) = f.run(&["--engine", "sat", "--sat-max-worlds", "0", "--no-progress"]);
    assert_eq!(code, 2, "{out}");
    assert!(!out.contains("counterexample"), "{out}");
    assert!(out.contains("worlds"), "{out}");
    let f = Fixture::new(
        "relation p();p():-p();assumption a:empty(p);verification v{semantics:completion;assumptions:[a];obligations:[];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--no-progress", "--json"]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("completion-assumption-ambiguity"), "{out}");
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--max-atoms",
        "0",
        "--no-progress",
        "--json",
    ]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("resource"), "{out}");
}

#[test]
fn sat_cli_checks_overlap_and_preserves_partial_selection_and_default_engine() {
    let f = Fixture::new(
        "sort S;const a,b:S;input i(x:S);relation r(x:S);r(X):-i(X);obligation one:at_most_one(r,group_by:());verification v{assumptions:[];obligations:[one];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--no-progress", "--max-bdd-nodes", "0"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("Backend: sat"));
    assert!(out.contains("2 distinct tuples hold"));
    assert!(out.contains("program.den:"));
    assert!(out.contains("Meaning uniqueness (whole program): at-most-one"));
    assert_eq!(
        f.run(&["--engine", "sat", "--verification", "v", "--no-progress"])
            .0,
        2
    );
    let (code, normal) = f.run(&["--no-progress"]);
    assert_eq!(code, 1);
    assert!(normal.contains("Backend: bdd"));
    for flags in [
        vec!["--engine", "sat", "--checking-within-w"],
        vec!["--engine", "sat", "--sat-probe"],
        vec!["--sat-max-solves", "2"],
        vec!["--engine", "other"],
    ] {
        assert_eq!(f.run(&flags).0, 2);
    }
}
#[test]
fn sat_fixed_checks_include_coverage_exactly_one_and_independent_errors() {
    let f=Fixture::new("sort S;const a,b:S;relation r(x:S);r(a);r(b);relation absent(x:S);relation p();p():-!p();
        obligation e:empty(r);obligation u:at_most_one(r,group_by:());obligation c:at_least_one(absent,group_by:(x));obligation x:exactly_one(r,group_by:());
        verification v{assumptions:[];obligations:[e,u,c,x];}");
    let (code, out) = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("no-meaning"));
    for name in [
        "e (empty)",
        "u (at-most-one)",
        "c (at-least-one)",
        "x (exactly-one)",
    ] {
        assert!(
            out.contains(&format!("Obligation {name}: counterexample [fixed]")),
            "{out}"
        );
    }
    assert!(out.contains("2 groups fail coverage"));
    assert!(!out.contains("not-analysed"));
}
#[test]
fn sat_cli_reports_unanalysed_kinds_and_every_meaning_state() {
    for (rules, expected, code) in [
        ("relation r();", "every-world", 0),
        ("relation r();r():-!r();", "no-meaning", 1),
        (
            "relation r();relation q();r():-!q();q():-!r();",
            "multiple-meanings",
            1,
        ),
    ] {
        let f = Fixture::new(&format!(
            "{rules} verification v{{assumptions:[];obligations:[];}}"
        ));
        let (c, out) = f.run(&["--engine", "sat", "--json", "--no-progress"]);
        assert_eq!(c, code, "{out}");
        assert!(out.contains(expected), "{out}");
    }
    let f = Fixture::new(
        "input i();obligation o:at_least_one(i,group_by:());notice n:varies(i);verification v{assumptions:[];obligations:[o];notices:[n];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("Obligation o (at-least-one): not-analysed"));
    assert!(out.contains("Notice n: not analysed"));
    let f = Fixture::new(
        "input i();assumption a:empty(i);assumption b:at_least_one(i,group_by:());relation r();obligation e:empty(r);verification v{assumptions:[a,b];obligations:[e];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("inconsistent-assumptions"));
}
#[test]
fn sat_limits_are_explicit_and_keep_earlier_fixed_failures() {
    let f = Fixture::new(
        "relation a();relation b();a():-!b();b():-!a();relation bad();bad();obligation e:empty(bad);verification v{assumptions:[];obligations:[e];}",
    );
    let (code, out) = f.run(&["--engine", "sat", "--sat-max-worlds", "0", "--no-progress"]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("relation is not empty"));
    assert!(out.contains("Meaning existence (whole program): inconclusive"));
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--sat-max-solves",
        "0",
        "--json",
        "--no-progress",
    ]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("solves"));
}

#[test]
fn sat_meaning_modes_keep_exit_incomplete_and_fixed_findings_visible() {
    for body in [
        "relation bad();",
        "relation bad();bad();",
        "relation bad();bad():-bad();",
    ] {
        let f = Fixture::new(&format!(
            "{body} obligation e:empty(bad);verification v{{assumptions:[];obligations:[e];}}"
        ));
        for mode in ["none", "uniqueness"] {
            for json in [false, true] {
                let mut flags = vec!["--engine", "sat", "--sat-meaning", mode, "--no-progress"];
                if json {
                    flags.push("--json");
                }
                let (code, out) = f.run(&flags);
                assert_eq!(code, 2, "{out}");
                assert!(out.contains("not-analysed"), "{out}");
                assert!(out.contains("disabled-by-option"), "{out}");
                if !json {
                    let expected = if body.contains("bad();bad();") {
                        "counterexample"
                    } else {
                        "proved"
                    };
                    assert!(
                        out.contains(&format!("Obligation e (empty): {expected} [fixed]")),
                        "{out}"
                    );
                }
            }
        }
        let implicit = f.run(&["--engine", "sat", "--no-progress"]);
        assert_eq!(
            implicit,
            f.run(&["--engine", "sat", "--sat-meaning", "full", "--no-progress"])
        );
        for flags in [
            vec!["--sat-meaning", "none"],
            vec!["--engine", "sat", "--sat-meaning", "invalid"],
        ] {
            assert_eq!(f.run(&flags).0, 2);
        }
    }
}

#[test]
fn sat_existence_reports_live_cube_statistics_and_skipped_phases_do_not_run() {
    let f = Fixture::new(
        "input flag();input unused();relation a();relation b();a():-flag();a():-!b();b():-!a();verification v{assumptions:[];obligations:[];}",
    );
    let (code, out, progress) = f.traced(&["--engine", "sat", "--json"]);
    assert_eq!(code, Ok(1)); // ambiguous, but all worlds have meaning
    assert!(out.contains("existenceStats"));
    assert!(out.contains("uniquenessStats"));
    for field in [
        "downstream-cone",
        "pairQueries",
        "extensionQueries",
        "fallbackReason",
    ] {
        assert!(out.contains(field), "{out}");
        assert!(progress.contains(field), "{progress}");
    }
    assert!(progress.contains("SAT uniqueness finished:"));
    for field in [
        "cubes",
        "inputsPerCube",
        "supportSize",
        "componentsTotal",
        "scopes",
        "component",
        "position",
        "statistics",
        "fallbackReason",
        "distinctInputs",
        "distinctCubeLiterals",
        "emittedExclusionLiterals",
        "emittedSelectorLiterals",
    ] {
        assert!(progress.contains(field), "{field}: {progress}");
    }
    assert!(progress.contains("SAT existence progress:"), "{progress}");
    assert!(progress.contains("SAT existence finished:"), "{progress}");
    let (_, _, progress) = f.traced(&["--engine", "sat", "--sat-meaning", "none"]);
    assert!(!progress.contains("SAT existence"));
    assert!(!progress.contains("SAT uniqueness"));
    let (_, _, progress) = f.traced(&["--engine", "sat", "--sat-meaning", "uniqueness"]);
    assert!(!progress.contains("SAT existence"));
    assert!(progress.contains("SAT uniqueness"));
}

#[test]
fn sat_component_inventory_without_meaning_and_bounded_dump() {
    let f = Fixture::new(
        "relation a();relation b();relation c();a():-!b();b():-!a();c():-a(),!c();verification v{assumptions:[];obligations:[];}",
    );
    let args = ["--engine", "sat", "--sat-meaning", "none", "--no-progress"];
    let (code, out) = f.run(&args);
    assert_eq!(code, 2);
    assert!(out.contains("Negative components: 2"), "{out}");
    assert!(out.contains("Component 1: 2 atoms"));
    assert!(out.contains("Component 2: 1 atoms"));
    assert!(out.contains("a() -["));
    assert!(out.contains(", -]-> ::b()"), "{out}");
    assert!(out.contains("program.den:1:"));
    assert_eq!(f.run(&args), (code, out.clone()));
    let (_, json) = f.run(&[
        "--engine",
        "sat",
        "--sat-meaning",
        "none",
        "--json",
        "--no-progress",
    ]);
    let inventory: serde_json::Value =
        serde_json::Deserializer::from_str(json.split_once("Negative components: ").unwrap().1)
            .into_iter()
            .next()
            .unwrap()
            .unwrap();
    assert_eq!(inventory["total"], 2);
    assert_eq!(
        inventory["components"][1]["cycle"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    for (file, cap, complete) in [("full.jsonl", "10000", true), ("short.jsonl", "2", false)] {
        let path = f.0.join(file);
        let mut options = args.to_vec();
        options.extend([
            "--dump-component",
            path.to_str().unwrap(),
            "--dump-component-limit",
            cap,
        ]);
        assert_eq!(f.run(&options), (code, out.clone()));
        let rows: Vec<serde_json::Value> = std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        if complete {
            assert!(
                rows.iter()
                    .any(|r| r["record"] == "graph-end" && r["complete"] == true)
            );
            assert_eq!(rows.iter().filter(|r| r["record"] == "atom").count(), 3);
            assert!(
                rows.iter()
                    .any(|r| r["record"] == "rule" && r["rule"]["source"]["uri"].is_string())
            );
        } else {
            assert!(rows.iter().any(|r| r["record"] == "truncated"));
        }
    }
}

#[test]
fn sat_subsumption_removes_listed_cycle_and_positive_cycles_are_not_listed() {
    for rules in [
        "input x();relation p();relation q();p():-x(),!q();p():-x();q():-!p();",
        "input x();relation p();relation q();p():-x();p():-q();q():-p();",
    ] {
        let f = Fixture::new(&format!(
            "{rules}verification v{{assumptions:[];obligations:[];}}"
        ));
        let (code, out) = f.run(&["--engine", "sat", "--sat-max-worlds", "0", "--no-progress"]);
        assert_eq!(code, 0, "{out}");
        assert!(out.contains("Negative components: 0"));
        if rules.contains("!q") {
            assert!(out.contains("subsumed-producer"));
        }
    }
}

#[test]
fn sat_obligation_cones_report_scope_sizes_and_keep_exit_contract() {
    for (rules, code) in [
        ("relation r(); relation p(); p():-!p();", 0),
        (
            "relation a();relation b();a():-!b();b():-!a();relation r();r():-a();relation c();c():-r(),!c();",
            1,
        ),
        ("relation r();r():-!r();", 1),
    ] {
        let f = Fixture::new(&format!(
            "{rules} obligation o:empty(r); verification v{{assumptions:[];obligations:[o];}}"
        ));
        for json in [false, true] {
            let mut flags = vec!["--engine", "sat", "--sat-meaning", "cone", "--no-progress"];
            if json {
                flags.push("--json");
            }
            let (c, out) = f.run(&flags);
            assert_eq!(c, code, "{out}");
            if json {
                let summary: serde_json::Value =
                    serde_json::Deserializer::from_str(out.split_once("Results: ").unwrap().1)
                        .into_iter()
                        .next()
                        .unwrap()
                        .unwrap();
                assert_eq!(summary["meaning"]["scope"], "obligation-cones");
                assert_eq!(summary["meaning"]["outsideAnalysed"], false);
                assert!(summary["meaning"]["coneSize"]["atoms"].is_number());
            } else {
                assert!(
                    out.contains("Meaning existence (obligation cones):"),
                    "{out}"
                );
                assert!(out.contains("outside not analysed"), "{out}");
            }
        }
        assert_eq!(
            f.run(&[
                "--engine",
                "sat",
                "--sat-meaning",
                "cone",
                "--sat-max-solves",
                "0",
                "--no-progress"
            ])
            .0,
            2
        );
    }
    let f = Fixture::new(
        "relation a();relation b();a():-!b();b():-!a();relation r();r():-a(),b();obligation o:empty(r);verification v{assumptions:[];obligations:[o];}",
    );
    assert_eq!(
        f.run(&[
            "--engine",
            "sat",
            "--sat-meaning",
            "cone",
            "--sat-max-worlds",
            "0",
            "--no-progress"
        ])
        .0,
        2
    );
}

#[test]
fn sat_pins_and_meaning_splits_have_cli_controls_and_explicit_output() {
    let source = "sort M;const a,b:M;input phase(m:M) exactly_one(group_by:());
        relation p();relation q();p():-phase(a),!q();q():-phase(b),p();
        relation chosen();chosen():-phase(a);assumption selected:at_least_one(chosen,group_by:());
        obligation clean:empty(q);verification v{assumptions:[];obligations:[clean];}";
    let f = Fixture::new(source);
    let (code, out) = f.run(&["--engine", "sat", "--sat-max-worlds", "0", "--no-progress"]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("Meaning split:"));
    assert_eq!(
        f.run(&[
            "--engine",
            "sat",
            "--sat-max-split-candidates",
            "0",
            "--sat-max-worlds",
            "0",
            "--no-progress"
        ])
        .0,
        2
    );
    assert_eq!(
        f.run(&["--engine", "sat", "--sat-split", "phase", "--no-progress"])
            .0,
        0
    );
    for args in [
        vec!["--sat-split", "phase"],
        vec!["--engine", "sat", "--sat-split", "p"],
        vec!["--engine", "sat", "--sat-split", "missing"],
    ] {
        assert_eq!(f.run(&args).0, 2);
    }
    // A quoted input and a generated helper may share their display text.
    let named = Fixture::new(&format!(
        "namespace n {{ {} relation $phase(); }}",
        source.replace("phase", "'$phase'")
    ));
    let (code, out) = named.run(&[
        "--engine",
        "sat",
        "--sat-split",
        "n::'$phase'",
        "--no-progress",
    ]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        named
            .run(&["--engine", "sat", "--sat-split", "n::$phase"])
            .0,
        2
    );
    let f = Fixture::new(&source.replace("assumptions:[]", "assumptions:[selected]"));
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--sat-max-split-candidates",
        "0",
        "--sat-max-worlds",
        "0",
        "--no-progress",
    ]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("Input pins: 2 proved"));
    assert_eq!(
        f.run(&[
            "--engine",
            "sat",
            "--sat-max-pin-candidates",
            "0",
            "--sat-max-split-candidates",
            "0",
            "--sat-max-worlds",
            "0",
            "--no-progress"
        ])
        .0,
        2
    );
}

#[test]
fn completion_cli_does_not_call_classification_contradictions_rejections() {
    let f = Fixture::new(
        "relation h();h():-!h();obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[total];}",
    );
    for json in [false, true] {
        let mut flags = vec!["--engine", "sat", "--no-progress"];
        if json {
            flags.push("--json");
        }
        let (code, out) = f.run(&flags);
        assert_eq!(code, 1, "{out}");
        assert!(out.contains("no-meaning"), "{out}");
        assert!(!out.contains("all-rejected"), "{out}");
        assert!(!out.contains("rejected-observation"), "{out}");
        if !json {
            assert!(out.contains("total (no-rejections): proved"), "{out}");
            assert!(out.contains("rejected none"), "{out}");
        }
    }
}

#[test]
fn completion_cli_selected_decisions_and_second_query_cutoff() {
    for (selection, code) in [("", 1), ("decisions:[h];", 0)] {
        let f = Fixture::new(&format!(
            "relation p();p():-p();relation h();h():-p();h():-!p();verification v{{semantics:completion;hypothesis:h;{selection}assumptions:[];obligations:[];}}"
        ));
        let (exit, out) = f.run(&["--engine", "sat", "--no-progress"]);
        assert_eq!(exit, code, "{out}");
        if code == 0 {
            assert!(out.contains("Decision relations: [h]"), "{out}");
        }
    }
    let f = Fixture::new(
        "relation h();obligation total:no_rejections(h);verification v{semantics:completion;hypothesis:h;assumptions:[];obligations:[total];}",
    );
    let (exit, out) = f.run(&["--engine", "sat", "--sat-max-solves", "1", "--no-progress"]);
    assert_eq!(exit, 2, "{out}");
    assert!(!out.contains("all-rejected"), "{out}");
    assert!(!out.contains("counterexample"), "{out}");
    assert!(out.contains("inconclusive"), "{out}");
}

#[test]
fn completion_cli_contract_truth_provider_scope_and_stable_audit_are_separate() {
    let f = Fixture::new(
        "relation p();relation q();p():-!q();q():-!p();relation valid();valid():-p();valid():-q();assumption a:at_least_one(valid,group_by:());verification v{semantics:completion;decisions:[];assumptions:[a];obligations:[];}",
    );
    for audit in [false, true] {
        let mut flags = vec!["--engine", "sat", "--no-progress"];
        if audit {
            flags.push("--validate-all-assumptions");
        }
        let (code, out) = f.run(&flags);
        assert_eq!(code, 0, "{out}");
        assert!(!out.contains("invalid-assumption"), "{out}");
        assert!(!out.contains("unvalidated-assumption"), "{out}");
    }
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--validate-all-assumptions",
        "--json",
    ]);
    assert_eq!(code, 0, "{out}");
    let audit = out
        .split_once("Assumption validation: ")
        .unwrap_or_else(|| panic!("missing audit: {out}"))
        .1
        .split("Verification ")
        .next()
        .unwrap();
    let audit: serde_json::Value = serde_json::from_str(audit).unwrap();
    assert_eq!(audit["assumptions"], serde_json::json!([]));
    assert_eq!(audit["findings"], serde_json::json!([]));
    let f = Fixture::new(
        "relation eligible();eligible():-eligible();input raw() within eligible;relation good();obligation o:empty(raw);obligation good:empty(good);verification a_bad{semantics:completion;decisions:[];assumptions:[];obligations:[o];}verification z_good{semantics:completion;decisions:[];assumptions:[];obligations:[good];}",
    );
    for json in [false, true] {
        let mut flags = vec!["--engine", "sat", "--no-progress"];
        if json {
            flags.push("--json");
        }
        let (code, out) = f.run(&flags);
        assert_eq!(code, 2, "{out}");
        assert!(out.contains("invalid-input-domain"), "{out}");
        assert!(out.contains("Verification ::z_good"), "{out}");
        assert!(out.contains("proved"), "{out}");
    }
}
#[test]
fn completion_cli_dead_producer_advisory_does_not_change_exit_codes() {
    let f = Fixture::new(
        "relation h();h();relation p();p():-p();relation absent();h():-p(),absent();verification v{semantics:completion;hypothesis:h;decisions:[h];assumptions:[];obligations:[];}",
    );
    let (code, plain) = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("dead-producer"));
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--completion-dead-producers",
    ]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("dead-producer"), "{out}");
    assert!(out.contains("p()"));
    assert_eq!(f.run(&["--completion-dead-producers"]).0, 2);
}

#[test]
fn completion_cli_shared_and_unselected_declarations_keep_stable_validation() {
    let prefix = "relation p();relation q();p():-!q();q():-!p();relation valid();valid():-p();valid():-q();assumption a:at_least_one(valid,group_by:());";
    let f = Fixture::new(&format!(
        "{prefix}verification done{{semantics:completion;decisions:[];assumptions:[a];obligations:[];}}verification stable{{assumptions:[a];obligations:[];}}"
    ));
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--validate-all-assumptions",
    ]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("invalid-assumption"), "{out}");
    assert!(out.contains("Verification ::done"), "{out}");
    assert!(out.contains("at-most-one"), "{out}");
    let f = Fixture::new(&format!(
        "{prefix}verification v{{semantics:completion;decisions:[];assumptions:[];obligations:[];}}"
    ));
    assert_eq!(f.run(&["--engine", "sat", "--no-progress"]).0, 0);
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--validate-all-assumptions",
    ]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("invalid-assumption"), "{out}");
}

#[test]
fn completion_cli_size_diagnostics_are_opt_in_and_keep_cutoff_counts() {
    let f = Fixture::new(
        "sort S;const a,b,c,d,e,f:S;relation loop(s:S);loop(X):-loop(X);verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let (plain_code, plain) = f.run(&["--engine", "sat", "--no-progress"]);
    assert!(!plain.contains("Completion preparation"));
    let (code, out) = f.run(&["--engine", "sat", "--no-progress", "--verbose"]);
    assert_eq!(code, plain_code);
    assert!(out.contains("Completion preparation work (includes grounding attempts)"));
    assert!(out.contains("work by stage:"));
    assert!(out.contains("circular-only"));
    assert!(out.contains("Completion CNF"));
    assert!(out.find("Completion preparation").unwrap() < out.find("Context:").unwrap());
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--no-progress",
        "--json",
        "--max-atoms",
        "3",
    ]);
    assert_eq!(code, 2, "{out}");
    let data = out.split_once("Completion preparation sizes: ").unwrap().1;
    let data: serde_json::Value = serde_json::Deserializer::from_str(data)
        .into_iter()
        .next()
        .unwrap()
        .unwrap();
    assert!(
        data["preparationWork"]["workByStage"]["runtime-grounding"]
            .as_u64()
            .unwrap()
            > 0
    );
    assert_eq!(data["preparations"][0]["complete"], false);
    assert_eq!(
        data["preparations"][0]["relations"][0]["state"],
        "partial-round"
    );
}

#[test]
fn completion_size_counts_reach_memory_profile() {
    let f = Fixture::new(
        "relation p();p():-p();verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let path = f.0.join("completion-profile.jsonl");
    let (code, out, _) = f.traced(&[
        "--engine",
        "sat",
        "--no-progress",
        "--profile-memory",
        path.to_str().unwrap(),
    ]);
    assert_eq!(code.unwrap(), 0, "{out}");
    let events = std::fs::read_to_string(&path)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    let prep = events
        .iter()
        .position(|e| e["type"] == "completion-preparation-sizes")
        .unwrap();
    assert!(events[prep]["sizes"]["preparations"][0]["complete"] == true);
    assert!(
        events[prep]["sizes"]["searches"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(
        prep < events
            .iter()
            .position(|e| e["type"] == "completion-sizes")
            .unwrap()
    );
    let event = events
        .iter()
        .find(|e| e["type"] == "completion-sizes")
        .unwrap();
    assert!(event["sizes"]["searches"].as_array().unwrap().len() > 0);
    assert_eq!(event["sizes"]["preparations"][0]["complete"], true);
}

#[test]
fn completion_preparation_sizes_are_flushed_before_checking_even_without_progress() {
    let f = Fixture::new(
        "relation p();p();verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let (membership, sources) = filesystem::discover(&f.0).unwrap();
    let p = denotate_ir_text::load(&membership, &sources).unwrap();
    let sink = denotate_check::CompletionSizes::default();
    let limits = Limits {
        completion_sizes: Some(sink.clone()),
        ..Default::default()
    };
    let mut flushed = false;
    let mut output = String::new();
    let result = sat::completion_inner(
        &p,
        p.corpus.verifications().next().unwrap(),
        &limits,
        &Default::default(),
        &Default::default(),
        false,
        0,
        512,
        false,
        false,
        false,
        true,
        false,
        &mut output,
        &None,
        &mut |text| {
            assert!(text.contains("Completion preparation sizes:"));
            assert!(text.contains("preparationWork"));
            assert!(
                sink.snapshot().searches.is_empty(),
                "checking ran before preparation was published"
            );
            flushed = true;
            limits.cancellation.cancel();
            Ok(())
        },
    );
    assert!(flushed);
    assert!(result.unwrap_err().1.contains("Cancelled"));
    assert!(!output.contains("Results:"));
}

#[test]
fn completion_size_progress_reports_the_diagnostic_pass() {
    let f = Fixture::new(
        "relation p();p();verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let (code, plain, quiet) = f.traced(&["--engine", "sat", "--verbose"]);
    assert_eq!(code.unwrap(), 0);
    assert!(!quiet.contains("completion size LFP"));
    assert!(plain.contains("work by phase"));
    let (code, _, trace) = f.traced(&["--engine", "sat", "--verbose", "--completion-size-lfp"]);
    assert_eq!(code.unwrap(), 0);
    assert!(trace.contains("completion size LFP"), "{trace}");
    assert!(trace.contains("component 1/1"), "{trace}");
    assert!(trace.contains("tuples"), "{trace}");
}

#[test]
fn sat_cli_defaults_and_overrides_do_not_depend_on_argument_order() {
    for flags in [
        vec![
            "root",
            "--engine",
            "sat",
            "--timeout-ms",
            "10",
            "--max-atoms",
            "100000",
            "--sat-max-polls",
            "3",
        ],
        vec![
            "root",
            "--sat-max-polls",
            "3",
            "--max-atoms",
            "100000",
            "--timeout-ms",
            "10",
            "--engine",
            "sat",
        ],
    ] {
        let o = options::Options::parse(flags.into_iter().map(str::to_owned), Limits::default())
            .unwrap();
        assert_eq!(o.limits.timeout, std::time::Duration::from_millis(10));
        assert_eq!(o.limits.max_atoms, 100000);
        assert_eq!(o.sat_query_limits.max_solver_polls, 3);
    }
    let b = options::Options::parse(["root".into()], Limits::default()).unwrap();
    let s = options::Options::parse(
        ["root".into(), "--engine".into(), "sat".into()],
        Limits::default(),
    )
    .unwrap();
    assert_eq!(b.limits.timeout, Limits::default().timeout);
    assert_eq!(s.limits.timeout, std::time::Duration::from_secs(120));
    assert!(s.limits.max_atoms > b.limits.max_atoms);
    let f = Fixture::new(
        "relation p();p();verification v{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let (code, out) = f.run(&[
        "--engine",
        "sat",
        "--timeout-ms",
        "0",
        "--json",
        "--no-progress",
    ]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("deadline"), "{out}");
}

#[test]
fn completion_full_models_is_explicit_and_not_enabled_by_verbose() {
    let f = Fixture::new(
        "relation p();p();obligation clean:empty(p);verification v{semantics:completion;assumptions:[];obligations:[clean];}",
    );
    for extra in [vec![], vec!["--verbose"], vec!["--completion-full-models"]] {
        let mut args = vec!["--engine", "sat", "--json", "--no-progress"];
        args.extend(extra.iter().copied());
        let (code, out) = f.run(&args);
        assert_eq!(code, 1, "{out}");
        let full = extra.contains(&"--completion-full-models");
        assert!(
            out.contains(if full {
                "\"fullModels\": true"
            } else {
                "\"fullModels\": false"
            }),
            "{out}"
        );
        assert!(out.contains("modelRef"));
    }
    let (code, _) = f.run(&["--completion-full-models"]);
    assert_eq!(code, 2);
}

#[test]
fn completion_pruning_is_opt_in_and_leaves_default_output_unchanged() {
    let f = Fixture::new(
        "input tag();relation accepted();relation profile();accepted():-tag();accepted():-profile();profile():-tag(),!accepted();verification v{semantics:completion;assumptions:[];obligations:[];}",
    );
    let flags = ["--engine", "sat", "--no-progress"];
    let (code, plain) = f.run(&flags);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("completion-pruning"));
    let (code, enabled) = f.run(&["--engine", "sat", "--no-progress", "--completion-prune"]);
    assert_eq!(code, 0, "{enabled}");
    assert!(enabled.contains("completion-pruning"), "{enabled}");
    assert_eq!(f.run(&flags), (0, plain));
    for enabled in [false, true] {
        let mut flags = vec!["--engine", "sat", "--no-progress", "--json"];
        if enabled {
            flags.push("--completion-prune");
        }
        let (code, out) = f.run(&flags);
        assert_eq!(code, 0, "{out}");
        assert_eq!(out.contains("\"simplifications\""), enabled, "{out}");
        assert_eq!(out.contains("completion pruning W"), enabled, "{out}");
        if !enabled {
            assert!(
                !out.contains("completion original validation index"),
                "{out}"
            );
        }
    }
    assert_eq!(f.run(&["--completion-prune"]).0, 2);
    assert!(options::help().contains("--completion-prune"));
}

#[test]
fn targeted_pruning_reports_considered_proved_and_optional_cutoffs_without_verbose() {
    let mut text = "input tag();relation accepted();accepted():-tag();".to_owned();
    for n in 0..16 {
        text.push_str(&format!(
            "relation profile{n}();accepted():-profile{n}();profile{n}():-tag(),!accepted();"
        ));
    }
    text.push_str("verification v{semantics:completion;assumptions:[];obligations:[];}");
    let f = Fixture::new(&text);
    let (code, output) = f.run(&["--engine", "sat", "--no-progress", "--completion-prune"]);
    assert_eq!(code, 0, "{output}");
    assert!(
        output.contains("candidates considered") && output.contains("proved"),
        "{output}"
    );
    let mut saw_cutoff = false;
    for work in ["500", "1000", "2000", "4000"] {
        let (_, out) = f.run(&[
            "--engine",
            "sat",
            "--no-progress",
            "--completion-prune",
            "--max-work",
            work,
        ]);
        if out.contains("Pruning optional cutoff:") {
            assert!(out.contains("work"), "{out}");
            saw_cutoff = true;
            break;
        }
    }
    assert!(
        saw_cutoff,
        "resource cutoff must not be hidden in JSON only"
    );
}

#[test]
fn completion_branches_are_opt_in_and_report_the_chosen_input_values() {
    let f = Fixture::new(
        "sort Tag;const a,b:Tag;input tag(v:Tag) exactly_one(group_by:());relation p();relation q();p():-tag(a);p():-tag(b),q();q():-tag(b);q():-tag(a),!p();verification v{semantics:completion;assumptions:[];obligations:[];}",
    );
    let (code, plain) = f.run(&["--engine", "sat", "--json", "--no-progress"]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("\"branches\""));
    let (code, shown) = f.run(&[
        "--engine",
        "sat",
        "--completion-split-depth",
        "2",
        "--completion-split-branches",
        "8",
        "--no-progress",
    ]);
    assert_eq!(code, 0, "{shown}");
    assert!(shown.contains("split group tag(a)"), "{shown}");
    assert!(shown.contains("tag(a)=true"), "{shown}");
    assert!(shown.contains("tag(b)=true"), "{shown}");
    let (code, json) = f.run(&[
        "--engine",
        "sat",
        "--completion-split-depth",
        "2",
        "--json",
        "--no-progress",
    ]);
    assert_eq!(code, 0, "{json}");
    assert!(json.contains("\"branches\""));
    assert!(json.contains("\"guardedEdges\""));
    let plain_human = f.run(&["--engine", "sat", "--no-progress"]);
    assert_eq!(
        f.run(&[
            "--engine",
            "sat",
            "--completion-split-depth",
            "0",
            "--no-progress"
        ]),
        plain_human
    );
    assert_eq!(f.run(&["--completion-split-depth", "2"]).0, 2);
}
