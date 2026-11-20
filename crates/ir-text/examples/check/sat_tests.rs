use super::tests::Fixture;

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
