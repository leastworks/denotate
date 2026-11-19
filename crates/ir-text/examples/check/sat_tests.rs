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
