use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::{Cardinality, top_level};
use denotate_ir_text::*;
use denotate_presentation::{Identity, Kind};
use std::collections::BTreeSet;
mod support;

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
const V: &str = "verification checks { assumptions: []; obligations: [one]; }";
fn run(
    p: &LoadedProgram,
    session: &mut Session,
    limits: &Limits,
) -> (ScopedResults, presentation::Presentation) {
    let ops = OperationalLimits::from(limits);
    let request = p.verification_requests(limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("preparation incomplete")
    };
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        panic!("checking incomplete")
    };
    let output = presentation::present(p, &report.checked).unwrap();
    assert_eq!(
        report.checked.verification.all_obligations_proved(),
        output.status["state"] == "proved"
    );
    (report.checked.results.value, output)
}
fn check(text: &str) -> (ScopedResults, presentation::Presentation) {
    run(
        &load_text(text),
        &mut Session::default(),
        &Limits::default(),
    )
}
fn uniqueness_proved(results: &ScopedResults) -> bool {
    results
        .groups
        .values()
        .all(|g| matches!(g, ScopedResult::Proved))
}

#[test]
fn independent_parts_cover_empty_global_zero_arity_and_distinct_tuples() {
    for (body, coverage, uniqueness, no_groups) in [
        (
            "sort S; const a,b:S; relation p(x:S); obligation one: exactly_one(p, group_by: ());",
            false,
            true,
            false,
        ),
        (
            "sort S; const a,b:S; relation p(x:S); p(a); obligation one: exactly_one(p, group_by: ());",
            true,
            true,
            false,
        ),
        (
            "sort S; const a,b:S; relation p(x:S); p(a); p(b); obligation one: exactly_one(p, group_by: ());",
            true,
            false,
            false,
        ),
        (
            "sort S; relation p(x:S); obligation one: exactly_one(p, group_by: (x));",
            true,
            true,
            true,
        ),
        (
            "sort S; relation p(x:S); obligation one: exactly_one(p, group_by: ());",
            false,
            true,
            false,
        ),
        (
            "relation p(); obligation one: exactly_one(p, group_by: ());",
            false,
            true,
            false,
        ),
        (
            "relation p(); p(); p(); obligation one: exactly_one(p, group_by: ());",
            true,
            true,
            false,
        ),
        (
            "sort S; const a,b:S; domain S=[a]; relation p(x:S); p(a); p(a); obligation one: exactly_one(p, group_by: (x));",
            true,
            true,
            false,
        ),
        (
            "sort S; const a,b:S; relation p(x:S,y:S); p(a,a); p(a,a); obligation one: exactly_one(p, group_by: (x,y));",
            false,
            true,
            false,
        ),
    ] {
        let (results, out) = check(&format!("{body}{V}"));
        let c = results.coverage.values().next().unwrap();
        assert_eq!(
            (c.proved(), uniqueness_proved(&results), c.no_groups),
            (coverage, uniqueness, no_groups),
            "{body}"
        );
        assert_eq!(out.status["state"] == "proved", coverage && uniqueness);
        assert_eq!(
            out.diagnostics
                .iter()
                .filter(|d| d.kind == Kind::EmptyGroupingDomain)
                .count(),
            usize::from(no_groups)
        );
        // Asking about uniqueness must not silently fold in another component.
        for (obligation, domain) in &results.group_domains {
            assert_eq!(domain.kind, Cardinality::ExactlyOne);
            if domain.domains.is_empty() && domain.members.values().all(|m| m.len() <= 1) {
                assert_eq!(
                    results.group(&domain.key(obligation, vec![]).unwrap()),
                    Some(ScopedResult::Proved)
                );
            }
        }
    }
}

#[test]
fn small_world_oracle_checks_both_parts_without_assuming_either() {
    for formula in 0..4 {
        for facts in 0..4 {
            for constrained in [false, true] {
                let rules = match formula {
                    0 => "p(a) :- i(a); p(b) :- i(b);",
                    1 => "p(a) :- !i(a); p(b) :- !i(b);",
                    2 => "p(a) :- i(a), !i(b); p(b) :- i(b), !i(a);",
                    _ => "p(a) :- i(a); p(a) :- !i(b); p(b) :- i(b); p(b) :- !i(a);",
                };
                let mut text = format!(
                    "sort S; const a,b:S; input i(x:S); relation p(x:S); {rules} assumption allowed: at_most_one(i, group_by: ()); obligation one: exactly_one(p, group_by: ()); verification checks {{ assumptions: [{}]; obligations: [one]; }}",
                    if constrained { "allowed" } else { "" }
                );
                if facts & 1 != 0 {
                    text.push_str("p(a);");
                }
                if facts & 2 != 0 {
                    text.push_str("p(b);");
                }
                let count = |world: usize| {
                    (0..2)
                        .filter(|group| {
                            let own = world & (1 << group) != 0;
                            let other = world & (1 << (1 - group)) != 0;
                            facts & (1 << group) != 0
                                || match formula {
                                    0 => own,
                                    1 => !own,
                                    2 => own && !other,
                                    _ => own || !other,
                                }
                        })
                        .count()
                };
                let worlds: Vec<_> = (0..4).filter(|w| !constrained || *w != 3).collect();
                let expected_coverage = worlds.iter().all(|w| count(*w) >= 1);
                let expected_uniqueness = worlds.iter().all(|w| count(*w) <= 1);
                let p = load_text(&text);
                let mut session = Session::default();
                let (cold, out) = run(&p, &mut session, &Limits::default());
                let (warm, _) = run(&p, &mut session, &Limits::default());
                assert_eq!(cold, warm);
                let coverage = cold.coverage.values().next().unwrap();
                assert!(coverage.complete());
                assert_eq!(coverage.proved(), expected_coverage, "{text}");
                assert_eq!(uniqueness_proved(&cold), expected_uniqueness, "{text}");
                assert_eq!(
                    out.status["state"] == "proved",
                    expected_coverage && expected_uniqueness
                );
                let world = |candidate: &Candidate| {
                    candidate.present.iter().fold(0, |w, atom| {
                        w | if atom.arguments[0]
                            == *p
                                .keys
                                .constant(p.corpus.constants().find(|c| c.name == "a").unwrap().id)
                                .unwrap()
                        {
                            1
                        } else {
                            2
                        }
                    })
                };
                for example in &coverage.examples {
                    assert_eq!(count(world(&example.observation)), 0);
                }
                for g in cold.groups.values() {
                    if let ScopedResult::Counterexample(c, _) = g {
                        assert!(count(world(&c.candidate)) >= 2, "{text}: {:?}", c.candidate);
                    }
                }
                // The fresh global API also includes both components.
                let request = p
                    .verification_requests(&Limits::default())
                    .unwrap()
                    .remove(0)
                    .1;
                let ops = OperationalLimits::from(&Limits::default());
                let RequestPreparation::Complete(prepared) =
                    request.prepare(&p.corpus, &p.keys, &ops).unwrap()
                else {
                    panic!()
                };
                let prepared = prepared.admit(&ops).unwrap();
                let CheckOutcome::Complete(global) = prepared.verify(&ops).unwrap() else {
                    panic!()
                };
                assert_eq!(
                    global.verification.all_obligations_proved(),
                    expected_coverage && expected_uniqueness
                );
            }
        }
    }
}

#[test]
fn coverage_aggregates_but_uniqueness_stays_per_group_and_old_identities_stay_unchanged() {
    let p = load_text(
        "sort G; const a,b,c,d:G; sort V; const x,y:V; relation p(g:G,v:V); p(a,x); p(a,y); p(b,x); p(b,y); obligation one: exactly_one(p, group_by: (g)); obligation covered: at_least_one(p, group_by: (g)); obligation unique: at_most_one(p, group_by: (g)); verification checks { assumptions: []; obligations: [one,covered,unique]; }",
    );
    let (results, out) = run(&p, &mut Session::default(), &Limits::default());
    let findings: BTreeSet<_> = out.diagnostics.iter().map(|d| d.identity.clone()).collect();
    assert_eq!(
        findings
            .iter()
            .filter(|id| matches!(id, Identity::Coverage(_)))
            .count(),
        2
    );
    assert_eq!(
        findings
            .iter()
            .filter(|id| matches!(id, Identity::Uniqueness { .. }))
            .count(),
        2
    );
    assert_eq!(
        findings
            .iter()
            .filter(|id| matches!(id, Identity::Group { .. }))
            .count(),
        2
    );
    for id in &findings {
        let data = id.data(&p.keys).unwrap();
        match id {
            Identity::Group { .. } => assert!(data.get("component").is_none()),
            Identity::Uniqueness { .. } => assert_eq!(data["component"], "uniqueness"),
            Identity::Coverage(_) => assert_eq!(data["component"], "coverage"),
            _ => unreachable!(),
        }
    }
    for c in results.coverage.values() {
        assert_eq!(c.missing, 2);
    }
    let combined = out.status["groups"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|g| g["identity"]["component"] == "uniqueness")
        .count();
    assert_eq!(combined, 2);
    assert_eq!(
        out.diagnostics
            .iter()
            .filter(|d| matches!(d.identity, Identity::Coverage(_)))
            .count(),
        4
    );
}

#[test]
fn either_failure_survives_the_other_components_exhaustion() {
    let names = (0..100)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let text = format!(
        "sort S; const {names}:S; sort V; const x,y:V; relation p(a:S,b:S,v:V); p(a0,a0,x); p(a0,a0,y); obligation one: exactly_one(p, group_by: (a,b)); {V}"
    );
    let p = load_text(&text);
    let limits = Limits {
        max_work: 2000,
        ..Limits::default()
    };
    let mut session = Session::default();
    let (cold, out) = run(&p, &mut session, &limits);
    assert_eq!(cold, run(&p, &mut session, &limits).0);
    assert!(
        cold.coverage
            .values()
            .next()
            .unwrap()
            .inconclusive
            .is_some()
    );
    assert!(
        cold.groups
            .values()
            .any(|g| matches!(g, ScopedResult::Counterexample(..)))
    );
    assert_eq!(out.status["state"], "findings");

    let names = (0..12)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let p = load_text(&format!(
        "sort S; const {names}:S; input p(x:S); obligation one: exactly_one(p, group_by: ()); {V}"
    ));
    let limits = Limits {
        max_bdd_nodes: 16,
        ..Limits::default()
    };
    let mut session = Session::default();
    let (cold, out) = run(&p, &mut session, &limits);
    assert_eq!(cold, run(&p, &mut session, &limits).0);
    assert_eq!(cold.coverage.values().next().unwrap().missing, 1);
    assert!(
        cold.groups
            .values()
            .any(|g| matches!(g, ScopedResult::Inconclusive(_))),
        "{:?}",
        cold.groups
    );
    assert_eq!(out.status["state"], "findings");
    assert!(
        out.diagnostics
            .iter()
            .any(|d| matches!(d.identity, Identity::Uniqueness { .. })
                && d.kind == Kind::Inconclusive)
    );
}

#[test]
fn changing_kind_context_and_facts_cannot_reuse_a_combined_proof() {
    let mut session = Session::default();
    for (kind, selection, facts, proved) in [
        ("at_most_one", "allowed", "", true),
        ("exactly_one", "allowed", "", false),
        ("exactly_one", "allowed", "p(a);", true),
        ("exactly_one", "", "p(a);", false),
        ("at_least_one", "", "p(a);", true),
        ("exactly_one", "allowed", "p(a);", true),
    ] {
        let p = load_text(&format!(
            "sort S; const a,b:S; input i(x:S); relation p(x:S); p(a) :- i(a); p(b) :- i(a), i(b); {facts} assumption allowed: at_most_one(i, group_by: ()); obligation one: {kind}(p, group_by: ()); verification checks {{ assumptions: [{selection}]; obligations: [one]; }}"
        ));
        let (warm, out) = run(&p, &mut session, &Limits::default());
        assert_eq!(warm, run(&p, &mut Session::default(), &Limits::default()).0);
        assert_eq!(
            out.status["state"] == "proved",
            proved,
            "{kind} {selection} {facts}"
        );
    }
}

#[test]
fn round_trip_keeps_one_declaration_both_parts_selection_and_origins() {
    let p = load_text(&format!(
        "namespace n {{ sort S; const a,b:S; input p(x:S); obligation one: exactly_one(p, group_by: ()); {V} }}"
    ));
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
    };
    let export = ExportProgram {
        corpus: &p.corpus,
        domains: &p.domains,
        sources: &p.sources,
        provenance: &p.provenance,
        layout: &layout,
    };
    for embedded_origins in [false, true] {
        let bundle = print(&export, PrintOptions { embedded_origins }).unwrap();
        assert_eq!(
            bundle.files["program.den"].matches("obligation ").count(),
            1
        );
        assert!(bundle.files["program.den"].contains("exactly_one"));
        let (membership, documents) = bundle.documents("file:///export");
        let reloaded = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &reloaded, "file:///export", embedded_origins);
        let (results, out) = run(&reloaded, &mut Session::default(), &Limits::default());
        assert_eq!(reloaded.corpus.obligations().count(), 1);
        assert_eq!(results.coverage.values().next().unwrap().missing, 1);
        assert!(!uniqueness_proved(&results));
        assert!(
            out.diagnostics
                .iter()
                .any(|d| matches!(d.identity, Identity::Coverage(_)))
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| matches!(d.identity, Identity::Uniqueness { .. }))
        );
    }
}

#[test]
fn exactly_one_is_obligation_only_and_reuses_group_validation() {
    for declaration in [
        "assumption a: exactly_one(p, group_by: (x));",
        "obligation a: exactly_one(p, group_by: (missing));",
        "obligation a: exactly_one(p, group_by: (x,x));",
    ] {
        let source = SourceFile::new(
            "file:///invalid.den",
            1,
            format!("sort S; input p(x:S); {declaration}"),
        );
        let membership = ProgramMembership::single("root", [source.uri.clone()]);
        assert!(load(&membership, &[source.clone()]).is_err());
        let mut index = index::Index::default();
        index.update(
            source.clone(),
            parser().parse(source.text.as_ref(), None).unwrap(),
        );
        index.set_membership(&membership).unwrap();
        if declaration.starts_with("assumption") || declaration.contains("missing") {
            assert!(
                index
                    .diagnostics("root", &source.uri)
                    .iter()
                    .any(|d| !d.warning)
            );
        }
    }
}

#[test]
fn unsupported_uniqueness_does_not_erase_independently_proved_coverage() {
    let (results, out) = check(&format!(
        "sort S; const a,b:S; relation p(x:S); p(a); p(b) :- !p(b); obligation one: exactly_one(p, group_by: ()); {V}"
    ));
    assert!(results.coverage.values().next().unwrap().proved());
    assert!(
        results
            .groups
            .values()
            .any(|g| matches!(g, ScopedResult::Unsupported(_)))
    );
    assert_ne!(out.status["state"], "proved");
    assert!(
        out.diagnostics
            .iter()
            .all(|d| !matches!(d.identity, Identity::Coverage(_)))
    );
}
