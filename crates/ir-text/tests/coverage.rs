use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::top_level;
use denotate_ir_text::*;
use denotate_presentation::{Identity, Kind};
mod support;

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn run(
    p: &LoadedProgram,
    session: &mut Session,
    limits: &Limits,
) -> (ScopedResults, presentation::Presentation) {
    let operations = OperationalLimits::from(limits);
    let request = p.verification_requests(limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = session
        .prepare(&request, &p.corpus, &p.keys, &operations)
        .unwrap()
    else {
        panic!("preparation incomplete");
    };
    let prepared = prepared.admit(&operations).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &operations).unwrap()
    else {
        panic!("verification incomplete");
    };
    let output = presentation::present(p, &report.checked).unwrap();
    (report.checked.results.value, output)
}
fn coverage(text: &str) -> (CoverageResult, presentation::Presentation) {
    let p = load_text(text);
    let (result, out) = run(&p, &mut Session::default(), &Limits::default());
    (result.coverage.into_values().next().unwrap(), out)
}
const V: &str = "verification checks { assumptions: []; obligations: [covered]; }";
#[test]
fn resolved_domains_empty_domains_global_and_zero_arity() {
    {
        for (body, missing, no_groups) in [
            (
                "sort S; const a,b:S; relation p(x:S); p(a); obligation covered: at_least_one(p, group_by: (x));",
                1,
                false,
            ),
            (
                "sort S; const a,b:S; domain S=[a]; relation p(x:S); p(a); obligation covered: at_least_one(p, group_by: (x));",
                0,
                false,
            ),
            (
                "sort S; const a,b:S; domain S=[]; relation p(x:S); obligation covered: at_least_one(p, group_by: (x));",
                0,
                true,
            ),
            (
                "sort S; const a,b:S; domain S=[]; relation p(x:S); obligation covered: at_least_one(p, group_by: ());",
                1,
                false,
            ),
            (
                "relation p(); obligation covered: at_least_one(p, group_by: ());",
                1,
                false,
            ),
            (
                "relation p(); p(); p(); obligation covered: at_least_one(p, group_by: ());",
                0,
                false,
            ),
            (
                "sort S; const a,b:S; sort T; relation p(x:S,y:T); obligation covered: at_least_one(p, group_by: (x));",
                2,
                false,
            ),
            (
                "sort S; const a,b:S; relation p(x:S,y:S); p(a,a); p(a,a); obligation covered: at_least_one(p, group_by: (x,y));",
                3,
                false,
            ),
        ] {
            let (result, out) = coverage(&format!("{body}{V}"));
            assert_eq!(
                (result.missing, result.no_groups, result.complete()),
                (missing, no_groups, true),
                "{body}: {result:?}"
            );
            let notes = out
                .diagnostics
                .iter()
                .filter(|d| d.kind == Kind::EmptyGroupingDomain)
                .collect::<Vec<_>>();
            assert_eq!(notes.len(), usize::from(no_groups));
            if no_groups {
                assert!(
                    notes[0]
                        .message
                        .contains("no groups: the grouping domain is empty")
                );
                assert_eq!(out.status["state"], "proved");
            }
            let failures = out
                .diagnostics
                .iter()
                .filter(|d| d.kind == Kind::Counterexample)
                .collect::<Vec<_>>();
            assert_eq!(failures.len(), usize::from(missing > 0));
            if missing > 0 {
                assert!(matches!(failures[0].identity, Identity::Coverage(_)));
            }
        }
    }
}

#[test]
fn small_world_oracle_and_replayed_absence_agree_with_bdd() {
    // Independently evaluate four Boolean rule forms, not checker-derived expectations.
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
                    "sort S; const a,b:S; input i(x:S); relation p(x:S); {rules} assumption allowed: at_most_one(i, group_by: ()); obligation covered: at_least_one(p, group_by: (x)); verification checks {{ assumptions: [{}]; obligations: [covered]; }}",
                    if constrained { "allowed" } else { "" }
                );
                if facts & 1 != 0 {
                    text.push_str("p(a);");
                }
                if facts & 2 != 0 {
                    text.push_str("p(b);");
                }
                let expected = (0..2)
                    .filter(|&group| {
                        (0..4).any(|world| {
                            if constrained && world == 3 {
                                return false;
                            }
                            let own = world & (1 << group) != 0;
                            let other = world & (1 << (1 - group)) != 0;
                            let produced = match formula {
                                0 => own,
                                1 => !own,
                                2 => own && !other,
                                _ => own || !other,
                            };
                            !produced && facts & (1 << group) == 0
                        })
                    })
                    .count();
                let p = load_text(&text);
                {
                    let mut session = Session::default();
                    let (cold, _) = run(&p, &mut session, &Limits::default());
                    let (warm, _) = run(&p, &mut session, &Limits::default());
                    assert_eq!(cold.coverage, warm.coverage);
                    let result = cold.coverage.values().next().unwrap();
                    assert_eq!(result.missing, expected, "{text}");
                    assert!(result.complete());
                    // Replay through the public prepared request so W is validated too.
                    let request = p
                        .verification_requests(&Limits::default())
                        .unwrap()
                        .remove(0)
                        .1;
                    let RequestPreparation::Complete(prepared) = request
                        .prepare(&p.corpus, &p.keys, &(&Limits::default()).into())
                        .unwrap()
                    else {
                        panic!()
                    };
                    let prepared = prepared.admit(&(&Limits::default()).into()).unwrap();
                    let relation = p.corpus.relations().find(|r| r.name == "p").unwrap().id;
                    for example in &result.examples {
                        let present = prepared
                            .program()
                            .input_atoms()
                            .filter(|atom| {
                                example
                                    .observation
                                    .present
                                    .contains(&AtomKey::from_atom(&p.keys, atom).unwrap())
                            })
                            .cloned()
                            .collect::<Vec<_>>();
                        let replay = prepared
                            .program()
                            .evaluate(present, &Limits::default())
                            .unwrap();
                        let constant = p
                            .corpus
                            .constants()
                            .find(|c| p.keys.constant(c.id).unwrap() == &example.group[0])
                            .unwrap()
                            .id;
                        assert!(matches!(
                            replay.fact(&GroundAtom::new(relation, [constant])).unwrap(),
                            FactState::Settled(false)
                        ));
                    }
                }
            }
        }
    }
}

#[test]
fn blocked_worlds_do_not_become_absence_and_independent_producers_can_cover() {
    {
        let (blocked, _) = coverage(&format!(
            "relation p(); p() :- !p(); obligation covered: at_least_one(p, group_by: ()); {V}"
        ));
        assert_eq!(blocked.missing, 0);
        assert!(!blocked.complete());
        assert!(blocked.unsupported > 0);
        let (mixed, out) = coverage(&format!(
            "input i(); relation p(); relation q(); p() :- !q(), !i(); q() :- !p(), !i(); obligation covered: at_least_one(p, group_by: ()); {V}"
        ));
        assert_eq!(mixed.missing, 1);
        assert!(!mixed.complete());
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.kind == Kind::Counterexample)
        );
        let (covered, _) = coverage(&format!(
            "sort S; const a,b:S; relation p(x:S); p(a); p(b) :- !p(b); obligation covered: at_least_one(p, group_by: ()); {V}"
        ));
        assert!(covered.proved());
    }
}

#[test]
fn bounded_enumeration_preserves_failure_and_aggregates_with_stable_identity() {
    let names = (0..100)
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let text = format!(
        "sort S; const {names}:S; relation p(x:S,y:S); obligation covered: at_least_one(p, group_by: (x,y)); {V}"
    );
    let p = load_text(&text);
    let limits = Limits {
        max_work: 2000,
        ..Limits::default()
    };
    {
        let mut session = Session::default();
        let (cold, out) = run(&p, &mut session, &limits);
        let (warm, _) = run(&p, &mut session, &limits);
        assert_eq!(cold.coverage, warm.coverage);
        let c = cold.coverage.values().next().unwrap();
        assert!(c.missing > 0 && c.missing < 10000);
        assert!(c.inconclusive.is_some());
        assert!(!c.complete());
        assert!(c.examples.len() <= 3);
        assert_eq!(out.diagnostics.len(), 1);
        assert!(out.diagnostics[0].message.contains("at least"));
        assert_eq!(out.status["state"], "findings");
        assert_eq!(out.diagnostics[0].evidence["missingGroups"]["exact"], false);
    }
}

#[test]
fn coverage_round_trip_preserves_kind_selection_and_origins() {
    let p = load_text(&format!(
        "namespace n {{ sort S; const a,b:S; input p(x:S); obligation covered: at_least_one(p, group_by: (x)); {V} }}"
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
        let (membership, documents) = bundle.documents("file:///export");
        let reloaded = load_with_resolver(&membership, &documents, Some(&mut &p.sources)).unwrap();
        support::compare(&export, &reloaded, "file:///export", embedded_origins);
        let (a, _) = run(&p, &mut Session::default(), &Limits::default());
        let (b, _) = run(&reloaded, &mut Session::default(), &Limits::default());
        assert_eq!(
            a.coverage.values().next().unwrap().missing,
            b.coverage.values().next().unwrap().missing
        );
    }
}

#[test]
fn sessions_refresh_domains_facts_and_selected_assumptions_without_changing_identity() {
    {
        let mut session = Session::default();
        let mut finding = None;
        for (facts, domain, missing) in [
            ("p(a);", "", 1),
            ("p(b);", "", 1),
            ("p(a);p(b);", "", 0),
            ("p(a);", "domain S=[a];", 0),
            ("", "domain S=[];", 0),
        ] {
            let p = load_text(&format!(
                "sort S; const a,b:S; relation p(x:S); {facts} {domain} obligation covered: at_least_one(p, group_by: (x)); {V}"
            ));
            let (warm, out) = run(&p, &mut session, &Limits::default());
            let (cold, _) = run(&p, &mut Session::default(), &Limits::default());
            assert_eq!(cold.coverage, warm.coverage);
            assert_eq!(warm.coverage.values().next().unwrap().missing, missing);
            if missing > 0 {
                let identity = out.diagnostics[0]
                    .identity
                    .data_in(&p.keys, warm.context.verification.as_ref())
                    .unwrap();
                if let Some(old) = &finding {
                    assert_eq!(old, &identity);
                } else {
                    finding = Some(identity);
                }
            }
        }
        for (selection, missing) in [("", 1), ("allowed", 0), ("", 1)] {
            let p = load_text(&format!(
                "sort S; const a,b:S; input i(x:S); relation p(); p() :- !i(a); p() :- !i(b); assumption allowed: at_most_one(i, group_by: ()); obligation covered: at_least_one(p, group_by: ()); verification checks {{ assumptions: [{selection}]; obligations: [covered]; }}"
            ));
            let (result, _) = run(&p, &mut session, &Limits::default());
            assert_eq!(result.coverage.values().next().unwrap().missing, missing);
        }
    }
}

#[test]
fn coverage_is_obligation_only_and_grouping_validation_is_shared() {
    for declaration in [
        "assumption a: at_least_one(p, group_by: (x));",
        "obligation a: at_least_one(p, group_by: (missing));",
        "obligation a: at_least_one(p, group_by: (x,x));",
    ] {
        let source = SourceFile::new(
            "file:///program.den",
            1,
            format!("sort S; input p(x:S); {declaration}"),
        );
        let membership = ProgramMembership::single("root", [source.uri.clone()]);
        assert!(load(&membership, &[source.clone()]).is_err());
        let tree = parser().parse(source.text.as_ref(), None).unwrap();
        let mut index = index::Index::default();
        index.update(source.clone(), tree);
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
fn included_coverage_uses_each_consumers_facts_domains_and_context_identity() {
    use std::collections::{BTreeMap, BTreeSet};
    let source = "namespace lib; sort S; const a,b:S; relation p(x:S); obligation covered: at_least_one(p, group_by: (x)); verification checks { assumptions: []; obligations: [covered]; }";
    for kind in ["at_least_one", "exactly_one"] {
        let library = source.replace("at_least_one", kind);
        let roots = BTreeMap::from([
            (
                "lib".into(),
                RootInfo {
                    files: BTreeSet::from(["file:///lib.den".into()]),
                    libraries: BTreeSet::new(),
                },
            ),
            (
                "app".into(),
                RootInfo {
                    files: BTreeSet::from(["file:///app.den".into()]),
                    libraries: BTreeSet::from(["lib".into()]),
                },
            ),
        ]);
        for (root, app, missing) in [
            ("lib", "", 2),
            ("app", "lib::p(lib::a);", 1),
            ("app", "domain lib::S=[lib::a]; lib::p(lib::a);", 0),
        ] {
            let documents = if root == "lib" {
                vec![SourceFile::new("file:///lib.den", 1, library.as_str())]
            } else {
                vec![
                    SourceFile::new("file:///lib.den", 1, library.as_str()),
                    SourceFile::new("file:///app.den", 1, app),
                ]
            };
            let p = load(
                &ProgramMembership {
                    root: root.into(),
                    roots: roots.clone(),
                },
                &documents,
            )
            .unwrap();
            let (result, out) = run(&p, &mut Session::default(), &Limits::default());
            assert_eq!(result.coverage.values().next().unwrap().missing, missing);
            if missing > 0 {
                assert_eq!(out.diagnostics.len(), 1);
                let data = out.diagnostics[0].data(&p.keys).unwrap();
                assert_eq!(data["program"], root);
                assert_eq!(
                    data["finding"]["verification"],
                    serde_json::json!(["lib", "checks"])
                );
                assert_eq!(out.diagnostics[0].fallback, root == "app");
            }
        }
    }
}
