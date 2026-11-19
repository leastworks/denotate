use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;

fn load_text(text: &str) -> denotate_ir_text::Result<LoadedProgram> {
    let source = SourceFile::new("file:///input-cardinality.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
}
fn run(
    p: &LoadedProgram,
    session: &mut Session,
    masked: bool,
) -> (ScopedResults, presentation::Presentation) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let mut request = p.verification_requests(&limits).unwrap().remove(0).1;
    request.checking_within_w = masked;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let admitted = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &ops).unwrap() else {
        panic!()
    };
    let presented = presentation::present(p, &report.checked).unwrap();
    (report.checked.results.value, presented)
}
const VERIFY: &str = "verification checks { assumptions: []; obligations: [valid]; }";

#[test]
fn declarations_filter_exactly_the_legal_worlds_without_selected_assumptions() {
    for kind in ["at_most_one", "exactly_one"] {
        for grouping in ["()", "(x)"] {
            let p = load_text(&format!("sort S; const a,b:S; input i(x:S) {kind}(group_by: {grouping}); relation bad(); obligation valid: empty(bad); {VERIFY}")).unwrap();
            let limits = Limits::default();
            let request = p.verification_requests(&limits).unwrap().remove(0).1;
            let RequestPreparation::Complete(prep) = request
                .prepare(&p.corpus, &p.keys, &(&limits).into())
                .unwrap()
            else {
                panic!()
            };
            let inputs = prep.program().input_atoms().cloned().collect::<Vec<_>>();
            assert_eq!(inputs.len(), 2);
            for bits in 0usize..4 {
                let count = bits.count_ones();
                let expected = match (kind, grouping) {
                    ("at_most_one", "()") => count <= 1,
                    ("exactly_one", "()") => count == 1,
                    ("exactly_one", _) => count == 2,
                    _ => true,
                };
                let world = inputs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, a)| a.clone())
                    .collect::<Vec<_>>();
                assert_eq!(
                    prep.program().evaluate(world, &limits).is_ok(),
                    expected,
                    "{kind} {grouping} {bits}"
                );
            }
            for masked in [false, true] {
                let mut session = Session::default();
                let (cold, presentation) = run(&p, &mut session, masked);
                assert_eq!(presentation.status["state"], "proved");
                assert!(
                    presentation.status["activeAssumptions"]
                        .as_array()
                        .unwrap()
                        .is_empty()
                );
                assert_eq!(presentation.status["inputUniverse"]["state"], "nonempty");
                assert_eq!(cold, run(&p, &mut session, masked).0);
            }
        }
    }
}

#[test]
fn universe_constrains_admission_and_unknown_short_circuits() {
    let source = "sort S; const a,b:S; input i(x:S) exactly_one(group_by: ()); relation left(); relation right(); left() :- i(a), !right(); right() :- i(b), !left(); relation bad(); bad() :- left(), right(); obligation valid: empty(bad);";
    let p = load_text(&format!("{source} {VERIFY}")).unwrap();
    for masked in [false, true] {
        let (result, presented) = run(&p, &mut Session::default(), masked);
        assert!(result.regions.is_empty(), "{:?}", result.regions);
        assert_eq!(presented.status["state"], "proved");
    }
}

#[test]
fn within_domain_and_cardinality_edits_invalidate_warm_preparation() {
    let mut session = Session::default();
    for (kind, facts, domain, empty) in [
        ("exactly_one", "allowed(a);", "", false),
        ("exactly_one", "", "", false),
        ("at_most_one", "", "", false),
        ("exactly_one", "", "domain S = [];", false),
        ("exactly_one", "allowed(b);", "", false),
    ] {
        let p = load_text(&format!("sort S; const a,b:S; {domain} relation allowed(x:S); {facts} input i(x:S) within allowed {kind}(group_by: ()); relation bad(); obligation valid: empty(bad); {VERIFY}")).unwrap();
        let (warm, presented) = run(&p, &mut session, false);
        assert_eq!(warm, run(&p, &mut Session::default(), false).0);
        assert_eq!(warm.empty_input_universe, empty);
        assert!(!warm.inconsistent_assumptions);
        assert_eq!(
            presented.status["state"],
            if empty {
                "empty-input-universe"
            } else {
                "proved"
            }
        );
        assert_eq!(
            presented
                .diagnostics
                .iter()
                .any(|d| d.kind.code() == "empty-input-universe"),
            empty
        );
    }
}

#[test]
fn no_eligible_tuples_have_no_groups_even_with_empty_group_by() {
    for (group, empty) in [("(x)", false), ("()", false)] {
        let p = load_text(&format!("sort S; input i(x:S) exactly_one(group_by: {group}); relation bad(); obligation valid: empty(bad); {VERIFY}")).unwrap();
        assert_eq!(
            run(&p, &mut Session::default(), false)
                .0
                .empty_input_universe,
            empty
        );
    }
}

#[test]
fn invalid_declaration_shapes_are_rejected() {
    for text in [
        "relation r() at_most_one(group_by: ());",
        "input r() at_least_one(group_by: ());",
        "input r() at_most_one(group_by: ()) exactly_one(group_by: ());",
        "input r() exactly_one(group_by: (missing));",
        "sort S; input r(x:S) at_most_one(group_by: (x,x));",
    ] {
        assert!(load_text(text).is_err(), "{text}");
    }
}

#[test]
fn masked_admission_preserves_every_legal_stable_model() {
    use denotate_check::test_support::rewrites::{stable_models, subsets};
    use std::collections::BTreeSet;
    let bodies = [
        "i(a)",
        "i(b)",
        "!i(a)",
        "!i(b)",
        "i(a), !y()",
        "i(b), !y()",
        "!y()",
        "y()",
    ];
    for cardinality in ["at_most_one", "exactly_one"] {
        for body in bodies {
            for extra in [
                "",
                "x() :- i(a);",
                "y() :- i(b);",
                "x() :- !i(a); y() :- i(a);",
            ] {
                let p=load_text(&format!("sort S; const a,b:S; input i(v:S) {cardinality}(group_by: ()); relation x(); relation y(); x() :- {body}; y() :- !x(); {extra}")).unwrap();
                let limits = Limits::default();
                let raw = GroundProgram::prepare(&p.corpus, &p.domains, &limits).unwrap();
                let admitted = raw.clone().admit(&limits).unwrap();
                let inputs: BTreeSet<_> = raw.input_atoms().cloned().collect();
                let atoms = raw.atoms().cloned().collect::<Vec<_>>();
                let before = raw.rules().cloned().collect::<Vec<_>>();
                let after = admitted.rules().cloned().collect::<Vec<_>>();
                let meaning = admitted.symbolic(&limits).unwrap();
                for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
                    let legal =
                        world.len() <= 1 && (cardinality == "at_most_one" || world.len() == 1);
                    if !legal {
                        continue;
                    }
                    let models = stable_models(&atoms, &inputs, &before, &world);
                    assert_eq!(
                        models,
                        stable_models(&atoms, &inputs, &after, &world),
                        "{cardinality} {body} {extra}"
                    );
                    for atom in &atoms {
                        if let SymbolicFact::Settled(c) = meaning.fact(atom).unwrap() {
                            let holds = meaning
                                .context()
                                .evaluate(&c, world.iter().cloned(), &limits)
                                .unwrap();
                            assert!(
                                models.iter().all(|m| m.contains(atom) == holds),
                                "{cardinality} {body} {extra} {atom:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn named_assumptions_still_refine_the_universe_independently() {
    let p=load_text("sort S; const a,b:S; input i(x:S) exactly_one(group_by: ()); assumption none: empty(i); relation bad(); obligation valid: empty(bad); verification checks { assumptions: [none]; obligations: [valid]; }").unwrap();
    let (r, presented) = run(&p, &mut Session::default(), false);
    assert!(r.inconsistent_assumptions);
    assert!(!r.empty_input_universe);
    assert_eq!(presented.status["state"], "inconsistent-assumptions");
    assert_eq!(presented.status["inputUniverse"]["state"], "nonempty");
}

#[test]
fn witnesses_extend_independent_exactly_one_groups_and_notices_respect_u() {
    let p=load_text("sort S; const a,b:S; input i(x:S) exactly_one(group_by: ()); input j(x:S) exactly_one(group_by: ()); relation bad(); bad() :- i(a); relation some(); some() :- i(_); obligation valid: empty(bad); notice yes: varies(some); verification checks { assumptions: []; obligations: [valid]; notices: [yes]; }").unwrap();
    for masked in [false, true] {
        let (r, presented) = run(&p, &mut Session::default(), masked);
        assert_eq!(presented.status["state"], "findings");
        assert_eq!(r.emptiness.values().next().unwrap().present, 1);
        for example in &r.emptiness.values().next().unwrap().examples {
            assert_eq!(example.observation.present.len(), 2);
        }
        assert!(
            r.notices
                .values()
                .all(|n| n.state == NoticeState::AlwaysTrue)
        );
    }
}

#[test]
fn empty_candidates_do_not_enumerate_cartesian_groups_and_sat_probe_uses_u() {
    let p=load_text("sort S; const a,b,c:S; relation none(x:S,y:S); input i(x:S,y:S) within none exactly_one(group_by:(x,y)); relation bad(); obligation valid:empty(bad); verification checks{assumptions:[];obligations:[valid];}").unwrap();
    let mut limits = Limits::default();
    limits.max_atoms = 4;
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap(),
        RequestPreparation::Complete(_)
    ));
    let p=load_text("input i() exactly_one(group_by:()); relation a(); relation b(); a():-i(); a():-!b(); b():-!a(); relation bad(); obligation valid:empty(bad); verification checks{assumptions:[];obligations:[valid];}").unwrap();
    let limits = Limits::default();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prep) = request
        .prepare(&p.corpus, &p.keys, &(&limits).into())
        .unwrap()
    else {
        panic!()
    };
    let component = prep
        .program()
        .components()
        .find(|c| c.cycle.is_some())
        .unwrap();
    let report = prep
        .sat_probe(component.id, &SatProbeLimits::default(), &(&limits).into())
        .unwrap();
    assert_eq!(report.answer, SatProbeAnswer::Unsat);
    assert_eq!(
        report.existence.unwrap().answer,
        SatExistenceAnswer::EveryWorld
    );
}

#[test]
fn selected_input_uniqueness_can_conflict_with_declared_exactly_one() {
    let source = "sort S;const a,b:S; input i(x:S) exactly_one(group_by:(x)); assumption one:at_most_one(i,group_by:()); relation clear(); obligation valid:empty(clear); verification checks{assumptions:[one];obligations:[valid];}";
    let mut session = Session::default();
    for (text, inconsistent) in [
        (source.to_string(), true),
        (source.replace("[one]", "[]"), false),
        (source.to_string(), true),
    ] {
        let p = load_text(&text).unwrap();
        let (warm, presented) = run(&p, &mut session, false);
        assert_eq!(warm, run(&p, &mut Session::default(), false).0);
        assert_eq!(warm.inconsistent_assumptions, inconsistent);
        assert!(!warm.empty_input_universe);
        assert_eq!(
            presented.status["state"],
            if inconsistent {
                "inconsistent-assumptions"
            } else {
                "proved"
            }
        );
        let relation = p.corpus.relations().find(|r| r.name == "i").unwrap().id;
        let low = GroundProgram::prepare_keyed_inputs(
            &p.corpus,
            &p.keys,
            &p.domains,
            &[InputAtMostOne {
                relation,
                group_by: vec![],
            }],
            &Limits::default(),
        )
        .unwrap();
        assert!(!low.assumptions_consistent());
    }
}

fn sat(p: &LoadedProgram) -> stable_query::Engine {
    stable_query::Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        &Limits {
            max_bdd_variables: 0,
            max_bdd_nodes: 0,
            max_bdd_tasks: 0,
            ..Limits::default()
        },
        stable_query::QueryLimits::default(),
    )
    .unwrap()
}
fn ground(p: &LoadedProgram, relation: &str, args: &[&str]) -> GroundAtom {
    GroundAtom::new(
        p.corpus
            .relations()
            .find(|r| r.name == relation)
            .unwrap()
            .id,
        args.iter()
            .map(|name| p.corpus.constants().find(|c| c.name == *name).unwrap().id),
    )
}

#[test]
fn eligible_projection_matches_every_tiny_world_in_bdd_and_sat() {
    // Include an unused output sort value: no missing candidate group enters U.
    let tuples = [("a", "x"), ("a", "y"), ("b", "x"), ("b", "y")];
    for candidates in 0usize..16 {
        let facts = tuples
            .iter()
            .enumerate()
            .filter(|(i, _)| candidates & (1 << i) != 0)
            .map(|(_, (o, v))| format!("allowed({o},{v});"))
            .collect::<String>();
        for kind in ["at_most_one", "exactly_one"] {
            for group in ["()", "(output)"] {
                let p = load_text(&format!(
                    "sort O; const a,b,c:O; sort V; const x,y:V;
                    relation allowed(output:O,value:V); {facts}
                    input i(output:O,value:V) within allowed {kind}(group_by:{group});
                    relation bad(); obligation valid:empty(bad); {VERIFY}"
                ))
                .unwrap();
                let limits = Limits::default();
                let raw = GroundProgram::prepare(&p.corpus, &p.domains, &limits).unwrap();
                let mut engine = sat(&p);
                let atoms = tuples
                    .iter()
                    .map(|(o, v)| ground(&p, "i", &[o, v]))
                    .collect::<Vec<_>>();
                let masks = if group == "()" {
                    vec![candidates]
                } else {
                    vec![candidates & 3, candidates & 12]
                };
                for bits in 0usize..16 {
                    let legal = bits & !candidates == 0
                        && masks.iter().filter(|m| **m != 0).all(|m| {
                            let count = (bits & m).count_ones();
                            if kind == "exactly_one" {
                                count == 1
                            } else {
                                count <= 1
                            }
                        });
                    let world = atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| bits & (1 << i) != 0)
                        .map(|(_, a)| a.clone())
                        .collect::<Vec<_>>();
                    assert_eq!(
                        raw.evaluate(world, &limits).is_ok(),
                        legal,
                        "BDD {candidates} {kind} {group} {bits}"
                    );
                    let query = stable_query::Query {
                        pins: atoms
                            .iter()
                            .enumerate()
                            .map(|(i, a)| (a.clone(), bits & (1 << i) != 0))
                            .collect(),
                        exclude: vec![],
                    };
                    for answer in [
                        engine.worlds(&query).unwrap(),
                        engine.models(&query).unwrap(),
                    ] {
                        assert_eq!(
                            matches!(answer, stable_query::Answer::Model(_)),
                            legal,
                            "SAT {candidates} {kind} {group} {bits}: {answer:?}"
                        );
                        assert!(!matches!(answer, stable_query::Answer::Inconclusive(_)));
                    }
                }
                for masked in [false, true] {
                    let (result, presented) = run(&p, &mut Session::default(), masked);
                    assert!(!result.empty_input_universe);
                    assert_eq!(presented.status["state"], "proved");
                }
            }
        }
    }
}

#[test]
fn empty_non_grouping_domain_has_no_input_groups_but_coverage_keeps_cartesian_groups() {
    for group in ["()", "(output)"] {
        for selected in [false, true] {
            let selection = if selected { "required" } else { "" };
            let p = load_text(&format!(
                "sort O; const a:O; sort V;
                input i(output:O,value:V) exactly_one(group_by:{group});
                assumption required:at_least_one(i,group_by:{group});
                obligation coverage:at_least_one(i,group_by:{group});
                verification checks{{assumptions:[{selection}];obligations:[coverage];}}"
            ))
            .unwrap();
            for masked in [false, true] {
                let (r, _) = run(&p, &mut Session::default(), masked);
                assert!(!r.empty_input_universe);
                assert_eq!(r.inconsistent_assumptions, selected);
                if !selected {
                    assert_eq!(r.coverage.values().next().unwrap().missing, 1);
                }
            }
            let r = sat(&p)
                .check(&p.keys, &stable_query::CheckOptions::default())
                .unwrap();
            assert_eq!(
                r.context,
                if selected {
                    stable_query::Context::InconsistentAssumptions
                } else {
                    stable_query::Context::Permitted
                }
            );
            if !selected {
                assert_eq!(r.coverage.values().next().unwrap().missing, 1);
            }
        }
    }
}

#[test]
fn candidate_coverage_remains_structural_and_named_assumptions_are_not_input_declarations() {
    for kind in ["at_least_one", "exactly_one"] {
        for selection in ["", "required"] {
            let p = load_text(&format!(
                "sort O; const a,b,c:O; domain O=[a,b]; sort V;const x:V;
                relation allowed(output:O,value:V);allowed(a,x);
                input i(output:O,value:V) within allowed exactly_one(group_by:output);
                assumption required:{kind}(i,group_by:output);
                obligation candidates:{kind}(allowed,group_by:output);
                verification checks{{assumptions:[{selection}];obligations:[candidates];}}"
            ))
            .unwrap();
            let (r, _) = run(&p, &mut Session::default(), false);
            assert!(!r.empty_input_universe);
            let report = sat(&p)
                .check(&p.keys, &stable_query::CheckOptions::default())
                .unwrap();
            if selection.is_empty() {
                assert!(!r.inconsistent_assumptions);
                assert_eq!(r.coverage.values().next().unwrap().missing, 1);
                assert_eq!(report.context, stable_query::Context::Permitted);
                assert_eq!(report.coverage.values().next().unwrap().missing, 1);
            } else {
                assert!(r.inconsistent_assumptions);
                assert_eq!(
                    report.context,
                    stable_query::Context::InconsistentAssumptions
                );
            }
        }
    }
}

#[test]
fn last_candidate_edits_change_forced_values_and_agree_cold_warm_in_both_modes() {
    for masked in [false, true] {
        let mut session = Session::with_grounding();
        for facts in [
            "allowed(a);allowed(b);",
            "allowed(a);",
            "",
            "allowed(a);allowed(b);",
        ] {
            let p = load_text(&format!(
                "sort S;const a,b:S; relation allowed(x:S);{facts}
                input i(x:S) within allowed exactly_one(group_by:x);
                relation bad();bad():-i(b);obligation valid:empty(bad);{VERIFY}"
            ))
            .unwrap();
            let (warm, presented) = run(&p, &mut session, masked);
            assert_eq!(warm, run(&p, &mut Session::default(), masked).0);
            assert!(!warm.empty_input_universe);
            let count = usize::from(facts.contains("allowed(b)"));
            assert_eq!(warm.emptiness.values().next().unwrap().present, count);
            assert_eq!(
                presented.status["state"],
                if count > 0 { "findings" } else { "proved" }
            );
            let mut e = sat(&p);
            for _ in 0..2 {
                let r = e
                    .check(&p.keys, &stable_query::CheckOptions::default())
                    .unwrap();
                assert_eq!(r.context, stable_query::Context::Permitted);
                assert_eq!(r.emptiness.values().next().unwrap().present, count);
            }
        }
    }
}
