use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;

fn load_text(text: &str) -> denotate_ir_text::Result<LoadedProgram> {
    let source = SourceFile::new("file:///assumptions.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
}
fn program(text: &str) -> LoadedProgram {
    load_text(text).unwrap()
}
fn run(p: &LoadedProgram, session: &mut Session) -> (ScopedResults, presentation::Presentation) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
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
const VERIFY: &str = "verification checks { assumptions: [a]; obligations: []; }";

#[test]
fn all_forms_match_exhaustive_small_world_oracle_for_inputs_and_derived_relations() {
    for derived in [false, true] {
        for kind in ["empty", "at_most_one", "at_least_one", "exactly_one"] {
            for grouped in [false, true] {
                if kind == "empty" && grouped {
                    continue;
                }
                let relation = if derived { "r" } else { "i" };
                let grouping = if kind == "empty" {
                    ""
                } else if grouped {
                    ", group_by: (x)"
                } else {
                    ", group_by: ()"
                };
                let p = program(&format!(
                    "sort S; const x,y:S; input i(x:S); relation r(x:S); r(X) :- i(X); assumption a: {kind}({relation}{grouping}); {VERIFY}"
                ));
                let limits = Limits::default();
                let request = p.verification_requests(&limits).unwrap().remove(0).1;
                let RequestPreparation::Complete(prepared) = request
                    .prepare(&p.corpus, &p.keys, &(&limits).into())
                    .unwrap()
                else {
                    panic!()
                };
                let atoms = prepared
                    .program()
                    .input_atoms()
                    .cloned()
                    .collect::<Vec<_>>();
                assert_eq!(atoms.len(), 2);
                for mask in 0usize..4 {
                    let count = mask.count_ones();
                    let expected = match kind {
                        "empty" => count == 0,
                        "at_most_one" => grouped || count <= 1,
                        "at_least_one" => {
                            if grouped {
                                count == 2
                            } else {
                                count >= 1
                            }
                        }
                        "exactly_one" => {
                            if grouped {
                                count == 2
                            } else {
                                count == 1
                            }
                        }
                        _ => unreachable!(),
                    };
                    let world = atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, a)| a.clone())
                        .collect::<Vec<_>>();
                    assert_eq!(
                        prepared.program().evaluate(world, &limits).is_ok(),
                        expected,
                        "{kind} derived={derived} grouped={grouped} mask={mask}"
                    );
                }
                assert!(!run(&p, &mut Session::default()).0.inconsistent_assumptions);
            }
        }
    }
}
#[test]
fn inconsistent_contexts_never_prove_even_without_obligations() {
    for (kind, facts) in [
        ("empty", "r(x);"),
        ("at_most_one", "r(x); r(y);"),
        ("at_least_one", ""),
        ("exactly_one", ""),
    ] {
        for obligations in ["", "o"] {
            let grouping = if kind == "empty" {
                ""
            } else {
                ", group_by: ()"
            };
            let p = program(&format!(
                "sort S; const x,y:S; relation r(x:S); {facts} assumption a:{kind}(r{grouping}); relation q(); obligation o:empty(q); verification checks {{ assumptions:[a]; obligations:[{obligations}]; }}"
            ));
            let (result, presented) = run(&p, &mut Session::default());
            assert!(result.inconsistent_assumptions);
            let limits = Limits::default();
            let request = p.verification_requests(&limits).unwrap().remove(0).1;
            let RequestPreparation::Complete(prepared) = request
                .prepare(&p.corpus, &p.keys, &(&limits).into())
                .unwrap()
            else {
                panic!()
            };
            let meaning = prepared.program().symbolic(&limits).unwrap();
            assert!(matches!(
                meaning.check_at_most_one(&limits),
                Err(CheckError::InconsistentAssumptions)
            ));
            assert!(
                !meaning
                    .verify_at_most_one(&limits)
                    .unwrap()
                    .all_obligations_proved()
            );

            assert!(
                result.groups.is_empty()
                    && result.group_domains.is_empty()
                    && result.coverage.is_empty()
                    && result.emptiness.is_empty()
            );
            assert_eq!(presented.status["state"], "inconsistent-assumptions");
            assert!(
                presented
                    .diagnostics
                    .iter()
                    .any(|d| d.kind.code() == "inconsistent-assumptions")
            );
        }
    }
    let p = program(&format!(
        "input i(); assumption a:empty(i); assumption b:at_least_one(i,group_by:()); verification v {{ assumptions:[a,b]; obligations:[]; }}"
    ));
    assert!(run(&p, &mut Session::default()).0.inconsistent_assumptions);
}
#[test]
fn empty_grouping_domains_are_vacuous_but_global_group_is_not() {
    for (group, consistent) in [("x", true), ("", false)] {
        let p = program(&format!(
            "sort S; input i(x:S); assumption a:at_least_one(i,group_by:({group})); {VERIFY}"
        ));
        assert_eq!(
            !run(&p, &mut Session::default()).0.inconsistent_assumptions,
            consistent
        );
    }
}
#[test]
fn negated_assumptions_and_outside_inputs_survive_replay_and_coverage() {
    let p = program(
        "input i(); relation absent(); absent() :- !i(); assumption a:empty(absent); relation bad(); bad(); obligation e:empty(bad); obligation c:at_least_one(i,group_by:()); verification checks { assumptions:[a]; obligations:[e,c]; }",
    );
    let (result, _) = run(&p, &mut Session::default());
    assert!(result.coverage.values().all(|r| r.proved()));
    let e = result.emptiness.values().next().unwrap();
    assert_eq!(e.present, 1);
    assert_eq!(
        e.examples[0].observation.present.len(),
        1,
        "a constraint outside the obligation cone still controls its world"
    );
}
#[test]
fn cone_validation_is_structural_independent_and_accepts_positive_recursion() {
    for body in ["r() :- !r();", "r() :- i(), !q(); q() :- r();"] {
        let p = program(&format!(
            "input i(); relation r(); relation q(); {body} assumption a:empty(r); {VERIFY}"
        ));
        let validation =
            validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &Limits::default()).unwrap();
        assert!(
            validation
                .assumptions
                .values()
                .any(|s| matches!(s, AssumptionValidity::Invalid { .. }))
        );
        let request = p
            .verification_requests(&Limits::default())
            .unwrap()
            .remove(0)
            .1;
        assert!(matches!(
            request.prepare(
                &p.corpus,
                &p.keys,
                &OperationalLimits::from(&Limits::default())
            ),
            Err(CheckError::InvalidAssumptionCone { .. })
        ));
    }
    let p = program(&format!(
        "input i(); relation r(); relation q(); q() :- i(); q() :- r(); r() :- q(); assumption a:empty(r); {VERIFY}"
    ));
    assert!(!run(&p, &mut Session::default()).0.inconsistent_assumptions);
}
#[test]
fn warnings_are_directional_and_verification_specific() {
    let declarations = "input i(); relation premise(); premise() :- i(); relation conclusion(); conclusion() :- premise(); relation downstream(); downstream() :- conclusion(); relation sibling(); sibling() :- premise(); obligation o:empty(conclusion);";
    for (relation, warn) in [
        ("conclusion", true),
        ("downstream", true),
        ("premise", false),
        ("i", false),
        ("sibling", false),
    ] {
        let p = program(&format!(
            "{declarations} assumption a:empty({relation}); verification checks {{ assumptions:[a]; obligations:[o]; }}"
        ));
        let (_, out) = run(&p, &mut Session::default());
        assert_eq!(
            out.diagnostics
                .iter()
                .any(|d| d.kind.code() == "assumed-conclusion"),
            warn,
            "{relation}"
        );
    }
}
#[test]
fn constraint_edits_selection_and_domain_changes_agree_cold_and_warm() {
    let mut session = Session::default();
    let mut grounding = Session::with_grounding();
    for (body, selection, domain) in [
        ("i(X)", "a", "x,y"),
        ("!i(X), all(X)", "a", "x,y"),
        ("i(X)", "", "x,y"),
        ("i(X)", "a", "x"),
        ("i(X)", "a", "x,y"),
    ] {
        let p = program(&format!(
            "sort S; const x,y:S; domain S=[{domain}]; input i(x:S); relation all(x:S); all(X):-i(X); relation r(x:S); r(X):-{body}; assumption a:at_most_one(r,group_by:()); obligation o:at_most_one(i,group_by:()); verification v{{assumptions:[{selection}];obligations:[o];}}"
        ));
        let (warm, wp) = run(&p, &mut session);
        let (cold, cp) = run(&p, &mut Session::default());
        assert_eq!(warm, cold);
        assert_eq!(wp.status, cp.status);
        let (grounded, gp) = run(&p, &mut grounding);
        assert_eq!(grounded, cold);
        assert_eq!(gp.status, cp.status);
    }
}
#[test]
fn exhaustion_and_cancellation_do_not_become_inconsistency() {
    let p = program(&format!(
        "input i(); assumption a:at_least_one(i,group_by:()); {VERIFY}"
    ));
    let limits = Limits {
        max_bdd_variables: 0,
        ..Limits::default()
    };
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap(),
        RequestPreparation::Inconclusive { .. }
    ));
    let ops = OperationalLimits::from(&Limits::default());
    ops.cancellation.cancel();
    assert!(matches!(
        request.prepare(&p.corpus, &p.keys, &ops),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn selection_controls_admission_rewrites_no_meaning_and_certification() {
    let mut session = Session::default();
    for select in ["a", "", "a"] {
        let p = program(&format!(
            "sort S; const x,y:S; input i(x:S); relation allowed(x:S); allowed(X):-i(X); assumption a:at_most_one(allowed,group_by:()); relation p(); relation q(); p():-i(x),!q(); q():-i(y),!p(); p():-!i(y); verification v{{assumptions:[{select}];obligations:[];}}"
        ));
        let (result, out) = run(&p, &mut session);
        assert_eq!(result.regions.is_empty(), !select.is_empty());
        if !select.is_empty() {
            assert!(out.diagnostics.iter().any(|d| d.kind.code() == "redundant"));
        }
        let limits = Limits::default();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) = request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap()
        else {
            panic!()
        };
        let world = prepared
            .program()
            .input_atoms()
            .cloned()
            .collect::<Vec<_>>();
        if !select.is_empty() {
            assert!(
                prepared
                    .program()
                    .certify_observation(world, &limits)
                    .is_err()
            );
        }
        let p = program(&format!(
            "sort S; const x,y:S; input i(x:S); relation forbidden(); forbidden():-i(x),i(y); assumption a:empty(forbidden); relation paradox(); paradox():-forbidden(),!paradox(); verification v{{assumptions:[{select}];obligations:[];}}"
        ));
        let (_, out) = run(&p, &mut session);
        assert_eq!(
            out.diagnostics
                .iter()
                .any(|d| d.kind.code() == "no-meaning"),
            select.is_empty()
        );
    }
}
#[test]
fn large_missing_group_space_exhausts_explicitly() {
    let p = program(&format!(
        "sort S; const x,y,z:S; relation r(x:S,y:S); assumption a:at_least_one(r,group_by:(x,y)); {VERIFY}"
    ));
    let limits = Limits {
        max_atoms: 2,
        ..Limits::default()
    };
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    assert!(matches!(
        request
            .prepare(&p.corpus, &p.keys, &(&limits).into())
            .unwrap(),
        RequestPreparation::Inconclusive { .. }
    ));
}

#[test]
fn library_contracts_use_each_consumers_metadata() {
    use std::collections::{BTreeMap, BTreeSet};
    let lib = "namespace lib { input left(); input right(); relation disjoint(); relation forbidden(); forbidden():-disjoint(),left(),right(); assumption a:empty(forbidden); sort S; const x,y:S; relation result(x:S); result(x):-left(); result(y):-right(); obligation unique:at_most_one(result,group_by:()); verification v{assumptions:[a];obligations:[unique];} }";
    let documents = [
        SourceFile::new("lib.den", 1, lib),
        SourceFile::new("a.den", 1, "lib::disjoint();"),
        SourceFile::new("b.den", 1, "// no contract metadata"),
    ];
    let roots = BTreeMap::from([
        (
            "library".into(),
            RootInfo {
                files: BTreeSet::from(["lib.den".into()]),
                libraries: BTreeSet::new(),
            },
        ),
        (
            "a".into(),
            RootInfo {
                files: BTreeSet::from(["a.den".into()]),
                libraries: BTreeSet::from(["library".into()]),
            },
        ),
        (
            "b".into(),
            RootInfo {
                files: BTreeSet::from(["b.den".into()]),
                libraries: BTreeSet::from(["library".into()]),
            },
        ),
    ]);
    let mut session = Session::with_grounding();
    for root in ["a", "b", "a"] {
        let p = load(
            &ProgramMembership {
                root: root.into(),
                roots: roots.clone(),
            },
            &documents,
        )
        .unwrap();
        let (result, _) = run(&p, &mut session);
        assert_eq!(
            result
                .groups
                .values()
                .all(|r| matches!(r, ScopedResult::Proved)),
            root == "a"
        );
        assert_eq!(result, run(&p, &mut Session::default()).0);
    }
}
