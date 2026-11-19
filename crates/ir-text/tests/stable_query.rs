//! Original-program SAT query boundary, independent of ordinary admission/BDD W.
use denotate_check::{stable_query::*, *};
use denotate_ir_text::*;
fn load_text(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///stable-query.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
}
fn prepare(p: &LoadedProgram, name: &str) -> std::result::Result<Engine, CheckError> {
    let v = p.corpus.verifications().find(|v| v.name == name).unwrap();
    // Even preparation must not require BDD variables, nodes, tasks or global W.
    let l = Limits {
        max_bdd_variables: 0,
        max_bdd_nodes: 0,
        max_bdd_tasks: 0,
        ..Limits::default()
    };
    Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v.id,
        &l,
        QueryLimits::default(),
    )
}
fn atom(p: &LoadedProgram, relation: &str, args: &[&str]) -> GroundAtom {
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
fn declared_universe_and_selected_restrictions_match_all_small_worlds() {
    for kind in ["at_most_one", "exactly_one"] {
        for restriction in ["at_most_one", "at_least_one", "exactly_one", "empty"] {
            let expr = if restriction == "empty" {
                "empty(r)".into()
            } else {
                format!("{restriction}(r, group_by: ())")
            };
            let p = load_text(&format!(
                "sort S; const a,b:S; input i(x:S) {kind}(group_by: ()); relation r(x:S); r(X):-i(X); assumption selected:{expr}; verification v{{assumptions:[selected];obligations:[];}}"
            ));
            let inputs = [atom(&p, "i", &["a"]), atom(&p, "i", &["b"])];
            let mut warm = prepare(&p, "v").unwrap();
            for bits in 0u32..4 {
                let n = bits.count_ones();
                let u = if kind == "exactly_one" {
                    n == 1
                } else {
                    n <= 1
                };
                let w = match restriction {
                    "at_most_one" => n <= 1,
                    "at_least_one" => n >= 1,
                    "exactly_one" => n == 1,
                    _ => n == 0,
                };
                let q = Query {
                    pins: inputs
                        .iter()
                        .enumerate()
                        .map(|(i, a)| (a.clone(), bits & (1 << i) != 0))
                        .collect(),
                    ..Query::default()
                };
                for e in [&mut warm, &mut prepare(&p, "v").unwrap()] {
                    for world in [true, false] {
                        let result = if world { e.worlds(&q) } else { e.models(&q) }.unwrap();
                        assert_eq!(
                            matches!(result, Answer::Model(_)),
                            u && w,
                            "{kind} {restriction} {bits} {result:?}"
                        );
                    }
                }
            }
        }
    }
}
#[test]
fn fixed_tuple_multiplicity_empty_domains_and_within_are_preserved() {
    for (declarations, assumption, permitted) in [
        (
            "sort S; const a,b:S; relation r(x:S);r(a);r(b);",
            "at_most_one(r, group_by: ())",
            false,
        ),
        (
            "sort S; const a,b:S; relation r(x:S);r(a);r(b);",
            "exactly_one(r, group_by: ())",
            false,
        ),
        (
            "sort S; relation r(x:S);",
            "at_least_one(r, group_by: ())",
            false,
        ),
        (
            "sort S; relation r(x:S);",
            "at_least_one(r, group_by: (x))",
            true,
        ),
        (
            "sort S; const a,b:S; domain S=[a]; relation r(x:S);r(a);",
            "exactly_one(r, group_by: (x))",
            true,
        ),
        (
            "sort S; const a,b:S; input r(x:S) within allowed;relation allowed(x:S);allowed(a);",
            "at_least_one(r, group_by: (x))",
            false,
        ),
    ] {
        let p = load_text(&format!(
            "{declarations} assumption a:{assumption}; verification v{{assumptions:[a];obligations:[];}}"
        ));
        let mut e = prepare(&p, "v").unwrap();
        assert_eq!(
            matches!(e.worlds(&Query::default()).unwrap(), Answer::Model(_)),
            permitted,
            "{declarations} {assumption}"
        );
        assert_eq!(
            matches!(e.models(&Query::default()).unwrap(), Answer::Model(_)),
            permitted
        );
    }
}
#[test]
fn assumption_validation_uses_the_existing_ground_cone_rule() {
    let body = "sort S; const a,b:S; input present(s:S); relation guarded(s:S); guarded(a); relation gives(s:S); gives(b); relation holds(s:S); holds(X):-present(X); holds(X):-guarded(X),!supplied(X); relation supplied(s:S); supplied(X):-gives(X),!holds(X); relation broken(); broken():-!holds(a); assumption not_broken:empty(broken); verification v{assumptions:[not_broken];obligations:[];}";
    let p = load_text(body);
    let mut e = prepare(&p, "v").unwrap();
    assert!(matches!(
        e.worlds(&Query::default()).unwrap(),
        Answer::Model(_)
    ));
    let invalid = load_text(&body.replace("relation gives(s:S); gives(b);", "input gives(s:S);"));
    assert!(matches!(
        prepare(&invalid, "v"),
        Err(CheckError::InvalidAssumptionCone { .. })
    ));
}
#[test]
fn empty_candidate_groups_and_inconsistent_contexts_have_distinct_outcomes() {
    for (body, permitted) in [
        (
            "sort S; input i(x:S) exactly_one(group_by: ()); verification v{assumptions:[];obligations:[];}",
            true,
        ),
        (
            "input i();assumption yes:at_least_one(i,group_by:());assumption no:empty(i);verification v{assumptions:[yes,no];obligations:[];}",
            false,
        ),
    ] {
        let p = load_text(body);
        let mut e = prepare(&p, "v").unwrap();
        for answer in [
            e.worlds(&Query::default()).unwrap(),
            e.models(&Query::default()).unwrap(),
        ] {
            match answer {
                Answer::Model(_) => assert!(permitted),
                Answer::NoModel => assert!(!permitted),
                Answer::Inconclusive(reason) => panic!("unexpected inconclusive: {reason:?}"),
            }
        }
    }
}

#[test]
fn solver_poll_allowance_interrupts_a_real_search() {
    let text = "sort Bird;const a,b,c,d,e,f,g,h,i:Bird;sort Hole;const h1,h2,h3,h4,h5,h6,h7,h8:Hole;input placement(bird:Bird,hole:Hole) exactly_one(group_by:(bird));assumption exclusive:at_most_one(placement,group_by:(hole));verification v{assumptions:[exclusive];obligations:[];}";
    let p = load_text(text);
    let v = p.corpus.verifications().next().unwrap().id;
    let config = QueryLimits {
        max_solver_polls: 0,
        ..QueryLimits::default()
    };
    let mut e = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        config,
    )
    .unwrap();
    let Answer::Inconclusive(why) = e.worlds(&Query::default()).unwrap() else {
        panic!("search must exhaust without an unsatisfiability answer")
    };
    assert!(format!("{why:?}").contains("solver polls"));
}
