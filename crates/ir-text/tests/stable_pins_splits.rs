use denotate_check::{stable_query::*, *};
use denotate_ir_text::*;

fn load_text(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///pins.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
}
fn engine(p: &LoadedProgram, v: &str, q: QueryLimits) -> Engine {
    Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().find(|x| x.name == v).unwrap().id,
        &Limits::default(),
        q,
    )
    .unwrap()
}
fn atom(p: &LoadedProgram, r: &str, args: &[&str]) -> GroundAtom {
    GroundAtom::new(
        p.corpus.relations().find(|x| x.name == r).unwrap().id,
        args.iter()
            .map(|x| p.corpus.constants().find(|c| &c.name == x).unwrap().id),
    )
}
fn no_splits() -> CheckOptions {
    CheckOptions {
        splits: SplitOptions {
            max_candidates: 0,
            ..Default::default()
        },
        ..Default::default()
    }
}
const SHARED: &str = "sort M;const a,b:M;input phase(m:M) exactly_one(group_by:());
    relation p();relation q();p():-phase(a),!q();q():-phase(b),p();
    relation chosen();chosen():-phase(a);
    assumption selected:at_least_one(chosen,group_by:());
    assumption other:empty(chosen);
    obligation clean:empty(q);
    verification v {assumptions:[];obligations:[clean];}
    verification a_only {assumptions:[selected];obligations:[clean];}
    verification b_only {assumptions:[other];obligations:[clean];}";

#[test]
fn forced_inputs_fold_shared_cycle_and_are_verification_local() {
    let p = load_text(SHARED);
    for (v, known) in [
        ("a_only", Some(true)),
        ("b_only", Some(false)),
        ("v", None),
        ("a_only", Some(true)),
    ] {
        let mut warm = engine(&p, v, QueryLimits::default());
        for e in [&mut warm, &mut engine(&p, v, QueryLimits::default())] {
            for _ in 0..2 {
                assert_eq!(e.prepared_value(&atom(&p, "p", &[])).unwrap(), known);
                assert_eq!(
                    e.negative_components(&p.keys, &Limits::default())
                        .unwrap()
                        .total,
                    usize::from(known.is_none())
                );
                if let Some(value) = known {
                    assert_eq!(e.input_pins().get(&atom(&p, "phase", &["a"])), Some(&value));
                    let mut opts = no_splits();
                    opts.max_worlds = 0;
                    let r = e.check(&p.keys, &opts).unwrap();
                    assert!(r.proved(), "{r:?}");
                    assert!(r.meaning.as_ref().unwrap().existence_stats.is_none());
                    let Answer::Model(m) = e.models(&Query::default()).unwrap() else {
                        panic!()
                    };
                    assert_eq!(m.value(&atom(&p, "p", &[])), Some(value));
                    assert!(matches!(
                        e.models(&Query {
                            pins: vec![(atom(&p, "p", &[]), !value)],
                            exclude: vec![]
                        })
                        .unwrap(),
                        Answer::NoModel
                    ));
                } else {
                    assert!(e.input_pins().is_empty());
                }
            }
        }
    }
    let mut raw = engine(
        &p,
        "a_only",
        QueryLimits {
            max_pin_candidates: 0,
            ..Default::default()
        },
    );
    assert_eq!(
        raw.negative_components(&p.keys, &Limits::default())
            .unwrap()
            .total,
        1
    );
    assert!(raw.check(&p.keys, &no_splits()).unwrap().proved());
}

#[test]
fn pin_proofs_use_worlds_not_program_models_and_handle_unknown_or_inconsistent_w() {
    let p = load_text(
        "input flag();relation p();p():-flag(),!p();verification v{assumptions:[];obligations:[];}",
    );
    for q in [
        QueryLimits::default(),
        QueryLimits {
            max_pin_work: 0,
            ..Default::default()
        },
    ] {
        let mut e = engine(&p, "v", q);
        assert!(e.input_pins().is_empty());
        let r = e.check(&p.keys, &no_splits()).unwrap();
        let Existence::NoMeaning(w) = &r.meaning.unwrap().existence else {
            panic!()
        };
        assert!(w.present.contains(&atom(&p, "flag", &[])));
    }
    let p = load_text(
        "input flag();assumption yes:at_least_one(flag,group_by:());assumption no:empty(flag);
        relation p();p():-flag(),!p();verification v{assumptions:[yes,no];obligations:[];}",
    );
    let mut e = engine(&p, "v", QueryLimits::default());
    assert!(e.input_pins().is_empty());
    assert_eq!(
        e.check(&p.keys, &CheckOptions::default()).unwrap().context,
        Context::InconsistentAssumptions
    );
    // A positive recursive assumption must be reduct-validated: completion could
    // invent loop=true with flag=false and lose this legitimate forced input.
    let p=load_text("input flag();relation loop();loop():-loop();loop():-flag();
        assumption yes:at_least_one(loop,group_by:());verification v{assumptions:[yes];obligations:[];}");
    let e = engine(&p, "v", QueryLimits::default());
    assert_eq!(e.input_pins().get(&atom(&p, "flag", &[])), Some(&true));
}

#[test]
fn splits_prove_shared_cycle_by_stratification_and_do_not_change_property_queries() {
    let p = load_text(SHARED);
    let mut warm = engine(&p, "v", QueryLimits::default());
    for e in [&mut warm, &mut engine(&p, "v", QueryLimits::default())] {
        for _ in 0..2 {
            let mut options = CheckOptions::default();
            options.max_worlds = 0;
            let r = e.check(&p.keys, &options).unwrap();
            assert!(r.proved(), "{r:?}");
            let split = r.meaning.as_ref().unwrap().split.as_ref().unwrap();
            assert!(split.branches.iter().all(|b| b.stratified));
            let summary = denotate_presentation::stable_summary(&p.corpus, &p.keys, &r).unwrap();
            assert!(summary["meaning"]["split"].is_object());
            for name in ["a", "b"] {
                let Answer::Model(m) = e
                    .models(&Query {
                        pins: vec![(atom(&p, "phase", &[name]), true)],
                        exclude: vec![],
                    })
                    .unwrap()
                else {
                    panic!()
                };
                assert_eq!(m.value(&atom(&p, "p", &[])), Some(name == "a"));
            }
            let r = e.check(&p.keys, &no_splits()).unwrap();
            assert!(r.proved());
            assert!(r.meaning.unwrap().split.is_none());
        }
    }
}

#[test]
fn failing_branch_keeps_its_world_and_unknown_branches_never_prove_meaning() {
    let p = load_text(&format!("{SHARED} relation bad();bad():-phase(a),!bad();"));
    let mut e = engine(&p, "v", QueryLimits::default());
    let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
    let m = r.meaning.unwrap();
    let Existence::NoMeaning(w) = m.existence else {
        panic!("{m:?}")
    };
    assert!(w.present.contains(&atom(&p, "phase", &["a"])));
    assert!(
        m.split
            .unwrap()
            .branches
            .iter()
            .any(|b| b.existence == "no-meaning")
    );
    let mut limited = CheckOptions::default();
    limited.max_worlds = 0;
    let r = e.check(&p.keys, &limited).unwrap();
    assert!(!r.proved());
    assert!(matches!(
        r.meaning.unwrap().existence,
        Existence::Inconclusive(_)
    ));
}

#[test]
fn split_hints_ranking_limits_and_empty_branches_are_advisory() {
    let p = load_text(&format!("{SHARED} input irrelevant();"));
    let mut e = engine(&p, "v", QueryLimits::default());
    for max_work in [0, 1_000_000] {
        let opts = CheckOptions {
            splits: SplitOptions {
                max_work,
                ..Default::default()
            },
            ..Default::default()
        };
        assert!(e.check(&p.keys, &opts).unwrap().proved());
    }
    let mut opts = CheckOptions::default();
    opts.splits.relation = Some(atom(&p, "phase", &["a"]).relation);
    assert!(e.check(&p.keys, &opts).unwrap().proved());
    opts.splits.relation = Some(atom(&p, "irrelevant", &[]).relation);
    assert!(e.check(&p.keys, &opts).is_err());
    // Disable global pin discovery to exercise an unreachable arm explicitly.
    let mut e = engine(
        &p,
        "a_only",
        QueryLimits {
            max_pin_candidates: 0,
            ..Default::default()
        },
    );
    let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
    assert!(r.proved());
    assert!(
        r.meaning
            .unwrap()
            .split
            .unwrap()
            .branches
            .iter()
            .any(|b| b.existence == "empty-context")
    );
}

#[test]
fn pinned_counterexamples_cite_original_producers_and_folding_reaches_the_plan() {
    let p = load_text(&SHARED.replace("obligation clean:empty(q)", "obligation clean:empty(p)"));
    let r = engine(&p, "a_only", QueryLimits::default())
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    let example = &r.emptiness.values().next().unwrap().examples[0];
    assert!(matches!(
        example.attribution,
        Some(Attribution::Complete(_))
    ));
    assert!(
        example
            .observation
            .present
            .contains(&atom(&p, "phase", &["a"]))
    );
    let v = p
        .corpus
        .verifications()
        .find(|v| v.name == "a_only")
        .unwrap()
        .id;
    let mut planner = denotate_plan::Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap();
    let output = denotate_plan::Output {
        atom: atom(&p, "p", &[]),
        priority: 0,
    };
    let mut options = denotate_plan::Options::default();
    options.meaning.max_worlds = 0;
    options.meaning.splits.max_candidates = 0;
    assert!(matches!(
        planner.build(&[output], &options).unwrap(),
        denotate_plan::Build::Ready(_)
    ));
}

#[test]
fn split_failure_survives_an_inconclusive_sibling() {
    let p = load_text(
        "sort M;const a,b:M;input phase(m:M) exactly_one(group_by:());input flag();
        relation bad();bad():-phase(a),!bad();
        relation p();relation q();p():-phase(b),flag(),!q();q():-phase(b),!flag(),!p();
        verification v{assumptions:[];obligations:[];}",
    );
    let mut options = CheckOptions::default();
    options.max_worlds = 1;
    let m = engine(&p, "v", QueryLimits::default())
        .check(&p.keys, &options)
        .unwrap()
        .meaning
        .unwrap();
    assert!(matches!(m.existence, Existence::NoMeaning(_)), "{m:?}");
    let branches = &m.split.as_ref().unwrap().branches;
    assert!(branches.iter().any(|b| b.existence == "no-meaning"));
    assert!(branches.iter().any(|b| b.existence == "inconclusive"));
}

#[test]
fn only_exactly_one_input_groups_cover_every_world() {
    for (cardinality, relation, extra) in [
        ("at_most_one", "phase", ""),
        ("at_least_one", "phase", ""),
        (
            "exactly_one",
            "copied",
            "relation copied(m:M);copied(X):-phase(X);",
        ),
    ] {
        let source=SHARED.replace("input phase(m:M) exactly_one(group_by:());",
            &format!("input phase(m:M);{extra} assumption selected_group:{cardinality}({relation},group_by:());"))
            .replace("assumptions:[]", "assumptions:[selected_group]");
        let p = load_text(&source);
        let r = engine(&p, "v", QueryLimits::default())
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        assert!(r.meaning.unwrap().split.is_none());
    }
}

#[test]
fn pins_and_splits_agree_with_exhaustive_stable_models() {
    // Independent reduct oracle: p,q,r,c = 0..4; exactly-one inputs x,y = 4,5.
    let templates = vec![
        (0, vec![(4, true), (1, false)]),
        (1, vec![(5, true), (0, true)]),
        (0, vec![(1, false)]),
        (1, vec![(0, false)]),
        (2, vec![(0, true)]),
        (2, vec![(1, true)]),
        (3, vec![(2, true), (3, false)]),
        (2, vec![(3, true)]),
    ];
    let names = ["p()", "q()", "r()", "c()", "phase(a)", "phase(b)"];
    for chosen in 0usize..256 {
        let rules: Vec<_> = templates
            .iter()
            .enumerate()
            .filter(|(i, _)| chosen & (1 << i) != 0)
            .map(|(_, r)| r)
            .collect();
        for selected in [None, Some(false), Some(true)] {
            let mut exists = true;
            let mut unique = true;
            let mut present = false;
            for input in [false, true]
                .into_iter()
                .filter(|i| selected.is_none_or(|s| s == *i))
            {
                let inputs = if input { 16 } else { 32 };
                let mut count = 0;
                for interpretation in 0usize..16 {
                    let candidate = interpretation | inputs;
                    let mut least = inputs;
                    loop {
                        let before = least;
                        for (head, body) in &rules {
                            if body.iter().all(|(a, pos)| {
                                if *pos {
                                    least & (1 << a) != 0
                                } else {
                                    candidate & (1 << a) == 0
                                }
                            }) {
                                least |= 1 << head;
                            }
                        }
                        if least == before {
                            break;
                        }
                    }
                    if least == candidate {
                        count += 1;
                        present |= candidate & 4 != 0;
                    }
                }
                exists &= count > 0;
                unique &= count <= 1;
            }
            let mut text="sort S;const a,b:S;input phase(s:S) exactly_one(group_by:());relation p();relation q();relation r();relation c();".to_string();
            for (head, body) in &rules {
                text.push_str(&format!(
                    "{}:-{};",
                    names[*head],
                    body.iter()
                        .map(|(a, pos)| format!("{}{}", if *pos { "" } else { "!" }, names[*a]))
                        .collect::<Vec<_>>()
                        .join(",")
                ));
            }
            text.push_str("relation chosen();chosen():-phase(a);assumption yes:at_least_one(chosen,group_by:());assumption no:empty(chosen);obligation clean:empty(r);");
            text.push_str(&format!(
                "verification v{{assumptions:[{}];obligations:[clean];}}",
                match selected {
                    None => "",
                    Some(true) => "yes",
                    Some(false) => "no",
                }
            ));
            let p = load_text(&text);
            for enabled in [false, true] {
                let mut e = engine(
                    &p,
                    "v",
                    QueryLimits {
                        max_pin_candidates: if enabled { 256 } else { 0 },
                        ..Default::default()
                    },
                );
                let opts = if enabled {
                    CheckOptions::default()
                } else {
                    no_splits()
                };
                let r = e.check(&p.keys, &opts).unwrap();
                let m = r.meaning.as_ref().unwrap();
                assert_eq!(
                    matches!(m.existence, Existence::EveryWorld),
                    exists,
                    "{enabled}: {text}: {m:?}"
                );
                assert_eq!(
                    matches!(m.existence, Existence::NoMeaning(_)),
                    !exists,
                    "{text}"
                );
                assert_eq!(
                    matches!(m.uniqueness, Uniqueness::AtMostOne),
                    unique,
                    "{text}: {m:?}"
                );
                assert_eq!(
                    matches!(m.uniqueness, Uniqueness::Multiple { .. }),
                    !unique,
                    "{text}"
                );
                // Fixed findings intentionally remain visible even with no models.
                if exists {
                    assert_eq!(r.has_failures(), present, "{text}");
                }
            }
        }
    }
}

#[test]
fn ranking_prefers_the_group_that_breaks_the_cycle_over_an_earlier_irrelevant_split() {
    let p=load_text("sort S;const a,b:S;input alpha(s:S) exactly_one(group_by:());input beta(s:S) exactly_one(group_by:());
        relation p();relation q();p():-beta(a),alpha(a),!q();p():-beta(a),alpha(b),!q();q():-beta(b),p();
        verification v{assumptions:[];obligations:[];}");
    let mut e = engine(&p, "v", QueryLimits::default());
    let mut options = CheckOptions::default();
    options.max_worlds = 0;
    let r = e.check(&p.keys, &options).unwrap();
    assert!(r.proved(), "{r:?}");
    assert!(
        r.meaning
            .unwrap()
            .split
            .unwrap()
            .group
            .iter()
            .all(|a| a.relation == atom(&p, "beta", &["a"]).relation)
    );
    options.max_worlds = 1024;
    options.splits.relation = Some(atom(&p, "alpha", &["a"]).relation);
    assert!(e.check(&p.keys, &options).unwrap().proved());
}

#[test]
fn splitting_respects_obligation_scope_and_does_not_reintroduce_outside_cycles() {
    let p = load_text(&format!(
        "{SHARED} relation outside();outside():-!outside();"
    ));
    let v = p.corpus.verifications().find(|v| v.name == "v").unwrap().id;
    let mut e = Engine::prepare_scoped(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
        PreparationScope::ObligationCones,
    )
    .unwrap();
    let r = e
        .check(
            &p.keys,
            &CheckOptions {
                meaning: MeaningMode::Cone,
                max_worlds: 0,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(r.proved(), "{r:?}");
    let m = r.meaning.unwrap();
    assert!(matches!(m.uniqueness, Uniqueness::NotAnalysed));
    assert!(m.split.is_some());
    assert!(matches!(
        engine(&p, "v", QueryLimits::default())
            .meaning(&CheckOptions::default())
            .unwrap()
            .existence,
        Existence::NoMeaning(_)
    ));
}

#[test]
fn optional_pin_work_cutoffs_do_not_poison_the_published_engine() {
    let p = load_text(SHARED);
    for max_pin_work in [0, 1, 4, 16, 64] {
        let mut e = engine(
            &p,
            "a_only",
            QueryLimits {
                max_pin_work,
                ..Default::default()
            },
        );
        assert!(e.check(&p.keys, &no_splits()).unwrap().proved());
        let Answer::Model(m) = e.models(&Query::default()).unwrap() else {
            panic!()
        };
        assert_eq!(m.value(&atom(&p, "p", &[])), Some(true));
    }
}
