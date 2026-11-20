//! Whole-program SAT meaning and emptiness, with no BDD preparation/admission.
use denotate_check::{stable_query::*, *};
use denotate_ir_text::*;
use denotate_presentation::{Identity, Kind};

fn load_text(text: &str) -> LoadedProgram {
    let f = SourceFile::new("file:///stable-checks.den", 0, text);
    load(&ProgramMembership::single("root", [f.uri.clone()]), &[f]).unwrap()
}
fn prepare(p: &LoadedProgram, name: &str) -> Engine {
    let v = p.corpus.verifications().find(|v| v.name == name).unwrap();
    let limits = Limits {
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
        &limits,
        QueryLimits::default(),
    )
    .unwrap()
}
fn atom(p: &LoadedProgram, name: &str, args: &[&str]) -> GroundAtom {
    GroundAtom::new(
        p.corpus.relations().find(|r| r.name == name).unwrap().id,
        args.iter()
            .map(|s| p.corpus.constants().find(|c| c.name == *s).unwrap().id),
    )
}
fn empty(r: &Report) -> &EmptinessReport {
    assert_eq!(r.emptiness.len(), 1);
    r.emptiness.values().next().unwrap()
}
const V: &str = "verification v { assumptions: []; obligations: [clean]; }";

#[test]
fn no_violation_does_not_hide_a_world_with_no_meaning() {
    let p = load_text(&format!(
        "input flag(); relation p(); p():-flag(),!p();
        relation violation(); violation():-flag(),!p(); obligation clean:empty(violation); {V}"
    ));
    let mut e = prepare(&p, "v");
    for _ in 0..2 {
        let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
        assert!(empty(&r).proved()); // property alone, not the verification
        assert!(!r.proved());
        let m = r.meaning.unwrap();
        let Existence::NoMeaning(w) = m.existence else {
            panic!("{m:?}")
        };
        assert!(w.present.contains(&atom(&p, "flag", &[])));
        assert!(matches!(m.uniqueness, Uniqueness::AtMostOne));
        assert!(matches!(
            e.worlds(&Query {
                pins: vec![(atom(&p, "flag", &[]), true)],
                ..Query::default()
            })
            .unwrap(),
            Answer::Model(_)
        ));
    }
}

#[test]
fn multiple_meanings_and_failures_have_their_own_confirmed_models() {
    for target in ["violation", "a"] {
        let p = load_text(&format!(
            "relation a(); relation b(); a():-!b(); b():-!a();
            relation violation(); violation():-a(),b(); obligation clean:empty({target}); {V}"
        ));
        let r = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        assert_eq!(r.has_failures(), target == "a");
        assert!(!r.proved());
        if target == "a" {
            let x = &empty(&r).examples[0];
            assert_eq!(x.tuple, atom(&p, "a", &[]));
            let Some(Attribution::Complete(proof)) = &x.attribution else {
                panic!("{x:?}")
            };
            assert!(proof.contains_key(&x.tuple));
        }
        let m = r.meaning.unwrap();
        assert!(matches!(m.existence, Existence::EveryWorld));
        let Uniqueness::Multiple {
            observation,
            first,
            second,
        } = m.uniqueness
        else {
            panic!("{m:?}")
        };
        assert!(observation.present.is_empty() && observation.absent.is_empty());
        let a = atom(&p, "a", &[]);
        let b = atom(&p, "b", &[]);
        assert_ne!(first.value(&a), second.value(&a));
        for model in [first, second] {
            assert_ne!(model.value(&a), model.value(&b));
        }
    }
}

#[test]
fn no_meaning_and_multiple_meanings_can_coexist_in_different_worlds() {
    let p = load_text(
        "input flag(); relation p(); p():-flag(),!p();
        relation a(); relation b(); a():-!flag(),!b(); b():-!flag(),!a();
        verification v {assumptions:[];obligations:[];}",
    );
    let r = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    let m = r.meaning.unwrap();
    let Existence::NoMeaning(ref w) = m.existence else {
        panic!("{m:?}")
    };
    assert!(w.present.contains(&atom(&p, "flag", &[])));
    let Uniqueness::Multiple { observation, .. } = m.uniqueness else {
        panic!("{m:?}")
    };
    assert!(observation.absent.contains(&atom(&p, "flag", &[])));
}

const TUPLES: &str = "sort S; const z,a,m,b,k:S;
    input i(x:S) at_most_one(group_by:()); relation r(x:S); r(X):-i(X);
    obligation clean:empty(r); verification v{assumptions:[];obligations:[clean];}";

#[test]
fn distinct_tuples_keep_their_own_worlds_and_deterministic_sample() {
    let p = load_text(TUPLES);
    let mut warm = prepare(&p, "v");
    let mut baseline = None;
    for examples in [
        EmptinessExamples::default(),
        EmptinessExamples::All,
        EmptinessExamples::Limited(1.try_into().unwrap()),
        EmptinessExamples::default(),
    ] {
        let options = CheckOptions {
            examples,
            ..CheckOptions::default()
        };
        for e in [&mut warm, &mut prepare(&p, "v")] {
            let r = e.check(&p.keys, &options).unwrap();
            assert_eq!(r.context, Context::Permitted);
            assert!(r.meaning.as_ref().unwrap().unique_everywhere());
            let v = empty(&r);
            assert!(v.complete());
            assert_eq!(v.present, 5);
            let mut keys = Vec::new();
            for ex in &v.examples {
                let input =
                    GroundAtom::new(atom(&p, "i", &["a"]).relation, ex.tuple.arguments.clone());
                assert_eq!(ex.observation.present, [input.clone()].into());
                assert_eq!(ex.observation.absent.len(), 4);
                assert_eq!(ex.replay_scope, ReplayScope::WholeProgram);
                assert!(
                    matches!(&ex.attribution,Some(Attribution::Complete(proof)) if proof.contains_key(&ex.tuple) && proof.contains_key(&input))
                );
                assert_eq!(
                    ex.dependency_inputs,
                    Some(Attribution::Complete([input].into()))
                );
                keys.push(AtomKey::from_atom(&p.keys, &ex.tuple).unwrap());
            }
            assert!(keys.windows(2).all(|w| w[0] < w[1]));
            if examples == EmptinessExamples::default() {
                assert_eq!(keys.len(), 3);
                if let Some(expected) = &baseline {
                    assert_eq!(&keys, expected)
                } else {
                    baseline = Some(keys)
                }
            }
        }
    }
}

#[test]
fn tuple_exhaustion_keeps_a_lower_bound_and_exclusions_do_not_leak() {
    let p = load_text(TUPLES);
    let mut e = prepare(&p, "v");
    for cap in [0, 2, 100] {
        let r = e
            .check(
                &p.keys,
                &CheckOptions {
                    max_tuples: cap,
                    ..CheckOptions::default()
                },
            )
            .unwrap();
        assert_eq!(empty(&r).present, cap.min(5));
        assert_eq!(empty(&r).complete(), cap >= 5);
        assert_eq!(r.has_failures(), cap > 0);
        let (id, v) = r.emptiness.iter().next().unwrap();
        let f = denotate_presentation::emptiness_finding(&p.corpus, *id, v, &|_| String::new())
            .unwrap()
            .unwrap();
        assert_eq!(f.identity, Identity::Emptiness(*id));
        assert_eq!(
            f.kind,
            if cap == 0 {
                Kind::Inconclusive
            } else {
                Kind::Counterexample
            }
        );
        if cap == 2 {
            assert!(f.message.contains("at least 2"));
        }
    }
}

#[test]
fn confirmed_failure_survives_meaning_exhaustion_and_attribution_exhaustion() {
    let p = load_text(&format!(
        "relation a(); relation b(); a():-!b(); b():-!a();
        relation bad(); bad(); obligation clean:empty(bad); {V}"
    ));
    let r = prepare(&p, "v")
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 0,
                attribution: Limits {
                    max_work: 0,
                    ..Limits::default()
                },
                ..CheckOptions::default()
            },
        )
        .unwrap();
    assert!(r.has_failures());
    assert!(empty(&r).complete());
    assert_eq!(empty(&r).present, 1);
    assert!(matches!(
        empty(&r).examples[0].attribution,
        Some(Attribution::Incomplete(_))
    ));
    assert!(matches!(
        r.meaning.as_ref().unwrap().existence,
        Existence::Inconclusive(_)
    ));
    assert!(matches!(
        r.meaning.as_ref().unwrap().uniqueness,
        Uniqueness::Multiple { .. }
    ));
}

#[test]
fn empty_candidate_groups_inconsistent_selection_and_unanalysed_checks_are_distinct() {
    for (prefix, assumptions, expected) in [
        (
            "sort S; input x(s:S) exactly_one(group_by:());",
            "",
            Context::Permitted,
        ),
        (
            "input x(); assumption a:at_least_one(x,group_by:()); assumption b:empty(x);",
            "a,b",
            Context::InconsistentAssumptions,
        ),
    ] {
        let p = load_text(&format!(
            "{prefix} relation r(); obligation clean:empty(r);
            verification v{{assumptions:[{assumptions}];obligations:[clean];}}"
        ));
        let r = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        assert_eq!(r.context, expected);
        if expected == Context::Permitted {
            assert!(r.proved());
            assert!(r.meaning.is_some());
            assert!(r.not_analysed.is_empty());
        } else {
            assert!(r.meaning.is_none());
            assert!(!r.proved());
            assert!(r.emptiness.is_empty());
            assert_eq!(r.not_analysed.len(), 1);
        }
    }
    let p = load_text(
        "input x(); relation r(); obligation clean:empty(r);
        obligation one:at_most_one(x,group_by:()); obligation two:at_least_one(x,group_by:());
        obligation three:exactly_one(x,group_by:()); notice n:varies(x);
        verification v{assumptions:[];obligations:[clean,one,two,three];notices:[n];}",
    );
    let r = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(empty(&r).proved());
    assert!(!r.proved());
    assert_eq!(r.not_analysed.len(), 2);
    assert_eq!(r.notices_not_analysed.len(), 1);
}

#[test]
fn self_support_does_not_lose_a_violation_or_leak_assumption_selection() {
    let p = load_text(
        "input flag(); relation p(); p():-flag(); p():-p();
        assumption a:at_least_one(p,group_by:()); relation bad(); bad():-!flag();
        obligation clean:empty(bad);
        verification yes{assumptions:[a];obligations:[clean];}
        verification free{assumptions:[];obligations:[clean];}",
    );
    for name in ["yes", "free", "yes"] {
        let mut e = prepare(&p, name);
        for _ in 0..2 {
            let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
            assert_eq!(r.has_failures(), name == "free");
            assert_eq!(r.proved(), name == "yes");
        }
    }
    let p = load_text(&format!(
        "input flag(); relation p(); p():-flag(),p();
        relation bad(); bad():-flag(); obligation clean:empty(bad); {V}"
    ));
    let r = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(r.has_failures());
    assert!(r.meaning.unwrap().unique_everywhere());
}

#[test]
fn shared_emptiness_presentation_agrees_with_bdd_on_matching_scopes() {
    for source in [
        TUPLES,
        "relation r(); r(); obligation clean:empty(r); verification v{assumptions:[];obligations:[clean];}",
        "relation r(); obligation clean:empty(r); verification v{assumptions:[];obligations:[clean];}",
    ] {
        let p = load_text(source);
        let sat = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        let limits = Limits::default();
        let ops = OperationalLimits::from(&limits);
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let admitted = prepared.admit(&ops).unwrap();
        let CheckOutcome::Complete(bdd) = admitted.verify(&ops).unwrap() else {
            panic!()
        };
        assert_eq!(sat.proved(), bdd.verification.all_obligations_proved());
        let names = |_| String::new();
        let bdd_findings =
            denotate_presentation::interpret(&p.corpus, &bdd.verification, &names).unwrap();
        let own = p.documents.iter().map(|d| d.uri.clone()).collect();
        let key = p.keys.verification(sat.verification).unwrap();
        let placement = denotate_presentation::Placement {
            program: &p.root,
            verification: Some(key),
            user_files: &own,
            sources: &p.sources,
            current: &p.provenance,
            upstream: &p.embedded.provenance,
        };
        for (id, result) in &sat.emptiness {
            let sf =
                denotate_presentation::emptiness_finding(&p.corpus, *id, result, &names).unwrap();
            let bf = bdd_findings
                .iter()
                .find(|f| f.identity == Identity::Emptiness(*id));
            assert_eq!(sf.is_some(), bf.is_some());
            if let (Some(s), Some(b)) = (sf, bf) {
                assert_eq!(s.kind, b.kind);
                assert_eq!(s.message, b.message);
                assert_eq!(s.placement_groups.len(), b.placement_groups.len());
                assert!(s.placement_groups.iter().all(|g| g.derivation.is_some()));
                let sd = placement.finding(&s).unwrap();
                let bd = placement.finding(b).unwrap();
                assert_eq!(
                    sd.iter()
                        .map(|d| (&d.primary, &d.identity))
                        .collect::<Vec<_>>(),
                    bd.iter()
                        .map(|d| (&d.primary, &d.identity))
                        .collect::<Vec<_>>()
                );
                for d in sd {
                    assert_eq!(d.data(&p.keys).unwrap()["kind"], "counterexample");
                }
            }
        }
    }
}

#[test]
fn attribution_allowances_are_independent_per_tuple() {
    let mut source = String::from("sort S;const a,b:S;relation r(x:S);r(a);relation c0();c0();");
    for i in 1..20 {
        source.push_str(&format!("relation c{i}();c{i}():-c{}();", i - 1));
    }
    source.push_str(&format!("r(b):-c19();obligation clean:empty(r);{V}"));
    let p = load_text(&source);
    let mut e = prepare(&p, "v");
    let mut mixed = false;
    for max_work in [0, 16, 64, 256, 1024, 4096] {
        let r = e
            .check(
                &p.keys,
                &CheckOptions {
                    attribution: Limits {
                        max_work,
                        ..Limits::default()
                    },
                    ..CheckOptions::default()
                },
            )
            .unwrap();
        let v = empty(&r);
        assert!(v.complete());
        assert_eq!(v.present, 2);
        let good = v
            .examples
            .iter()
            .filter(|x| matches!(x.attribution, Some(Attribution::Complete(_))))
            .count();
        mixed |= good == 1;
    }
    assert!(
        mixed,
        "one expensive attribution must not exhaust another tuple's allowance"
    );
}

#[test]
fn existence_covers_irrelevant_inputs_and_stratification_needs_no_world_search() {
    let mut source = String::new();
    for i in 0..20 {
        source.push_str(&format!("input i{i}();"));
    }
    source.push_str("relation a();relation b();a():-!b();b():-!a();verification v{assumptions:[];obligations:[];}");
    let p = load_text(&source);
    let r = prepare(&p, "v")
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 1,
                ..CheckOptions::default()
            },
        )
        .unwrap();
    assert!(matches!(
        r.meaning.unwrap().existence,
        Existence::EveryWorld
    ));
    let p = load_text(
        "input seed();relation p();p():-seed();p():-p();verification v{assumptions:[];obligations:[];}",
    );
    let r = prepare(&p, "v")
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 0,
                ..CheckOptions::default()
            },
        )
        .unwrap();
    assert!(r.proved());
}

#[test]
fn uniqueness_groups_respect_assumptions_and_do_not_leak_between_queries() {
    let p=load_text("sort K;const a,b:K;sort V;const x,y:V;input i(k:K,v:V);
        relation r(k:K,v:V);r(K,V):-i(K,V);assumption single:at_most_one(i,group_by:(k));
        obligation one:at_most_one(r,group_by:(k));
        verification yes{assumptions:[single];obligations:[one];}verification free{assumptions:[];obligations:[one];}");
    for name in ["yes", "free", "yes"] {
        let mut e = prepare(&p, name);
        for _ in 0..2 {
            let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
            assert_eq!(r.proved(), name == "yes");
            assert_eq!(r.groups.len(), 2);
            for g in &r.groups {
                match &g.outcome {
                    VerifiedOutcome::Proved => assert_eq!(name, "yes"),
                    VerifiedOutcome::Counterexample(c) => {
                        assert_eq!(name, "free");
                        assert_eq!(c.tuples.len(), 2);
                        for a in &c.tuples {
                            assert_eq!(&a.arguments[..1], g.group.key.as_slice());
                            assert!(c.evidence.contains_key(a));
                        }
                    }
                    other => panic!("{other:?}"),
                }
            }
            let output = presentation::present_stable(&p, &r).unwrap();
            assert_eq!(
                output.status["state"],
                if name == "yes" { "proved" } else { "findings" }
            );
        }
    }
}
#[test]
fn structural_cardinalities_use_resolved_domains_and_survive_unrelated_no_meaning() {
    let p=load_text("sort S;const a,b:S;domain S=[a];relation r(x:S);r(a);
        relation bad();bad():-!bad();obligation e:empty(r);obligation u:at_most_one(r,group_by:());obligation c:at_least_one(r,group_by:(x));obligation x:exactly_one(r,group_by:());
        verification v{assumptions:[];obligations:[e,u,c,x];}");
    let r = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(r.not_analysed.is_empty());
    assert_eq!(r.fixed_obligations.len(), 4);
    assert!(r.has_failures());
    assert!(r.coverage.values().all(CoverageReport::proved));
    assert!(matches!(
        r.meaning.as_ref().unwrap().existence,
        Existence::NoMeaning(_)
    ));
    for source in [
        "sort S;relation r(x:S);obligation c:at_least_one(r,group_by:(x));verification v{assumptions:[];obligations:[c];}",
        "sort S;relation r(x:S);obligation c:at_least_one(r,group_by:());verification v{assumptions:[];obligations:[c];}",
    ] {
        let p = load_text(source);
        let r = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        let c = r.coverage.values().next().unwrap();
        assert_eq!(c.no_groups, c.missing == 0);
        assert!(presentation::present_stable(&p, &r).is_ok());
    }
}
#[test]
fn uniqueness_attribution_exhaustion_keeps_failure_and_falls_back() {
    let p = load_text(
        "sort S;const a,b:S;input i(x:S);relation r(x:S);r(X):-i(X);obligation u:at_most_one(r,group_by:());verification v{assumptions:[];obligations:[u];}",
    );
    let r = prepare(&p, "v")
        .check(
            &p.keys,
            &CheckOptions {
                attribution: Limits {
                    max_work: 0,
                    ..Limits::default()
                },
                ..CheckOptions::default()
            },
        )
        .unwrap();
    let output = presentation::present_stable(&p, &r).unwrap();
    assert!(r.has_failures());
    assert_eq!(output.status["state"], "findings");
    assert!(
        output
            .diagnostics
            .iter()
            .any(|d| d.notes.iter().any(|n| n.contains("Source attribution")))
    );
    assert!(
        output.status["findings"][0]["evidence"]["incompleteAttribution"]
            .as_array()
            .unwrap()
            .len()
            >= 2
    );
}

#[test]
fn uniqueness_queries_and_shared_evidence_agree_with_bdd_on_unique_meanings() {
    for rules in [
        "r(a);r(b);r(c);",
        "r(X):-i(X);",
        "r(a):-i(a);r(b):-r(a);r(a):-r(b);r(c):-i(c);",
    ] {
        let p = load_text(&format!(
            "sort S;const a,b,c:S;input i(x:S);relation r(x:S);{rules} obligation u:at_most_one(r,group_by:());verification v{{assumptions:[];obligations:[u];}}"
        ));
        let sat = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        assert!(sat.has_failures());
        for g in &sat.groups {
            if let VerifiedOutcome::Counterexample(c) = &g.outcome {
                for step in c.evidence.values() {
                    if let GroundEvidence::Derived { premises, .. } = &step.evidence {
                        for premise in premises {
                            if let PremiseEvidence::Positive { fact, .. } = premise {
                                assert!(c.evidence[fact].order < step.order);
                            }
                        }
                    }
                }
            }
        }
        let l = Limits::default();
        let ops = OperationalLimits::from(&l);
        let req = p.verification_requests(&l).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) = req.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let admitted = prepared.admit(&ops).unwrap();
        let CheckOutcome::Complete(bdd) = admitted.verify(&ops).unwrap() else {
            panic!()
        };
        let names = presentation::diagnostic_names(&p.corpus);
        let sf = denotate_presentation::stable_findings(&p.corpus, &sat, &names).unwrap();
        let bf = denotate_presentation::interpret(&p.corpus, &bdd.verification, &names).unwrap();
        assert_eq!(sf.len(), bf.len());
        assert_eq!(sf[0].identity, bf[0].identity);
        assert_eq!(sf[0].kind, bf[0].kind);
        if !rules.contains("i(") {
            assert_eq!(sf[0].message, bf[0].message);
        }
    }
}

#[test]
fn oracle_respects_input_universe_and_returns_runtime_evaluable_expressions() {
    let p = load_text(
        "sort S; const a,b,c:S; domain S=[a,b,c];
        relation eligible(s:S); eligible(a); eligible(b);
        input value(s:S) within eligible exactly_one(group_by:());
        relation selected(); selected():-value(b);
        verification v{assumptions:[];obligations:[];}",
    );
    let mut e = prepare(&p, "v"); // BDD variables, tasks and nodes all zero.
    let a = atom(&p, "value", &["a"]);
    let b = atom(&p, "value", &["b"]);
    let c = atom(&p, "value", &["c"]);
    let target = atom(&p, "selected", &[]);
    let q = Query::default();
    let l = OracleLimits::default();
    assert!(matches!(
        e.constant(&q, &c, &l).unwrap(),
        ConstantAnswer::Constant(false)
    ));
    let SynthesisAnswer::Expression(expr) = e.synthesize(&q, &target, &[a.clone()], &l).unwrap()
    else {
        panic!()
    };
    assert_eq!(
        expr.dependencies().unwrap(),
        std::collections::BTreeSet::from([a.clone()])
    );
    assert_eq!(expr.evaluate(|_| Some(true)), Some(false));
    assert_eq!(expr.evaluate(|_| Some(false)), Some(true));
    assert!(matches!(
        e.equivalent(&q, &target, &[a.clone()], &expr, &l).unwrap(),
        EquivalenceAnswer::Equivalent
    ));
    let impossible = Query {
        pins: vec![(a, true), (b, true)],
        exclude: vec![],
    };
    assert!(matches!(e.feasible(&impossible).unwrap(), Answer::NoModel));
}
#[test]
fn oracle_results_do_not_replace_verification_meaning_or_property_checks() {
    let p = load_text(
        "input a(); input b(); relation x(); x():-a(),!b();
        relation p(); relation q(); p():-!q(); q():-!p();
        obligation clean:empty(x);
        verification v{assumptions:[];obligations:[clean];}",
    );
    let mut warm = prepare(&p, "v");
    let target = atom(&p, "x", &[]);
    let k = [atom(&p, "a", &[]), atom(&p, "b", &[])];
    let l = OracleLimits::default();
    let SynthesisAnswer::Expression(expr) =
        warm.synthesize(&Query::default(), &target, &k, &l).unwrap()
    else {
        panic!()
    };
    assert!(matches!(
        warm.equivalent(&Query::default(), &target, &k, &expr, &l)
            .unwrap(),
        EquivalenceAnswer::Equivalent
    ));
    for mut e in [warm, prepare(&p, "v")] {
        let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
        assert!(!r.proved());
        assert_eq!(empty(&r).present, 1);
        assert!(empty(&r).complete());
        assert!(matches!(
            r.meaning.unwrap().uniqueness,
            Uniqueness::Multiple { .. }
        ));
    }
}

#[test]
fn meaning_modes_are_explicit_and_do_not_change_property_checks_or_reused_answers() {
    for rules in [
        "relation a(); relation b(); a():-!b(); b():-!a();",
        "relation a(); a():-!a();",
        "relation a(); a():-a();", // completion truth is not stable truth
    ] {
        let p = load_text(&format!(
            "{rules} relation bad(); bad(); obligation clean:empty(bad); {V}"
        ));
        let mut warm = prepare(&p, "v");
        for mode in [
            MeaningMode::Full,
            MeaningMode::None,
            MeaningMode::Uniqueness,
            MeaningMode::Full,
        ] {
            let options = CheckOptions {
                meaning: mode,
                ..Default::default()
            };
            let r = warm.check(&p.keys, &options).unwrap();
            let fresh = prepare(&p, "v").check(&p.keys, &options).unwrap();
            assert!(r.has_failures());
            assert!(!r.proved());
            let summary = denotate_presentation::stable_summary(&p.corpus, &p.keys, &r).unwrap();
            let fresh_summary =
                denotate_presentation::stable_summary(&p.corpus, &p.keys, &fresh).unwrap();
            // Witnesses and accumulated solver work are not goldens.
            assert_eq!(summary["state"], fresh_summary["state"]);
            assert_eq!(summary["obligations"], fresh_summary["obligations"]);
            for phase in ["existence", "uniqueness"] {
                assert_eq!(
                    summary["meaning"][phase]["state"],
                    fresh_summary["meaning"][phase]["state"]
                );
            }
            assert_eq!(summary["meaning"]["mode"], mode.label());
            if mode != MeaningMode::Full {
                assert_eq!(summary["state"], "incomplete");
                assert_eq!(summary["meaning"]["existence"]["state"], "not-analysed");
                assert_eq!(
                    summary["meaning"]["existence"]["reason"],
                    "disabled-by-option"
                );
                assert!(r.meaning.as_ref().unwrap().existence_stats.is_none());
            }
            if mode == MeaningMode::None {
                assert_eq!(summary["meaning"]["uniqueness"]["state"], "not-analysed");
            }
        }
    }
    let p = load_text(&format!(
        "relation p();p():-p();obligation clean:empty(p);{V}"
    ));
    let r = prepare(&p, "v")
        .check(
            &p.keys,
            &CheckOptions {
                meaning: MeaningMode::None,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(empty(&r).proved());
    assert!(!r.proved());
}

#[test]
fn component_existence_uses_local_meaning_not_whole_program_uniqueness() {
    let pair = "relation a(); relation b(); a():-!b(); b():-!a();";
    for (tail, exists, multiple, fallback) in [
        ("relation r(); r():-a();", true, true, false),
        ("relation c(); c():-a(),!c();", true, false, true),
        (
            "relation c(); c():-a(),!c(); relation d(); d():-b(),!d();",
            false,
            false,
            true,
        ),
    ] {
        let p = load_text(&format!(
            "{pair} {tail} verification v {{ assumptions: []; obligations: []; }}"
        ));
        let mut warm = prepare(&p, "v");
        for e in [&mut warm, &mut prepare(&p, "v")] {
            for _ in 0..2 {
                let m = e
                    .check(&p.keys, &CheckOptions::default())
                    .unwrap()
                    .meaning
                    .unwrap();
                assert_eq!(
                    matches!(m.existence, Existence::EveryWorld),
                    exists,
                    "{m:?}"
                );
                assert_eq!(matches!(m.existence, Existence::NoMeaning(_)), !exists);
                assert_eq!(
                    matches!(m.uniqueness, Uniqueness::Multiple { .. }),
                    multiple
                );
                let uniqueness_stats = m.uniqueness_stats.as_ref().unwrap();
                assert_eq!(uniqueness_stats.scope, "downstream-cone");
                assert!(uniqueness_stats.fallback_reason.is_none());
                assert_eq!(m.existence_stats.unwrap().fallback.is_some(), fallback);
            }
        }
    }
}

#[test]
fn component_cover_never_hides_an_independent_no_meaning_world() {
    let p = load_text(
        "input flag(); relation a(); relation b(); a():-!b(); b():-!a();
        relation bad(); bad():-flag(),!bad(); verification v { assumptions: []; obligations: []; }",
    );
    let mut e = prepare(&p, "v");
    for _ in 0..2 {
        let m = e
            .check(&p.keys, &CheckOptions::default())
            .unwrap()
            .meaning
            .unwrap();
        let Existence::NoMeaning(w) = m.existence else {
            panic!("{m:?}")
        };
        assert!(w.present.contains(&atom(&p, "flag", &[])));
        assert!(matches!(m.uniqueness, Uniqueness::Multiple { .. }));
        // A zero-input cube for a/b must not remove this world from bad's search.
        assert!(m.existence_stats.unwrap().fallback.is_none());
    }
}

#[test]
fn cone_uniqueness_can_establish_eligibility_for_a_reader() {
    let p = load_text(
        "input flag(); relation a(); relation b(); a():-flag(); a():-!flag();
        a():-!b(); b():-!a(); relation c(); c():-a(),!c();
        verification v { assumptions: []; obligations: []; }",
    );
    let m = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap()
        .meaning
        .unwrap();
    assert!(matches!(m.existence, Existence::NoMeaning(_)));
    let s = m.existence_stats.unwrap();
    assert!(s.fallback.is_none());
    assert!(s.scopes.iter().any(|s| s.state == "determined"));
}

#[test]
fn cone_support_excludes_unrelated_inputs_but_worlds_keep_cross_boundary_groups() {
    let p = load_text(
        "sort S; const a,b,c,d: S; input x(s:S);
        relation p(); relation q(); p():-x(a); p():-!q(); q():-!p();
        relation copied(s:S); copied(X):-x(X);
        assumption one: exactly_one(x, group_by: ());
        verification v { assumptions: [one]; obligations: []; }",
    );
    let mut e = prepare(&p, "v");
    for _ in 0..2 {
        let m = e
            .check(&p.keys, &CheckOptions::default())
            .unwrap()
            .meaning
            .unwrap();
        assert!(matches!(m.existence, Existence::EveryWorld));
        assert!(matches!(m.uniqueness, Uniqueness::Multiple { .. }));
        let s = m.existence_stats.unwrap();
        assert_eq!(s.support_size, 4);
        assert_eq!(s.scopes.len(), 1);
        assert_eq!(s.scopes[0].counters.support_size, 1);
        assert!(s.scopes[0].counters.max_inputs <= 1);
    }
}

#[test]
fn scoped_queries_validate_positive_recursive_assumption_definitions() {
    // Completion alone lets loop() invent truth and would admit flag=false.
    // The reduct oracle for W must reject that fabricated permitted world.
    let p = load_text(
        "input flag(); relation loop(); loop():-loop(); loop():-flag();
        assumption selected: at_least_one(loop, group_by: ());
        relation a(); relation b(); a():-flag(); a():-!b(); b():-!a();
        verification v { assumptions: [selected]; obligations: []; }",
    );
    let mut e = prepare(&p, "v");
    for _ in 0..2 {
        let m = e
            .check(&p.keys, &CheckOptions::default())
            .unwrap()
            .meaning
            .unwrap();
        assert!(m.unique_everywhere(), "{m:?}");
        assert_eq!(m.existence_stats.unwrap().scopes[0].state, "determined");
    }
}

#[test]
fn component_exhaustion_keeps_fixed_failures_and_has_no_reusable_partial_cover() {
    let p = load_text(
        "input x(); relation a(); relation b(); a():-x(),!b(); b():-!x(),!a();
        relation bad(); bad(); obligation clean:empty(bad);
        verification v { assumptions: []; obligations: [clean]; }",
    );
    let mut e = prepare(&p, "v");
    let limited = e
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 1,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(limited.has_failures());
    let m = limited.meaning.unwrap();
    assert!(matches!(m.existence, Existence::Inconclusive(_)));
    let stats = m.existence_stats.unwrap();
    assert!(stats.cubes > 0);
    assert_eq!(stats.scopes.last().unwrap().state, "inconclusive");
    for _ in 0..2 {
        let full = e.check(&p.keys, &CheckOptions::default()).unwrap();
        assert!(full.has_failures());
        assert!(full.meaning.unwrap().unique_everywhere());
    }
    assert!(
        prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap()
            .meaning
            .unwrap()
            .unique_everywhere()
    );
}

#[test]
fn scoped_global_uniqueness_ignores_512_unrelated_positive_pairs() {
    let mut text = String::from(
        "input flag(); relation a(); relation b(); a():-flag(); a():-!b(); b():-!a();\n",
    );
    for i in 0..512 {
        text.push_str(&format!("input x{i}(); relation y{i}(); y{i}():-x{i}();\n"));
    }
    text.push_str("verification v { assumptions: []; obligations: []; }");
    let p = load_text(&text);
    let mut warm = prepare(&p, "v");
    for e in [&mut warm, &mut prepare(&p, "v")] {
        for mode in [
            MeaningMode::Full,
            MeaningMode::Uniqueness,
            MeaningMode::Full,
        ] {
            let m = e
                .check(
                    &p.keys,
                    &CheckOptions {
                        meaning: mode,
                        ..Default::default()
                    },
                )
                .unwrap()
                .meaning
                .unwrap();
            if mode == MeaningMode::Full {
                assert!(matches!(m.existence, Existence::EveryWorld));
            } else {
                assert!(matches!(m.existence, Existence::NotAnalysed));
            }
            let Uniqueness::Multiple {
                observation,
                first,
                second,
            } = m.uniqueness
            else {
                panic!("{m:?}")
            };
            assert!(first.differences(&second).unwrap().any(|(_, a, b)| a != b));
            for i in 0..512 {
                let x = atom(&p, &format!("x{i}"), &[]);
                let y = atom(&p, &format!("y{i}"), &[]);
                let value = observation.present.contains(&x);
                for model in [&first, &second] {
                    assert_eq!(model.value(&x), Some(value));
                    assert_eq!(model.value(&y), Some(value));
                }
            }
            let s = m.uniqueness_stats.unwrap();
            assert_eq!(s.scope, "downstream-cone");
            assert!(s.atoms < 512);
            assert!(s.fallback_reason.is_none());
        }
    }
}

#[test]
fn completed_cone_proofs_establish_global_uniqueness_without_another_pair_query() {
    let p = load_text(
        "input x(); relation a(); relation b(); a():-x(),!b(); b():-!x(),!a();
        relation r(); r():-a(); verification v { assumptions: []; obligations: []; }",
    );
    let mut e = prepare(&p, "v");
    for mode in [
        MeaningMode::Full,
        MeaningMode::Uniqueness,
        MeaningMode::Full,
    ] {
        let m = e
            .check(
                &p.keys,
                &CheckOptions {
                    meaning: mode,
                    ..Default::default()
                },
            )
            .unwrap()
            .meaning
            .unwrap();
        assert!(matches!(m.uniqueness, Uniqueness::AtMostOne));
        let s = m.uniqueness_stats.unwrap();
        if mode == MeaningMode::Full {
            assert_eq!(s.scope, "local-proofs");
            assert_eq!(s.pair_queries, 0);
        } else {
            assert_eq!(s.scope, "downstream-cone");
        }
    }
}

#[test]
fn settled_atoms_remove_dead_cycles_before_meaning_and_keep_original_evidence() {
    let p = load_text(
        "relation f(); f(); input x(); relation p(); p():-f(); p():-x(); relation q(); relation r(); q():-!p(),!r(); r():-!q(); obligation clean:empty(p); verification v{assumptions:[];obligations:[clean];}",
    );
    let mut engine = prepare(&p, "v");
    let target = atom(&p, "p", &[]);
    assert_eq!(engine.prepared_value(&target).unwrap(), Some(true));
    assert!(engine.program().components().all(|c| c.cycle.is_none()));
    assert!(
        engine
            .original_program()
            .components()
            .any(|c| c.cycle.is_some())
    );
    engine.preparation_receipts().total().unwrap();
    for _ in 0..2 {
        // No world enumeration is available: stratification must establish meaning.
        let report = engine
            .check(
                &p.keys,
                &CheckOptions {
                    max_worlds: 0,
                    ..Default::default()
                },
            )
            .unwrap();
        assert!(report.meaning.as_ref().unwrap().unique_everywhere());
        assert_eq!(empty(&report).present, 1);
        let example = &empty(&report).examples[0];
        let Some(Attribution::Complete(steps)) = &example.attribution else {
            panic!("missing original evidence")
        };
        let GroundEvidence::Derived { rule, .. } = &steps[&target].evidence else {
            panic!()
        };
        assert!(!rule.body.is_empty(), "must keep original f premise");
        assert!(steps.contains_key(&atom(&p, "f", &[])));
    }
    assert!(matches!(
        engine
            .models(&Query {
                pins: vec![(target.clone(), false)],
                ..Default::default()
            })
            .unwrap(),
        Answer::NoModel
    ));
    let Answer::Model(m) = engine
        .models(&Query {
            pins: vec![(target.clone(), true)],
            ..Default::default()
        })
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(m.value(&target), Some(true));
}

#[test]
fn subsumption_notices_are_located_advisory_and_report_partial_instances() {
    for (fixed, partial) in [("p(a);", true), ("p(a);p(b);", false)] {
        let p = load_text(&format!(
            "sort S;const a,b:S;input x(s:S);relation p(s:S);{fixed}\np(X):-x(X);\nverification v{{assumptions:[];obligations:[];}}"
        ));
        let mut e = prepare(&p, "v");
        let report = e.check(&p.keys, &CheckOptions::default()).unwrap();
        assert!(report.proved());
        assert_eq!(report.subsumed_producers.len(), 1);
        let notice = &report.subsumed_producers[0];
        assert_eq!(notice.instances.len(), if partial { 1 } else { 2 });
        let shown = presentation::present_stable(&p, &report).unwrap();
        let notices: Vec<_> = shown
            .diagnostics
            .iter()
            .filter(|d| d.kind == Kind::SubsumedProducer)
            .collect();
        assert_eq!(notices.len(), 1);
        assert_eq!(
            notices[0].kind.severity(),
            denotate_presentation::Severity::Information
        );
        assert_eq!(notices[0].message.starts_with("Some instances"), partial);
        assert!(!notices[0].related.is_empty());
        assert!(notices[0].notes.iter().any(|n| n.contains("p(a)")));
        assert_eq!(shown.status["state"], "proved");
        let source = p.sources.text(notices[0].primary).unwrap();
        assert!(source.contains("p(X)"));
    }
}

#[test]
fn propagated_settlement_notices_do_not_claim_their_own_support_is_redundant() {
    let p = load_text(
        "relation f();f();input x();relation p();relation q();p():-f();p():-x();q():-p();p():-q();verification v{assumptions:[];obligations:[];}",
    );
    let report = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(report.proved());
    for notice in &report.subsumed_producers {
        for (candidate, producer) in &notice.instances {
            assert_ne!(candidate, producer);
        }
    }
    let shown = presentation::present_stable(&p, &report).unwrap();
    let notices: Vec<_> = shown
        .diagnostics
        .iter()
        .filter(|d| d.kind == Kind::SubsumedProducer)
        .collect();
    assert_eq!(notices.len(), 2);
    for d in notices {
        let text = p.sources.text(d.primary).unwrap();
        assert!(!text.contains("p():-f()") && !text.contains("q():-p()"));
    }
}

#[test]
fn constant_producer_breaks_a_readability_cycle_and_names_the_other_producer() {
    let p = load_text(
        "input raw();input gate();relation supplied();relation readable();relation term();relation seen();supplied():-term();supplied();readable():-supplied();term():-gate(),!seen();seen():-readable(),raw();verification v{assumptions:[];obligations:[];}",
    );
    let mut e = prepare(&p, "v");
    for name in ["supplied", "readable"] {
        assert_eq!(e.prepared_value(&atom(&p, name, &[])).unwrap(), Some(true));
    }
    let report = e
        .check(
            &p.keys,
            &CheckOptions {
                max_worlds: 0,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(report.proved());
    let shown = presentation::present_stable(&p, &report).unwrap();
    let notice = shown
        .diagnostics
        .iter()
        .find(|d| d.kind == Kind::SubsumedProducer)
        .unwrap();
    assert!(
        p.sources
            .text(notice.primary)
            .unwrap()
            .contains("supplied():-term()")
    );
}

#[test]
fn syntactic_subsumption_cuts_cycles_and_reports_original_support() {
    let p = load_text(
        "input seed(); relation p(); relation q();\np():-seed(),!q();\np():-seed();\nq():-!p();\nverification v{assumptions:[];obligations:[];}",
    );
    let mut e = prepare(&p, "v");
    assert!(e.original_program().components().any(|c| c.cycle.is_some()));
    assert_eq!(
        e.negative_components(&p.keys, &Limits::default())
            .unwrap()
            .total,
        0
    );
    let options = CheckOptions {
        max_worlds: 0,
        ..CheckOptions::default()
    };
    for _ in 0..2 {
        let r = e.check(&p.keys, &options).unwrap();
        assert!(r.proved());
        assert_eq!(r.subsumed_producers.len(), 1);
        let n = &r.subsumed_producers[0];
        assert!(n.syntactic);
        assert_eq!(n.instances.len(), 1);
        let original = e.original_program();
        assert_eq!(
            original.original_rule(n.instances[0].0).unwrap().body.len(),
            2
        );
        assert_eq!(
            original.original_rule(n.instances[0].1).unwrap().body.len(),
            1
        );
        let presented = presentation::present_stable(&p, &r).unwrap();
        let d = presented
            .diagnostics
            .iter()
            .find(|d| d.kind == Kind::SubsumedProducer)
            .unwrap();
        assert!(d.message.contains("sufficient premises"));
        assert!(
            d.primary.byte_range().start
                < p.sources
                    .snapshot(d.primary.snapshot())
                    .unwrap()
                    .text
                    .find("p():-seed();")
                    .unwrap()
        );
        assert!(!d.related.is_empty());
    }
}

#[test]
fn negative_inventory_is_separate_deterministic_and_includes_self_loops() {
    let p = load_text(
        "relation a();relation b();relation c();a():-!b();b():-!a();c():-a(),!c();verification v{assumptions:[];obligations:[];}",
    );
    let mut e = prepare(&p, "v");
    let signature = |e: &Engine| {
        let listing = e.negative_components(&p.keys, &Limits::default()).unwrap();
        assert!(listing.incomplete.is_none());
        assert_eq!(listing.total, 2);
        listing
            .components
            .iter()
            .map(|c| {
                (
                    c.representative.clone(),
                    c.atoms,
                    c.cycle
                        .iter()
                        .map(|edge| {
                            (
                                AtomKey::from_atom(&p.keys, &edge.consumer).unwrap(),
                                AtomKey::from_atom(&p.keys, &edge.provider).unwrap(),
                                edge.polarity == Polarity::Negative,
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>()
    };
    let first = signature(&e);
    assert_eq!(first.iter().map(|c| c.1).collect::<Vec<_>>(), [2, 1]);
    assert_eq!(first.iter().map(|c| c.2.len()).collect::<Vec<_>>(), [2, 1]);
    let short = e
        .negative_components(
            &p.keys,
            &Limits {
                max_work: 0,
                ..Limits::default()
            },
        )
        .unwrap();
    assert!(short.incomplete.is_some());
    assert_eq!(short.total, 2);
    // Find a cutoff during cycle sampling, without pinning an operation count.
    assert!((1..100).any(|work| {
        let partial = e
            .negative_components(
                &p.keys,
                &Limits {
                    max_work: work,
                    ..Limits::default()
                },
            )
            .unwrap();
        partial.incomplete.is_some()
            && partial
                .components
                .iter()
                .any(|c| c.atoms > 0 && !c.cycle_search_complete)
    }));
    let result = e.check(&p.keys, &CheckOptions::default()).unwrap();
    let fresh = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert_eq!(result.has_failures(), fresh.has_failures());
    assert_eq!(signature(&e), first);
    assert_eq!(signature(&prepare(&p, "v")), first);
}

#[test]
fn duplicate_survivor_and_edit_restoration_keep_models_and_locations() {
    for tail in ["p():-seed();p():-seed();", "", "p():-seed();p():-seed();"] {
        let p = load_text(&format!(
            "input seed();relation p();relation q();p():-seed(),!q();q():-!p();{tail}verification v{{assumptions:[];obligations:[];}}"
        ));
        let mut warm = prepare(&p, "v");
        for _ in 0..2 {
            let r = warm.check(&p.keys, &CheckOptions::default()).unwrap();
            let mut fresh = prepare(&p, "v");
            assert_eq!(
                r.proved(),
                fresh
                    .check(&p.keys, &CheckOptions::default())
                    .unwrap()
                    .proved()
            );
            assert_eq!(
                warm.negative_components(&p.keys, &Limits::default())
                    .unwrap()
                    .total,
                if tail.is_empty() { 1 } else { 0 }
            );
            if !tail.is_empty() {
                assert_eq!(r.subsumed_producers.len(), 2);
                let supports = r
                    .subsumed_producers
                    .iter()
                    .flat_map(|n| {
                        n.instances
                            .iter()
                            .map(|(_, s)| warm.original_program().original_rule(*s).unwrap().source)
                    })
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(supports.len(), 1);
                assert!(
                    r.subsumed_producers
                        .iter()
                        .all(|n| !supports.contains(&n.rule))
                );
            }
        }
    }
}

#[test]
fn recursive_survivor_is_safe_and_inventory_bounds_long_cycle_examples() {
    let p = load_text(
        "input seed();relation p();relation q();p():-seed(),q();p():-q();q():-p();q():-seed();verification v{assumptions:[];obligations:[];}",
    );
    let mut e = prepare(&p, "v");
    let r = e.check(&p.keys, &CheckOptions::default()).unwrap();
    assert!(r.proved());
    assert!(r.subsumed_producers.iter().any(|n| n.syntactic));
    for flag in [false, true] {
        let Answer::Model(m) = e
            .models(&Query {
                pins: vec![(atom(&p, "seed", &[]), flag)],
                ..Query::default()
            })
            .unwrap()
        else {
            panic!()
        };
        assert_eq!(m.value(&atom(&p, "p", &[])), Some(flag));
    }
    let mut text = String::new();
    for i in 0..14 {
        text.push_str(&format!("relation r{i}();"));
    }
    for i in 0..14 {
        text.push_str(&format!("r{i}():-!r{}();", (i + 1) % 14));
    }
    text.push_str("verification v{assumptions:[];obligations:[];}");
    let p = load_text(&text);
    let e = prepare(&p, "v");
    let inventory = e.negative_components(&p.keys, &Limits::default()).unwrap();
    assert_eq!(inventory.total, 1);
    assert_eq!(inventory.components[0].cycle.len(), 12);
    assert_eq!(inventory.components[0].omitted_edges, 2);
}

#[test]
fn keyless_query_api_keeps_producers_without_inventing_an_arena_order() {
    let p = load_text(
        "input seed();relation p();relation q();p():-seed(),!q();p():-seed();q():-!p();verification v{assumptions:[];obligations:[];}",
    );
    let v = p.corpus.verifications().next().unwrap().id;
    let mut keyless = Engine::prepare(
        &p.corpus,
        &p.domains,
        &denotate_ir::SemanticKeys::default(),
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap();
    let mut keyed = prepare(&p, "v");
    assert!(keyless.program().rules().count() > keyed.program().rules().count());
    for present in [false, true] {
        let query = Query {
            pins: vec![(atom(&p, "seed", &[]), present)],
            ..Query::default()
        };
        let Answer::Model(a) = keyless.models(&query).unwrap() else {
            panic!()
        };
        let Answer::Model(b) = keyed.models(&query).unwrap() else {
            panic!()
        };
        for name in ["p", "q"] {
            assert_eq!(a.value(&atom(&p, name, &[])), b.value(&atom(&p, name, &[])));
        }
    }
}

fn cone_prepare(p: &LoadedProgram) -> Engine {
    let v = p.corpus.verifications().find(|v| v.name == "v").unwrap();
    Engine::prepare_scoped(
        &p.corpus,
        &p.domains,
        &p.keys,
        v.id,
        &Limits::default(),
        QueryLimits::default(),
        PreparationScope::ObligationCones,
    )
    .unwrap()
}
fn cone_options() -> CheckOptions {
    CheckOptions {
        meaning: MeaningMode::Cone,
        ..Default::default()
    }
}

#[test]
fn obligation_cones_isolate_both_meaning_and_counterexamples() {
    for (text, exists, violation) in [
        ("relation r(); relation p(); p():-!p();", true, false),
        (
            "relation a(); relation b(); a():-!b(); b():-!a(); relation r(); r():-a(); relation c(); c():-r(),!c();",
            true,
            true,
        ),
        (
            "input flag(); relation r(); r():-flag(),!r();",
            false,
            false,
        ),
    ] {
        let p = load_text(&format!("{text} obligation clean:empty(r); {V}"));
        let mut warm = cone_prepare(&p);
        for engine in [&mut warm, &mut cone_prepare(&p)] {
            for _ in 0..2 {
                let r = engine.check(&p.keys, &cone_options()).unwrap();
                let m = r.meaning.as_ref().unwrap();
                assert_eq!(matches!(m.existence, Existence::EveryWorld), exists);
                assert_eq!(r.has_failures(), violation);
                assert_eq!(r.proved(), exists && !violation);
                assert!(matches!(m.uniqueness, Uniqueness::NotAnalysed));
                assert_eq!(r.scope.label, "obligation-cones");
                let summary =
                    denotate_presentation::stable_summary(&p.corpus, &p.keys, &r).unwrap();
                assert_eq!(
                    summary["state"],
                    if !exists || violation {
                        "findings"
                    } else {
                        "proved"
                    }
                );
                assert_eq!(summary["meaning"]["outsideAnalysed"], false);
                if exists {
                    let root = atom(&p, "r", &[]);
                    let Answer::Model(model) = engine.models(&Query::default()).unwrap() else {
                        panic!()
                    };
                    assert!(
                        model.value(&root).is_some(),
                        "selected absent roots remain in scope"
                    );
                    if !violation {
                        assert!(matches!(
                            engine
                                .models(&Query {
                                    pins: vec![(root, true)],
                                    exclude: vec![]
                                })
                                .unwrap(),
                            Answer::NoModel
                        ));
                    }
                }
                if violation {
                    let example = &empty(&r).examples[0];
                    assert_eq!(example.replay_scope, ReplayScope::ConeOnly);
                    assert!(matches!(
                        example.attribution,
                        Some(Attribution::Complete(_))
                    ));
                }
                if let Existence::NoMeaning(w) = &m.existence {
                    assert!(w.present.contains(&atom(&p, "flag", &[])));
                }
            }
        }
        let full = prepare(&p, "v")
            .check(&p.keys, &CheckOptions::default())
            .unwrap();
        assert_eq!(full.proved(), violation);
        if violation {
            assert!(empty(&full).proved());
        }
    }
}

#[test]
fn cone_world_contract_is_independent_and_scoped_models_do_not_invent_absence() {
    let p = load_text(
        "input flag(); relation restriction(); restriction():-flag();
        assumption exclude:empty(restriction); relation r(); r():-flag();
        relation outside(); outside():-!outside(); obligation clean:empty(r);
        verification v { assumptions:[exclude]; obligations:[clean]; }",
    );
    let mut e = cone_prepare(&p);
    assert!(e.check(&p.keys, &cone_options()).unwrap().proved());
    assert!(matches!(
        e.worlds(&Query {
            pins: vec![(atom(&p, "flag", &[]), true)],
            exclude: vec![]
        })
        .unwrap(),
        Answer::NoModel
    ));
    let Answer::Model(m) = e.models(&Query::default()).unwrap() else {
        panic!()
    };
    assert_eq!(m.value(&atom(&p, "outside", &[])), None);
    assert_eq!(m.value(&atom(&p, "restriction", &[])), None);
    assert_eq!(m.value(&atom(&p, "r", &[])), Some(false));
    assert!(
        e.models(&Query {
            pins: vec![(atom(&p, "outside", &[]), false)],
            exclude: vec![]
        })
        .is_err()
    );
    assert!(prepare(&p, "v").check(&p.keys, &cone_options()).is_err());
}

#[test]
fn cone_union_checks_uniqueness_conflicts_and_keeps_fixed_evidence() {
    let p = load_text("sort S; const a,b:S; input flag(); relation r(s:S);
        r(a):-flag(); r(b):-flag(); relation c(); c():-flag(),!c();
        relation fixed(); fixed(); obligation unique:at_most_one(r,group_by:());
        obligation clean:empty(fixed); verification v { assumptions:[]; obligations:[unique,clean]; }");
    let r = cone_prepare(&p).check(&p.keys, &cone_options()).unwrap();
    assert!(matches!(
        r.meaning.as_ref().unwrap().existence,
        Existence::EveryWorld
    ));
    assert!(
        r.groups
            .iter()
            .any(|g| matches!(g.outcome, VerifiedOutcome::Counterexample(_)))
    );
    assert_eq!(empty(&r).present, 1);
    assert!(matches!(
        empty(&r).examples[0].attribution,
        Some(Attribution::Complete(_))
    ));
    let full = prepare(&p, "v")
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(
        full.groups
            .iter()
            .all(|g| matches!(g.outcome, VerifiedOutcome::Proved))
    );
}

#[test]
fn cone_empty_selection_is_consistency_only_and_optional_uniqueness_is_separate() {
    let p =
        load_text("relation p(); p():-!p(); verification v { assumptions:[]; obligations:[]; }");
    let r = cone_prepare(&p).check(&p.keys, &cone_options()).unwrap();
    assert!(r.proved());
    assert_eq!(r.scope.atoms, 0);
    let p = load_text(&format!(
        "relation a(); relation b(); a():-!b(); b():-!a(); relation r(); r():-a(),b(); obligation clean:empty(r); {V}"
    ));
    let mut e = cone_prepare(&p);
    assert!(e.check(&p.keys, &cone_options()).unwrap().proved());
    let m = e.meaning(&CheckOptions::default()).unwrap();
    assert!(matches!(m.existence, Existence::EveryWorld));
    assert!(matches!(m.uniqueness, Uniqueness::Multiple { .. }));
    assert!(e.check(&p.keys, &cone_options()).unwrap().proved());
}

#[test]
fn obligation_cones_match_exhaustive_reduct_oracle() {
    // Original rules, independent of the checker's graph, simplification and SAT.
    // a=0,b=1,r=2,c=3,input i=4; bool is positive polarity.
    let templates = vec![
        (0, vec![(1, false)]),
        (1, vec![(0, false)]),
        (0, vec![(4, true)]),
        (1, vec![(4, false)]),
        (2, vec![(0, true)]),
        (2, vec![(1, true)]),
        (3, vec![(2, true), (3, false)]),
        (2, vec![(3, true)]),
    ];
    let names = ["a", "b", "r", "c", "i"];
    for chosen in 0..256 {
        let rules: Vec<_> = templates
            .iter()
            .enumerate()
            .filter(|(i, _)| chosen & (1 << i) != 0)
            .map(|(_, r)| r)
            .collect();
        let mut scope = 1usize << 2;
        loop {
            let before = scope;
            for (head, body) in &rules {
                if scope & (1 << head) != 0 {
                    for (a, _) in body {
                        scope |= 1 << a;
                    }
                }
            }
            if scope == before {
                break;
            }
        }
        let mut every = true;
        let mut present = false;
        for input in [false, true] {
            let mut exists = false;
            for interpretation in 0usize..16 {
                if interpretation & !(scope & 15) != 0 {
                    continue;
                }
                let candidate = interpretation | if input { 16 } else { 0 };
                let mut least = if input { 16 } else { 0 };
                loop {
                    let before = least;
                    for (head, body) in &rules {
                        if scope & (1 << head) == 0 {
                            continue;
                        }
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
                    if before == least {
                        break;
                    }
                }
                if least == candidate {
                    exists = true;
                    present |= candidate & 4 != 0;
                }
            }
            every &= exists;
        }
        let mut text =
            "input i(); relation a(); relation b(); relation r(); relation c();".to_string();
        for (head, body) in &rules {
            text.push_str(&format!(
                "{}():-{};",
                names[*head],
                body.iter()
                    .map(|(a, pos)| format!("{}{}()", if *pos { "" } else { "!" }, names[*a]))
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
        text.push_str(&format!("obligation clean:empty(r); {V}"));
        let p = load_text(&text);
        let r = cone_prepare(&p).check(&p.keys, &cone_options()).unwrap();
        assert_eq!(
            matches!(r.meaning.as_ref().unwrap().existence, Existence::EveryWorld),
            every,
            "{text}"
        );
        assert_eq!(empty(&r).present > 0, present, "{text}");
    }
}

#[test]
fn explicit_root_scope_reuses_the_same_isolation_for_future_plan_consumers() {
    let p = load_text(
        "input flag(); relation out(); out():-flag(); relation bad();bad():-!bad();
        verification v { assumptions:[]; obligations:[]; }",
    );
    let v = p.corpus.verifications().next().unwrap().id;
    let mut e = Engine::prepare_scoped(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
        PreparationScope::Roots(vec![atom(&p, "out", &[])]),
    )
    .unwrap();
    assert!(
        e.meaning(&CheckOptions::default())
            .unwrap()
            .unique_everywhere()
    );
    assert_eq!(e.scope().label, "root-cones");
    assert!(e.prepared_value(&atom(&p, "bad", &[])).is_err());
    let Answer::Model(m) = e
        .models(&Query {
            pins: vec![(atom(&p, "flag", &[]), true)],
            exclude: vec![],
        })
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(m.value(&atom(&p, "out", &[])), Some(true));
    assert_eq!(m.value(&atom(&p, "bad", &[])), None);
}

#[test]
fn cone_boundary_precedes_subsumption_of_an_original_dependency() {
    let p = load_text(&format!(
        "input flag(); relation p();p():-!p();
        relation r();r():-flag();r():-flag(),p(); obligation clean:empty(r); {V}"
    ));
    let mut e = cone_prepare(&p);
    assert_eq!(e.scope().atoms, 3);
    let r = e.check(&p.keys, &cone_options()).unwrap();
    assert!(matches!(
        r.meaning.as_ref().unwrap().existence,
        Existence::NoMeaning(_)
    ));
    assert!(!r.proved());
}
