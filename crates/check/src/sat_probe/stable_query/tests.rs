use super::*;
use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets};
use denotate_ir::*;
fn engine(c: &mut Corpus, assumptions: &[AssumptionId]) -> Engine {
    let v = c
        .verification_in(
            Namespace::new(["test"]).unwrap(),
            format!("v{}", c.verifications().count()),
            assumptions.iter().copied(),
            [],
        )
        .unwrap();
    Engine::prepare(
        c,
        &Domains::new(),
        &SemanticKeys::default(),
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
}
fn model(answer: Answer) -> Model {
    match answer {
        Answer::Model(m) => m,
        a => panic!("expected model: {a:?}"),
    }
}
fn pin(r: RelationId, v: bool) -> Query {
    Query {
        pins: vec![(atom(r), v)],
        ..Query::default()
    }
}

#[test]
fn positive_self_support_does_not_hide_a_bad_world() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let p = rel(&mut c, "p", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(flag, false), (p, false)]);
    rule(&mut c, bad, &[(flag, false)]);
    let mut e = engine(&mut c, &[]);
    // Pin the unfounded interpretation first. Grounding may already eliminate
    // this unsupported positive producer; either path must preserve the bad world.
    assert!(matches!(e.models(&pin(p, true)).unwrap(), Answer::NoModel));
    let m = model(e.models(&pin(bad, true)).unwrap());
    assert_eq!(m.value(&atom(flag)), Some(true));
    assert_eq!(m.value(&atom(p)), Some(false));
    assert_eq!(
        model(e.worlds(&pin(flag, true)).unwrap()).value(&atom(flag)),
        Some(true)
    );
}
#[test]
fn program_refinements_cannot_hide_worlds_without_a_meaning() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(flag, false), (p, true)]);
    rule(&mut c, p, &[(p, false)]);
    let mut e = engine(&mut c, &[]);
    assert!(matches!(
        e.models(&pin(flag, true)).unwrap(),
        Answer::NoModel
    ));
    assert!(e.stats().refinements > 0);
    let m = model(e.worlds(&pin(flag, true)).unwrap());
    assert_eq!(m.value(&atom(flag)), Some(true));
    assert_eq!(m.value(&atom(p)), None);
    assert_eq!(
        model(e.models(&pin(flag, false)).unwrap()).value(&atom(p)),
        Some(false)
    );
    assert!(e.worlds(&pin(p, false)).is_err());
}
#[test]
fn assumptions_and_query_modes_are_isolated_without_bdds() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(flag, false)]);
    rule(&mut c, p, &[(p, false)]);
    let a = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "a", p, [])
        .unwrap();
    for selection in [vec![a], vec![], vec![a]] {
        let mut e = engine(&mut c, &selection);
        e.limits.max_bdd_nodes = 0;
        e.limits.max_bdd_tasks = 0;
        let q = pin(flag, false);
        for world in [true, false] {
            let answer = if world { e.worlds(&q) } else { e.models(&q) }.unwrap();
            assert_eq!(matches!(answer, Answer::NoModel), !selection.is_empty());
        }
        let m = model(e.worlds(&pin(flag, true)).unwrap());
        assert_eq!(m.value(&atom(flag)), Some(true));
    }
}
#[test]
fn queries_and_exclusions_do_not_change_later_queries() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(flag, false)]);
    let mut e = engine(&mut c, &[]);
    for value in [true, false, true] {
        assert_eq!(
            model(e.models(&pin(p, value)).unwrap()).value(&atom(flag)),
            Some(value)
        );
    }
    let q = Query {
        exclude: vec![vec![]],
        ..Query::default()
    };
    assert!(matches!(e.models(&q).unwrap(), Answer::NoModel));
    assert!(matches!(
        e.models(&Query::default()).unwrap(),
        Answer::Model(_)
    ));
    let q = Query {
        pins: vec![(atom(flag), true), (atom(p), true)],
        ..Query::default()
    };
    model(e.models(&q).unwrap());
    let mut reordered = q.clone();
    reordered.pins.reverse();
    model(e.models(&reordered).unwrap());
    assert!(e.stats().cache_hit);
    let m = model(e.models(&q).unwrap());
    drop(e);
    assert_eq!(m.value(&atom(p)), Some(true));
}
#[test]
fn tiny_original_programs_match_exhaustive_stable_models() {
    // All pairs of signed one-literal producers, including positive recursion,
    // mutual negation, odd loops, input guards and headless atoms.
    for a in 0..6 {
        for b in 0..6 {
            let mut c = Corpus::new();
            let x = rel(&mut c, "x", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let rs = [x, p, q];
            rule(&mut c, p, &[(rs[a / 2], a % 2 == 1)]);
            rule(&mut c, q, &[(rs[b / 2], b % 2 == 1)]);
            let original =
                GroundProgram::prepare_cartesian(&c, &Domains::new(), &Limits::default()).unwrap();
            let atoms: Vec<_> = rs.into_iter().map(atom).collect();
            let inputs = BTreeSet::from([atom(x)]);
            let rules: Vec<_> = original.rules().cloned().collect();
            let mut e = engine(&mut c, &[]);
            for world in subsets(&[atom(x)]) {
                let expected = stable_models(&atoms, &inputs, &rules, &world);
                let mut query = pin(x, world.contains(&atom(x)));
                let mut found = BTreeSet::new();
                loop {
                    match e.models(&query).unwrap() {
                        Answer::NoModel => break,
                        Answer::Model(m) => {
                            let got = atoms
                                .iter()
                                .filter(|a| m.value(a) == Some(true))
                                .cloned()
                                .collect();
                            assert!(found.insert(got));
                            query.exclude.push(
                                atoms
                                    .iter()
                                    .map(|a| (a.clone(), m.value(a).unwrap()))
                                    .collect(),
                            );
                        }
                        a => panic!("unexpected {a:?}"),
                    }
                }
                assert_eq!(
                    found, expected,
                    "producer choices {a}, {b}; world {world:?}"
                );
                model(e.worlds(&pin(x, world.contains(&atom(x)))).unwrap());
            }
        }
    }
}
#[test]
fn resource_exhaustion_is_not_unsatisfiability_or_cached() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let mut e = engine(&mut c, &[]);
    e.config.max_solves = 0;
    assert!(matches!(
        e.models(&pin(flag, true)).unwrap(),
        Answer::Inconclusive(_)
    ));
    assert!(e.cache.is_empty());
    e.config.max_solves = 10;
    model(e.models(&pin(flag, true)).unwrap());
    e.limits.cancellation.cancel();
    assert!(matches!(
        e.models(&pin(flag, true)),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn query_cutoffs_and_cache_disable_preserve_answer_boundaries() {
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(flag, false), (p, true)]);
    rule(&mut c, p, &[(p, false)]);
    let mut e = engine(&mut c, &[]);
    e.config.max_refinements = 0;
    assert!(matches!(
        e.models(&pin(p, true)).unwrap(),
        Answer::Inconclusive(_)
    ));
    assert!(e.cache.is_empty());
    e.config.max_refinements = 64;
    assert!(matches!(e.models(&pin(p, true)).unwrap(), Answer::NoModel));
    for bytes in [0, 1024 * 1024] {
        let mut e = engine(&mut c, &[]);
        e.config.cache_entries = usize::from(bytes == 0);
        e.config.cache_bytes = bytes;
        model(e.worlds(&pin(flag, true)).unwrap());
        model(e.worlds(&pin(flag, true)).unwrap());
        assert!(!e.stats().cache_hit);
        assert!(e.cache.is_empty());
    }
    let mut e = engine(&mut c, &[]);
    e.limits.max_rules = 0;
    assert!(matches!(
        e.models(&pin(flag, true)).unwrap(),
        Answer::Inconclusive(_)
    ));
    assert!(e.append_failed.is_some());
    e.limits.max_rules = Limits::default().max_rules;
    assert!(matches!(
        e.worlds(&Query::default()).unwrap(),
        Answer::Inconclusive(_)
    ));
    let mut e = engine(&mut c, &[]);
    e.cnf.solver.cb_mut().timeout = Duration::ZERO;
    assert!(matches!(
        e.models(&pin(flag, true)).unwrap(),
        Answer::Inconclusive(_)
    ));
}

#[test]
fn seeded_recursion_and_its_negation_are_query_order_independent() {
    let mut c = Corpus::new();
    let seed = rel(&mut c, "seed", true);
    let p = rel(&mut c, "p", false);
    let missing = rel(&mut c, "missing", false);
    rule(&mut c, p, &[(seed, false)]);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, missing, &[(p, true)]);
    for order in [[p, missing], [missing, p]] {
        let mut e = engine(&mut c, &[]);
        for r in order {
            let m = model(e.models(&pin(r, true)).unwrap());
            assert_eq!(m.value(&atom(seed)), Some(r == p));
            let fresh = model(engine(&mut c, &[]).models(&pin(r, true)).unwrap());
            for a in [seed, p, missing] {
                assert_eq!(m.value(&atom(a)), fresh.value(&atom(a)));
            }
        }
    }
}

#[test]
fn whole_program_meaning_and_emptiness_agree_with_exhaustive_tiny_worlds() {
    let mut seed = 13579u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for case in 0..100 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let d = rel(&mut c, "d", false);
        let all = [i, j, a, b, d];
        for _ in 0..7 {
            let head = all[2 + next() % 3];
            let body = (0..next() % 4)
                .map(|_| (all[next() % 5], next() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, head, &body);
        }
        let original =
            GroundProgram::prepare_cartesian(&c, &Domains::new(), &Limits::default()).unwrap();
        let atoms: Vec<_> = all.into_iter().map(atom).collect();
        let inputs = BTreeSet::from([atom(i), atom(j)]);
        let rules: Vec<_> = original.rules().cloned().collect();
        let worlds = subsets(&inputs.iter().cloned().collect::<Vec<_>>());
        let expected = worlds
            .into_iter()
            .map(|w| {
                let models = stable_models(&atoms, &inputs, &rules, &w);
                (w, models)
            })
            .collect::<BTreeMap<_, _>>();
        let mut keys = SemanticKeys::default();
        for r in c.relations() {
            keys.bind_relation(
                &c,
                r.id,
                RelationKey::Named(QualifiedKey::new("test", r.name.clone())),
            )
            .unwrap();
        }
        let obligations = [a, b, d].map(|r| {
            let id = c
                .empty(format!("empty_{}", c.relation(r).unwrap().name), r, "")
                .unwrap();
            (id, r)
        });
        let v = c
            .verification_in(
                Namespace::default(),
                "checks",
                [],
                obligations.map(|(id, _)| id),
            )
            .unwrap();
        let mut e = Engine::prepare(
            &c,
            &Domains::new(),
            &keys,
            v,
            &Limits::default(),
            QueryLimits::default(),
        )
        .unwrap();
        // Every certified cube preserves this derived interpretation in every
        // matching world, checked by the independent exhaustive reduct oracle.
        for models in expected.values() {
            for model in models {
                let values: Vec<_> = (0..e.cone.fixed.len())
                    .map(|i| e.cone.fixed[i].unwrap_or_else(|| model.contains(&e.cone.atoms[i])))
                    .collect();
                let limits = Limits::default();
                let cover =
                    meaning::cubes::certified(&e.cone, &values, &mut Budget::new(&limits)).unwrap();
                for (world, alternatives) in &expected {
                    if cover
                        .iter()
                        .all(|i| world.contains(&e.cone.atoms[*i]) == values[*i])
                    {
                        assert!(
                            alternatives.iter().any(|other| e
                                .cone
                                .atoms
                                .iter()
                                .enumerate()
                                .all(|(i, a)| e.cone.input[i] || other.contains(a) == values[i])),
                            "case {case}: cube lost finite support"
                        );
                    }
                }
            }
        }
        for _ in 0..2 {
            let r = e.check(&keys, &CheckOptions::default()).unwrap();
            assert_eq!(r.context, Context::Permitted);
            let meaning = r.meaning.as_ref().unwrap();
            match &meaning.existence {
                Existence::EveryWorld => {
                    assert!(expected.values().all(|m| !m.is_empty()), "case {case}")
                }
                Existence::NoMeaning(w) => assert!(expected[&w.present].is_empty(), "case {case}"),
                v => panic!("unexpected {v:?} for tiny case {case}"),
            }
            match &meaning.uniqueness {
                Uniqueness::AtMostOne => {
                    assert!(expected.values().all(|m| m.len() <= 1), "case {case}")
                }
                Uniqueness::Multiple {
                    observation,
                    first,
                    second,
                } => {
                    let facts = |m: &Model| {
                        atoms
                            .iter()
                            .filter(|a| m.value(a) == Some(true))
                            .cloned()
                            .collect::<BTreeSet<_>>()
                    };
                    let left = facts(first);
                    let right = facts(second);
                    assert_ne!(left, right);
                    assert!(expected[&observation.present].contains(&left));
                    assert!(expected[&observation.present].contains(&right));
                }
                v => panic!("unexpected {v:?} for tiny case {case}"),
            }
            for (id, relation) in obligations {
                let tuple = atom(relation);
                let possible = expected.values().flatten().any(|m| m.contains(&tuple))
                    || r.program().fixed_value(&tuple) == Some(true);
                let empty = &r.emptiness[&id];
                assert!(empty.complete(), "case {case}");
                assert_eq!(empty.present, usize::from(possible), "case {case}");
                for example in &empty.examples {
                    assert!(
                        r.program().fixed_value(&tuple) == Some(true)
                            || expected[&example.observation.present]
                                .iter()
                                .any(|m| m.contains(&tuple))
                    );
                    assert!(
                        matches!(&example.attribution,Some(Attribution::Complete(e)) if e.contains_key(&tuple)),
                        "case {case}: {example:?}"
                    );
                }
            }
            assert_eq!(
                r.proved(),
                expected.values().all(|m| m.len() == 1)
                    && r.emptiness.values().all(EmptinessReport::proved)
            );
            // Neither pair constraints nor existence exclusions may leak into
            // later independent queries on the same engine.
            for world in expected.keys() {
                let q = Query {
                    pins: inputs
                        .iter()
                        .map(|a| (a.clone(), world.contains(a)))
                        .collect(),
                    exclude: vec![],
                };
                model(e.worlds(&q).unwrap());
                assert_eq!(
                    matches!(e.models(&q).unwrap(), Answer::Model(_)),
                    !expected[world].is_empty()
                );
            }
        }
    }
}

#[test]
fn whole_check_context_cutoffs_are_not_consistency_or_meaning_verdicts() {
    for deadline in [false, true] {
        let mut c = Corpus::new();
        rel(&mut c, "flag", true);
        let mut e = engine(&mut c, &[]);
        if deadline {
            e.limits.timeout = Duration::ZERO
        } else {
            e.config.max_solves = 0
        }
        let r = e
            .check(&SemanticKeys::default(), &CheckOptions::default())
            .unwrap();
        let Context::Inconclusive(reason) = r.context else {
            panic!("{r:?}")
        };
        assert_eq!(
            reason.resource,
            if deadline { "deadline" } else { "solves" }
        );
        assert!(r.meaning.is_none());
        assert!(!r.proved());
        e.limits.cancellation.cancel();
        assert!(matches!(
            e.check(&SemanticKeys::default(), &CheckOptions::default()),
            Err(CheckError::Cancelled)
        ));
    }
}
