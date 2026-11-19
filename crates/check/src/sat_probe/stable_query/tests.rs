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
