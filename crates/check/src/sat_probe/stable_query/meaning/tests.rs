use super::*;
use crate::test_support::rewrites::{atom, rel, rule};

fn prepared(n: usize, cached: bool) -> Engine {
    let mut corpus = Corpus::new();
    for i in 0..n {
        let flag = rel(&mut corpus, &format!("flag{i}"), true);
        let a = rel(&mut corpus, &format!("a{i}"), false);
        let z = rel(&mut corpus, &format!("b{i}"), false);
        rule(&mut corpus, a, &[(flag, false)]);
        rule(&mut corpus, a, &[(z, true)]);
        rule(&mut corpus, z, &[(a, true)]);
    }
    let v = corpus
        .verification_in(denotate_ir::Namespace::default(), "v", [], [])
        .unwrap();
    Engine::prepare(
        &corpus,
        &Domains::new(),
        &SemanticKeys::default(),
        v,
        &Limits::default(),
        QueryLimits {
            cache_entries: if cached { 32 } else { 0 },
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn enumeration_appends_once_bypasses_cache_and_isolates_every_query() {
    for cached in [false, true] {
        let mut e = prepared(3, cached);
        // Populate the ordinary empty-world key first. It must not answer the
        // changing enumeration, nor be overwritten by its eventual NoModel.
        assert!(matches!(
            e.worlds(&Query::default()).unwrap(),
            Answer::Model(_)
        ));
        let limits = Limits::default();
        let mut b = Budget::new(&limits);
        let enumeration = e.start_enumeration(&mut b).unwrap();
        let untouched = e.start_enumeration(&mut b).unwrap();
        let cache_len = e.cache.len();
        let mut stats = ExistenceStats::default();
        let mut worlds = BTreeSet::new();
        let mut widths = 0;
        loop {
            let world = match e.enumeration_world(&enumeration, &mut b).unwrap() {
                Answer::NoModel => break,
                Answer::Model(m) => m,
                other => panic!("{other:?}"),
            };
            assert!(!e.stats.cache_hit);
            assert_eq!(e.cache.len(), cache_len);
            let values = world.cone_values(&e.world_cone, &mut b).unwrap();
            let cover: BTreeSet<_> = e
                .cone
                .input
                .iter()
                .enumerate()
                .filter_map(|(i, yes)| yes.then_some(i))
                .collect();
            assert!(worlds.insert(cover.iter().map(|i| values[*i]).collect::<Vec<_>>()));
            let before = e.cnf.literals;
            e.exclude_world_cube(&enumeration, &cover, &values, &mut stats, &mut b)
                .unwrap();
            widths += cover.len();
            assert_eq!(e.cnf.literals - before, cover.len() + 1);
            assert_eq!(stats.emitted_exclusion_literals, widths);
            assert_eq!(stats.emitted_selector_literals, worlds.len());
            assert!(matches!(
                e.enumeration_world(&untouched, &mut b).unwrap(),
                Answer::Model(_)
            ));
        }
        assert!(worlds.len() > 1);
        assert_eq!(worlds.len(), 1 << e.program.inputs.len());
        assert!(!e.stats.cache_hit);
        assert_eq!(e.cache.len(), cache_len);
        // Both cached and actual ordinary SAT searches remain independent.
        assert!(matches!(
            e.worlds(&Query::default()).unwrap(),
            Answer::Model(_)
        ));
        e.cache.clear();
        e.cache_bytes = 0;
        assert!(matches!(
            e.worlds(&Query::default()).unwrap(),
            Answer::Model(_)
        ));
        assert!(!e.stats.cache_hit);
        let inputs: Vec<_> = e.program.inputs.iter().cloned().collect();
        for world in worlds {
            let q = Query {
                pins: inputs.iter().cloned().zip(world).collect(),
                exclude: vec![],
            };
            assert!(matches!(e.worlds(&q).unwrap(), Answer::Model(_)));
            assert!(matches!(e.models(&q).unwrap(), Answer::Model(_)));
        }
        let meaning = e.meaning(&CheckOptions::default()).unwrap();
        assert!(matches!(meaning.existence, Existence::EveryWorld));
        assert!(matches!(meaning.uniqueness, Uniqueness::Multiple { .. }));
        let s = meaning.existence_stats.unwrap();
        assert_eq!(s.emitted_exclusion_literals, s.distinct_cube_literals);
        assert_eq!(s.emitted_selector_literals, s.cubes);
    }
}

#[test]
fn empty_cube_is_local_and_failed_append_requires_rebuild() {
    let mut e = prepared(1, false);
    let limits = Limits::default();
    let mut b = Budget::new(&limits);
    let enumeration = e.start_enumeration(&mut b).unwrap();
    let mut stats = ExistenceStats::default();
    e.exclude_world_cube(&enumeration, &BTreeSet::new(), &[], &mut stats, &mut b)
        .unwrap();
    assert_eq!(stats.emitted_exclusion_literals, 0);
    assert_eq!(stats.emitted_selector_literals, 1);
    assert!(matches!(
        e.enumeration_world(&enumeration, &mut b).unwrap(),
        Answer::NoModel
    ));
    assert!(matches!(
        e.models(&Query::default()).unwrap(),
        Answer::Model(_)
    ));
    let other = e.start_enumeration(&mut b).unwrap();
    let limits = Limits {
        max_rules: e.cnf.clauses,
        ..Limits::default()
    };
    assert!(
        e.exclude_world_cube(
            &other,
            &BTreeSet::new(),
            &[],
            &mut stats,
            &mut Budget::new(&limits)
        )
        .is_err()
    );
    assert!(e.append_failed.is_some());
    assert!(matches!(
        e.worlds(&Query::default()).unwrap(),
        Answer::Inconclusive(_)
    ));
}

#[test]
fn existence_statistics_survive_cutoff_and_repeated_checks() {
    let events = Arc::new(std::sync::Mutex::new(Vec::new()));
    let captured = events.clone();
    let mut e = prepared(3, true);
    e.limits.progress = CheckingProgress::new(move |event| captured.lock().unwrap().push(event));
    let (limited, stats) = e
        .existence(&CheckOptions {
            max_worlds: 1,
            ..Default::default()
        })
        .unwrap();
    assert!(matches!(limited, Existence::Inconclusive(_)));
    assert!(stats.cubes > 0);
    assert_eq!(
        stats.emitted_exclusion_literals,
        stats.distinct_cube_literals
    );
    assert_eq!(stats.emitted_selector_literals, stats.cubes);
    assert_eq!(
        stats.mean_inputs(),
        Some(stats.distinct_cube_literals as f64 / stats.cubes as f64)
    );
    assert!(stats.min_inputs.unwrap() <= stats.max_inputs);
    assert!(stats.distinct_inputs <= stats.support_size);
    let collected = events.lock().unwrap();
    assert!(collected.iter().any(|e| e.state == "exhausted"));
    let finished = collected
        .iter()
        .rev()
        .find(|e| e.state == "finished")
        .unwrap();
    let Some(CheckingTarget::SatExistence(final_stats)) = &finished.target else {
        panic!("{finished:?}")
    };
    assert_eq!(final_stats, &stats);
    drop(collected);
    for _ in 0..2 {
        let (answer, stats) = e.existence(&CheckOptions::default()).unwrap();
        assert!(matches!(answer, Existence::EveryWorld));
        assert_eq!(
            stats.emitted_exclusion_literals,
            stats.distinct_cube_literals
        );
        assert_eq!(stats.emitted_selector_literals, stats.cubes);
    }
    // The previous failed/complete enumerations cannot hide any ordinary input world.
    let flag = e.program.inputs.iter().next().unwrap().relation;
    assert!(matches!(
        e.worlds(&Query {
            pins: vec![(atom(flag), true)],
            ..Default::default()
        })
        .unwrap(),
        Answer::Model(_)
    ));
}
