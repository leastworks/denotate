use super::*;
use crate::test_support::symbolic::{assert_symbolic_agrees, condition, nullary, relation, rule};
use denotate_ir::*;
use std::sync::{Arc, Mutex};

fn fixture() -> (GroundProgram, Vec<RelationId>) {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let y = relation(&mut c, "y", true);
    let nodes: Vec<_> = (0..4)
        .map(|i| relation(&mut c, &format!("node{i}"), false))
        .collect();
    for i in 0..nodes.len() {
        rule(&mut c, nodes[i], &[(nodes[(i + 1) % nodes.len()], false)]);
    }
    rule(&mut c, nodes[3], &[(x, false), (y, false)]);
    (
        GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap(),
        nodes,
    )
}
#[test]
fn recursive_profile_reports_shape_current_storage_and_preserves_every_world() {
    let (p, nodes) = fixture();
    assert_symbolic_agrees(&p);
    let events = Arc::new(Mutex::new(Vec::new()));
    let out = events.clone();
    let profile = Profile::new(|_| {});
    profile.observe_conditions(move |e| out.lock().unwrap().push(e.observation));
    let limits = Limits {
        profile,
        ..Limits::default()
    };
    let baseline = p.symbolic(&Limits::default()).unwrap();
    let observed = p.symbolic(&limits).unwrap();
    for n in nodes {
        assert!(
            observed
                .context()
                .equivalent(
                    &condition(&baseline, nullary(n)),
                    &condition(&observed, nullary(n)),
                    &limits
                )
                .unwrap()
        );
    }
    let events = events.lock().unwrap();
    let shape = events
        .iter()
        .find_map(|e| {
            if let ConditionObservation::RecursiveShape(s) = e {
                Some(s)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(shape.atoms, 4);
    assert!(!shape.cycles.is_empty());
    for cycle in &shape.cycles {
        assert_eq!(cycle.first(), cycle.last());
        for edge in cycle.windows(2) {
            assert!(
                p.dependencies()
                    .any(|d| d.consumer == edge[0] && d.provider == edge[1])
            );
        }
    }
    let s = events
        .iter()
        .find_map(|e| {
            if let ConditionObservation::RecursiveSnapshot(s) = e {
                Some(s)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(s.state, "complete");
    assert!(s.completed_rounds > 0 && s.rule_evaluations > 0);
    assert_eq!(s.largest.len(), 4);
    assert_eq!(s.component_nodes, s.relations.iter().map(|r| r.nodes).sum());
    assert!(s.storage.nodes <= s.component_nodes);
    assert!(s.result_nodes >= s.storage.nodes as u64);
}
#[test]
fn recursive_profile_captures_exhaustion_before_restart_and_global_abort() {
    let (p, _) = fixture();
    for global in [false, true] {
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let profile = Profile::new(|_| {});
        let cancellation = Cancellation::default();
        let cancel = cancellation.clone();
        profile.observe_conditions(move |e| {
            if global && matches!(e.observation, ConditionObservation::RecursiveShape(_)) {
                cancel.cancel();
            }
            out.lock().unwrap().push(e.observation);
        });
        let limits = Limits {
            profile,
            cancellation,
            max_bdd_nodes: if global { 100_000 } else { 3 },
            ..Limits::default()
        };
        let result = p.symbolic(&limits);
        if global {
            assert!(result.is_err());
        }
        let events = events.lock().unwrap();
        assert!(events.iter().any(|e|matches!(e,ConditionObservation::RecursiveSnapshot(s) if s.error.is_some() && s.state==if global {"interrupted"}else{"exhausted"})));
        if !global {
            let baseline = p
                .symbolic(&Limits {
                    max_bdd_nodes: 3,
                    ..Limits::default()
                })
                .unwrap();
            let profiled = result.unwrap();
            for a in p.atoms() {
                assert_eq!(
                    format!("{:?}", baseline.fact(a).unwrap()),
                    format!("{:?}", profiled.fact(a).unwrap())
                );
            }
        }
    }
}

fn scan<T>(run: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            SCAN_ONLY.with(|s| s.set(self.0));
        }
    }
    let _restore = Restore(SCAN_ONLY.with(|s| s.replace(true)));
    run()
}
#[test]
fn worklist_agrees_with_scan_and_concrete_worlds_and_releases_metadata_on_pressure() {
    let (p, _) = fixture();
    let unlimited = Limits::default();
    let reference = scan(|| p.symbolic(&unlimited).unwrap());
    let mut saw_fallback = false;
    for cap in [16, 24, 32, 40, 48, 64, 1000] {
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let profile = Profile::new(|_| {});
        profile.observe_conditions(move |e| out.lock().unwrap().push(e.observation));
        let limits = Limits {
            profile,
            max_condition_nodes: cap,
            ..Limits::default()
        };
        let sparse = p.symbolic(&limits).unwrap();
        let scanned = scan(|| p.symbolic(&limits).unwrap());
        for atom in p.atoms() {
            match (sparse.fact(atom).unwrap(), scanned.fact(atom).unwrap()) {
                (SymbolicFact::Settled(a), SymbolicFact::Settled(b)) => {
                    assert!(sparse.context().equivalent(&a, &b, &unlimited).unwrap());
                    assert!(
                        sparse
                            .context()
                            .equivalent(&a, &condition(&reference, atom.clone()), &unlimited)
                            .unwrap()
                    );
                }
                (SymbolicFact::Inconclusive(_), SymbolicFact::Inconclusive(_)) => {}
                other => panic!("{cap}: {other:?}"),
            }
        }
        saw_fallback |= events.lock().unwrap().iter().any(|e|matches!(e,ConditionObservation::RecursiveSnapshot(s) if s.state=="scheduler-fallback"));
    }
    assert!(saw_fallback);
    assert_symbolic_agrees(&p);
}

#[test]
fn sparse_positive_cycles_agree_with_scan_for_multiple_growing_producers() {
    for n in [1, 2, 5, 12] {
        let mut c = Corpus::new();
        let x = relation(&mut c, "x", true);
        let y = relation(&mut c, "y", true);
        let rs: Vec<_> = (0..n)
            .map(|i| relation(&mut c, &format!("r{i}"), false))
            .collect();
        for i in 0..n {
            rule(&mut c, rs[i], &[(rs[(i + 1) % n], false)]);
            if i % 2 == 0 {
                rule(&mut c, rs[i], &[(x, false), (y, true)]);
            }
        }
        rule(&mut c, rs[n - 1], &[(y, false)]);
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        assert_symbolic_agrees(&p);
        let sparse = p.symbolic(&l).unwrap();
        let reference = scan(|| p.symbolic(&l).unwrap());
        for a in p.atoms() {
            assert!(
                sparse
                    .context()
                    .equivalent(
                        &condition(&sparse, a.clone()),
                        &condition(&reference, a.clone()),
                        &l
                    )
                    .unwrap()
            );
        }
    }
}
