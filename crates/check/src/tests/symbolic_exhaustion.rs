use crate::{contracts::ConeIndex, limits::Budget, test_support::symbolic::*, *};
use denotate_ir::*;

fn wide() -> (Corpus, RelationId, RelationId, RelationId) {
    let mut c = Corpus::new();
    let wide = relation(&mut c, "wide", false);
    for i in 0..8 {
        let input = relation(&mut c, &format!("input_{i}"), true);
        rule(&mut c, wide, &[(input, false)]);
    }
    let reader = relation(&mut c, "reader", false);
    rule(&mut c, reader, &[(wide, true)]);
    let independent = relation(&mut c, "independent", false);
    rule(&mut c, independent, &[]);
    (c, wide, reader, independent)
}

#[test]
fn admission_symbolic_exhaustion_is_local_to_the_atom_and_its_readers() {
    let (c, wide, reader, independent) = wide();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let mut budget = Budget::new(&limits);
    let cone = ConeIndex::new(&p, &mut budget)
        .unwrap()
        .build(p.atoms().cloned(), &mut budget)
        .unwrap();
    let low = Limits {
        max_bdd_nodes: 5,
        ..limits
    };
    let m = p
        .symbolic_for_admission(&mut Budget::new(&low), None, &cone)
        .unwrap();
    for r in [wide, reader] {
        assert!(matches!(
            m.fact(&nullary(r)).unwrap(),
            SymbolicFact::Inconclusive(Inconclusive {
                resource: "BDD nodes",
                ..
            })
        ));
        assert_eq!(m.unknown[&nullary(r)].atom, nullary(wide));
    }
    assert!(
        matches!(m.fact(&nullary(independent)).unwrap(), SymbolicFact::Settled(c) if c.is_true())
    );
    assert!(!m.is_complete());
}

#[test]
fn false_guards_and_true_alternatives_do_not_depend_on_unknown_values() {
    let (mut c, wide, _, _) = wide();
    let flag = relation(&mut c, "flag", true);
    let never = relation(&mut c, "never", false);
    rule(&mut c, never, &[(flag, false), (flag, true)]);
    let masked = relation(&mut c, "masked", false);
    rule(&mut c, masked, &[(wide, false), (never, false)]);
    let yes = relation(&mut c, "yes", false);
    rule(&mut c, yes, &[(wide, true)]);
    rule(&mut c, yes, &[]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let low = Limits {
        max_bdd_nodes: 5,
        ..Limits::default()
    };
    let m = p.symbolic(&low).unwrap();
    assert!(matches!(
        m.fact(&nullary(wide)).unwrap(),
        SymbolicFact::Inconclusive(_)
    ));
    assert!(matches!(m.fact(&nullary(masked)).unwrap(), SymbolicFact::Settled(c) if c.is_false()));
    assert!(matches!(m.fact(&nullary(yes)).unwrap(), SymbolicFact::Settled(c) if c.is_true()));
}

#[test]
fn positive_component_restarts_after_a_head_exhausts() {
    let (mut c, wide, reader, _) = wide();
    let copied = relation(&mut c, "copied", false);
    rule(&mut c, copied, &[(wide, false)]);
    rule(&mut c, wide, &[(copied, false)]);
    let flag = relation(&mut c, "flag", true);
    let never = relation(&mut c, "never", false);
    rule(&mut c, never, &[(flag, false), (flag, true)]);
    let masked = relation(&mut c, "masked", false);
    rule(&mut c, masked, &[(wide, false), (never, false)]);
    rule(&mut c, wide, &[(masked, false)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    assert!(p.component_for(&nullary(wide)).unwrap().recursive);
    let low = Limits {
        max_bdd_nodes: 5,
        ..Limits::default()
    };
    let m = p.symbolic(&low).unwrap();
    for r in [wide, copied, reader] {
        assert!(matches!(
            m.fact(&nullary(r)).unwrap(),
            SymbolicFact::Inconclusive(_)
        ));
        assert!(
            !m.conditions.contains_key(&nullary(r)),
            "no partial least-fixed-point escapes"
        );
    }
    assert!(matches!(m.fact(&nullary(masked)).unwrap(), SymbolicFact::Settled(c) if c.is_false()));
    assert_symbolic_agrees(&p);
}

#[test]
fn independent_cycle_is_admitted_after_symbolic_exhaustion() {
    let (mut c, wide, _, _) = wide();
    let bad = relation(&mut c, "bad", false);
    rule(&mut c, bad, &[(wide, false), (bad, true)]);
    let flag = relation(&mut c, "flag", true);
    let a = relation(&mut c, "a", false);
    let b = relation(&mut c, "b", false);
    rule(&mut c, a, &[(flag, false), (b, true)]);
    rule(&mut c, b, &[(flag, true), (a, true)]);
    let low = Limits {
        max_bdd_nodes: 5,
        ..Limits::default()
    };
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&low)
        .unwrap();
    assert!(p.admission_limit().is_none(), "{:?}", p.admission_limit());
    assert!(p.component_for(&nullary(a)).unwrap().blocked_by.is_empty());
    assert!(p.component_for(&nullary(b)).unwrap().blocked_by.is_empty());
    assert!(
        !p.component_for(&nullary(bad))
            .unwrap()
            .blocked_by
            .is_empty()
    );
}

#[test]
fn local_storage_and_task_limits_recover_but_shared_and_global_limits_do_not() {
    let (c, wide, _, _) = wide();
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let storage = p
        .symbolic(&Limits {
            max_condition_nodes: 30,
            ..Limits::default()
        })
        .unwrap();
    assert!(matches!(
        storage.fact(&nullary(wide)).unwrap(),
        SymbolicFact::Inconclusive(Inconclusive {
            resource: "condition nodes",
            ..
        })
    ));
    assert!((1..30).any(|max_bdd_tasks| {
        p.symbolic(&Limits {
            max_bdd_tasks,
            ..Limits::default()
        })
        .is_ok_and(|m| {
            matches!(
                m.fact(&nullary(wide)).unwrap(),
                SymbolicFact::Inconclusive(Inconclusive {
                    resource: "BDD tasks",
                    ..
                })
            )
        })
    }));
    for low in [
        Limits {
            max_work: 1,
            ..Limits::default()
        },
        Limits {
            max_condition_nodes: 0,
            ..Limits::default()
        },
        Limits {
            max_bdd_nodes: 2,
            ..Limits::default()
        },
    ] {
        assert!(matches!(
            p.symbolic(&low),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
}

#[test]
fn restart_work_exhaustion_keeps_the_existing_partial_reporting_boundary() {
    let (c, _, _, _) = wide();
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut exercised = false;
    for max_work in 1..1_000 {
        let low = Limits {
            max_work,
            max_bdd_nodes: 5,
            ..Limits::default()
        };
        let AnalysisOutcome::Complete(m) = p.symbolic_checked(&low).unwrap() else {
            continue;
        };
        if m.inconclusive
            .values()
            .any(|c| c.phase == "symbolic restart")
        {
            assert!(!m.is_complete());
            assert!(m.inconclusive.values().all(|c| c.resource == "work"));
            exercised = true;
            break;
        }
    }
    assert!(
        exercised,
        "exercise total work exhaustion at the new rollback scan"
    );
}

#[test]
fn forced_unknowns_and_all_remaining_exact_facts_agree_with_independent_models() {
    use crate::test_support::rewrites::{stable_models, subsets, supported_models};
    let (c, wide, reader, _) = wide();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let atoms: Vec<_> = p.atoms().cloned().collect();
    let inputs = p.input_atoms().cloned().collect();
    let rules: Vec<_> = p.rules().cloned().collect();
    let m = p
        .symbolic(&Limits {
            max_bdd_nodes: 5,
            ..limits.clone()
        })
        .unwrap();
    let unlimited = p.symbolic(&limits).unwrap();
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        let stable = stable_models(&atoms, &inputs, &rules, &world);
        let supported = supported_models(&p, &rules, &world);
        assert_eq!(stable, supported);
        assert_eq!(stable.len(), 1);
        for atom in &atoms {
            for meaning in [&m, &unlimited] {
                if let SymbolicFact::Settled(condition) = meaning.fact(atom).unwrap() {
                    assert_eq!(
                        meaning
                            .context()
                            .evaluate(&condition, world.iter().cloned(), &limits)
                            .unwrap(),
                        stable.first().unwrap().contains(atom)
                    );
                }
            }
        }
    }
    for r in [wide, reader] {
        assert!(m.unknown.contains_key(&nullary(r)));
    }
    assert!(unlimited.is_complete());
}
