use super::*;
use crate::sat_probe::completion_query::tests::{keys, prepare, verification};
use crate::test_support::rewrites::{rel, rule};
use denotate_ir::{Literal, Namespace, Parameter, RelationRole, Term};
fn fixture(second: bool, dead: bool, repeat: bool) -> (Corpus, Engine, usize) {
    let mut c = Corpus::new();
    let s = c.declare_sort("Value").unwrap();
    let vs = ["a", "b", "c"].map(|v| c.declare_constant(v, s).unwrap());
    let input = c
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    let scalar = c
        .declare_relation("scalar", RelationRole::Derived, [Parameter::new("v", s)])
        .unwrap();
    let extra = rel(&mut c, "extra", !dead);
    let p = rel(&mut c, "p", false);
    for (n, v) in vs.iter().enumerate() {
        if repeat && n == 2 {
            continue;
        }
        let head = c.atom(scalar, [Term::Constant(*v)]).unwrap();
        let source = c.atom(input, [Term::Constant(*v)]).unwrap();
        c.add_rule(head, [Literal::Positive(source)]).unwrap();
    }
    if second {
        let head = c.atom(scalar, [Term::Constant(vs[0])]).unwrap();
        let source = c.atom(extra, []).unwrap();
        c.add_rule(head, [Literal::Positive(source)]).unwrap();
    }
    let h = c.atom(p, []).unwrap();
    let v = c.atom(input, [Term::Constant(vs[2])]).unwrap();
    let other = c.atom(p, []).unwrap();
    c.add_rule(other, [Literal::Positive(v), Literal::Negative(h)])
        .unwrap();
    let a = c
        .assume_in(
            Namespace::default(),
            "single",
            Cardinality::AtMostOne,
            scalar,
            [],
        )
        .unwrap();
    let v = verification(&mut c, None, &[a]);
    let e = prepare(&c, v, &[(s, vs.to_vec())].into());
    let third = e.program.atom_index[&GroundAtom::new(input, [vs[2]])];
    (c, e, third)
}
#[test]
fn derived_certificates_use_live_own_equations_and_exclude_repeated_values() {
    for (second, dead, repeat, expected) in [
        (false, false, false, 3),
        (true, false, false, 0),
        (true, true, false, 3),
        (false, false, true, 2),
    ] {
        let (c, e, third) = fixture(second, dead, repeat);
        let l = e.limits.clone();
        let mut b = Budget::new(&l);
        let state = fitting::Bundle::new(&e, &mut b).unwrap();
        let gs = groups::groups(&e, &state, &mut b).unwrap();
        assert_eq!(gs.first().map_or(0, |g| g.atoms.len()), expected);
        if repeat {
            assert!(gs.iter().all(|g| !g.atoms.contains(&third)));
        }
        let got = e
            .check(
                &keys(&c),
                &CheckOptions {
                    split_depth: 3,
                    ..Default::default()
                },
            )
            .unwrap();
        crate::sat_probe::completion_query::tests::scale::same_report(
            &got,
            &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
        );
    }
}
#[test]
fn processing_substitutions_cannot_certify_an_assumption_group() {
    let (c, mut e, _) = fixture(true, false, false);
    let extra = c.relations().find(|r| r.name == "extra").unwrap().id;
    let index = e.program.atom_index[&GroundAtom::new(extra, [])];
    // Simulate a narrower processing/H view. The assumption still has its
    // second live producer in its own equations, so it cannot certify AMO.
    Arc::make_mut(&mut e.cone).fixed[index] = Some(false);
    let limits = e.limits.clone();
    let mut budget = Budget::new(&limits);
    let state = fitting::Bundle::new(&e, &mut budget).unwrap();
    assert!(groups::groups(&e, &state, &mut budget).unwrap().is_empty());
}
#[test]
fn rest_preserves_other_values_and_absence_and_can_split_again() {
    for absent in [false, true] {
        let (mut c, _, _) = fixture(false, false, false);
        let input = c.relations().find(|r| r.name == "value").unwrap().id;
        let vs: Vec<_> = c.constants().map(|a| a.id).collect();
        let s = c.constants().next().unwrap().sort;
        let p = rel(&mut c, "safe", false);
        let q = rel(&mut c, "ready", false);
        emit(&mut c, p, &[(input, Some(vs[0]), true)]);
        emit(&mut c, p, &[(input, Some(vs[0]), false), (q, None, true)]);
        emit(&mut c, q, &[(input, Some(vs[0]), false)]);
        emit(&mut c, q, &[(input, Some(vs[0]), true), (p, None, false)]);
        // Keep the residual value-c loop inside the original targeted SCC. A
        // rest child may split it again; unrelated loops are residual-checked.
        let cycle = c.relations().find(|r| r.name == "p").unwrap().id;
        emit(
            &mut c,
            p,
            &[(input, Some(vs[0]), true), (cycle, None, true)],
        );
        emit(
            &mut c,
            cycle,
            &[(input, Some(vs[0]), true), (p, None, true)],
        );
        if absent {
            let bad = rel(&mut c, "absent_bad", false);
            let mut body: Vec<_> = vs.iter().map(|v| (input, Some(*v), false)).collect();
            body.push((bad, None, false));
            emit(&mut c, bad, &body);
        }
        let v = c.verifications().next().unwrap().id;
        let e = prepare(&c, v, &[(s, vs)].into());
        let options = CheckOptions {
            split_depth: 4,
            split_branches: 16,
            ..Default::default()
        };
        let got = e.check(&keys(&c), &options).unwrap();
        crate::sat_probe::completion_query::tests::scale::same_report(
            &got,
            &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
        );
        assert!(got.meaning.no_meaning.exists());
        let mut forced = e.clone();
        forced.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
        assert!(matches!(
            test_partition(&forced, false, true, &options).unwrap(),
            Search::Exists(())
        ));
        // A real search may return the first failing value before visiting rest.
        // Exercise rest directly without pinning which witness ranking chooses.
        let mut budget = Budget::new(&e.limits);
        let state = fitting::Bundle::new(&e, &mut budget).unwrap();
        let group = groups::groups(&e, &state, &mut budget).unwrap().remove(0);
        let first = e.program.atom_index
            [&GroundAtom::new(input, [c.constants().find(|x| x.name == "a").unwrap().id])];
        let rest = Choice {
            group,
            selected: vec![first],
            rest: true,
            score: 0,
            binary: false,
            formula: None,
            child_targets: vec![],
            child_states: vec![],
        }
        .children()
        .pop()
        .unwrap()
        .0;
        let child = state.child(&rest, &mut budget).unwrap();
        assert_eq!(child.cone.value(first), Some(false));
        assert!(
            choose(
                &e,
                &child,
                false,
                true,
                16,
                &mut e.config.clone(),
                &mut vec![],
                &mut 0,
                &mut budget
            )
            .unwrap()
            .is_some()
        );
    }
}
#[test]
fn incremental_propagation_matches_fresh_and_does_not_rescan_unrelated_rules() {
    let (mut c, e, _) = fixture(false, false, false);
    let v = e.verification;
    for n in 0..4000 {
        let p = rel(&mut c, &format!("unrelated{n}"), false);
        rule(&mut c, p, &[]);
    }
    let s = c.constants().next().unwrap().sort;
    let vs = c.constants().map(|a| a.id).collect();
    let e = prepare(&c, v, &[(s, vs)].into());
    let limits = e.limits.clone();
    let mut b = Budget::new(&limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let inputs: Vec<_> = e
        .cone
        .input
        .iter()
        .enumerate()
        .filter_map(|(i, v)| v.then_some(i))
        .collect();
    for mask in 0..1 << inputs.len() {
        let pins: Vec<_> = inputs
            .iter()
            .enumerate()
            .map(|(n, i)| (*i, mask & (1 << n) != 0))
            .collect();
        let start = b.used();
        let child = root.child(&pins, &mut b).unwrap();
        let propagation = b.used() - start;
        let mut fresh = (*e.cone).clone();
        for (i, v) in &pins {
            fresh.fixed[*i] = Some(*v)
        }
        let start = b.used();
        let expected = encoding::fitting(&fresh, &mut b).unwrap();
        let fresh_work = b.used() - start;
        assert_eq!(child.cone.values_for_test(), expected);
        assert!(propagation < fresh_work);
        assert!(Arc::ptr_eq(
            &root.cone.index_for_test(),
            &child.cone.index_for_test()
        ));
    }
}

fn emit(
    c: &mut Corpus,
    h: denotate_ir::RelationId,
    body: &[(
        denotate_ir::RelationId,
        Option<denotate_ir::ConstantId>,
        bool,
    )],
) {
    let head = c.atom(h, []).unwrap();
    let body: Vec<_> = body
        .iter()
        .map(|(r, v, p)| {
            let a = c.atom(*r, v.map(Term::Constant)).unwrap();
            if *p {
                Literal::Positive(a)
            } else {
                Literal::Negative(a)
            }
        })
        .collect();
    c.add_rule(head, body).unwrap();
}

#[test]
fn branch_solvers_inherit_the_absolute_question_deadline() {
    let (_, e, _) = fixture(false, false, false);
    let mut options = CheckOptions::default();
    options.split_depth = 2;
    let seen = std::cell::Cell::new(None);
    let result = partition(&e, false, true, &options, 1, |branch, _| {
        let deadline = branch.limits.run_deadline.expect("absolute deadline");
        if let Some(old) = seen.get() {
            assert_eq!(old, deadline);
        } else {
            seen.set(Some(deadline));
        }
        let limits = branch.limits.clone();
        let mut b = Budget::new(&limits);
        let mut q = queries::Run::local(branch, &mut b)?;
        assert_eq!(q.cnf.solver.cb().deadline, Some(deadline));
        q.cnf.solver.cb_mut().deadline = Some(Instant::now());
        assert!(matches!(q.raw_solve(&[]), Err(CheckError::Deadline { .. })));
        Ok(Search::<()>::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
    assert!(seen.get().is_some());
}

#[test]
fn cutting_one_component_does_not_hide_an_unaffected_odd_loop() {
    let (mut c, e, _) = fixture(false, false, false);
    let v = e.verification;
    let bad = rel(&mut c, "independent", false);
    rule(&mut c, bad, &[(bad, true)]);
    let s = c.constants().next().unwrap().sort;
    let vs = c.constants().map(|a| a.id).collect();
    let e = prepare(&c, v, &[(s, vs)].into());
    let got = e
        .check(
            &keys(&c),
            &CheckOptions {
                split_depth: 3,
                ..Default::default()
            },
        )
        .unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(got.meaning.no_meaning.exists());
}
#[test]
fn expired_partition_does_not_start_pending_units() {
    let (_, mut e, _) = fixture(false, false, false);
    e.limits.run_deadline = Some(Instant::now());
    let result = run::<()>(
        &e,
        false,
        true,
        &CheckOptions {
            split_depth: 2,
            ..Default::default()
        },
        1,
        |_, _| panic!("expired unit started"),
    )
    .unwrap();
    assert!(matches!(result, Search::Inconclusive(_)));
}

#[test]
fn ranking_uses_edges_per_extra_child_with_deterministic_ties() {
    fn candidate(edges: usize, children: usize) -> Choice {
        Choice {
            group: Group {
                atoms: (0..children).collect(),
                exact: true,
                assumption: None,
                mapping: vec![],
            },
            selected: (0..children).collect(),
            rest: false,
            score: edges,
            binary: false,
            formula: None,
            child_targets: vec![],
            child_states: vec![],
        }
    }
    assert!(candidate(12, 3).rank(&candidate(5, 2)).is_gt());
    assert!(candidate(12, 3).rank(&candidate(6, 2)).is_gt());
    assert!(candidate(3, 2).rank(&candidate(12, 6)).is_gt());
    assert!(
        candidate(usize::MAX, 2)
            .rank(&candidate(usize::MAX, 3))
            .is_gt()
    );
}
#[test]
fn unsplit_proofs_and_counterexamples_return_without_partitioning() {
    let (_, e, _) = fixture(false, false, false);
    for counterexample in [false, true] {
        let calls = std::cell::Cell::new(0);
        let got = run(
            &e,
            false,
            true,
            &CheckOptions {
                split_depth: 3,
                ..Default::default()
            },
            1,
            |b, o| {
                calls.set(calls.get() + 1);
                assert_eq!(o.split_depth, 0);
                assert!(b.limits.run_deadline.is_some());
                Ok(if counterexample {
                    Search::Exists("confirmed")
                } else {
                    Search::None
                })
            },
        )
        .unwrap();
        assert_eq!(calls.get(), 1);
        assert_eq!(got.exists(), counterexample);
    }
}
#[test]
fn inconclusive_unsplit_attempt_reserves_allowances_and_keeps_the_outer_deadline() {
    let (_, mut e, _) = fixture(false, false, false);
    let calls = std::cell::Cell::new(0);
    let first = std::cell::Cell::new(None);
    let end = Instant::now() + e.limits.timeout;
    e.limits.run_deadline = Some(end);
    let got = run(
        &e,
        false,
        true,
        &CheckOptions {
            split_depth: 3,
            ..Default::default()
        },
        1,
        |b, _| {
            let i = calls.get();
            calls.set(i + 1);
            if i == 0 {
                first.set(Some((
                    b.limits.max_work,
                    b.config.max_solver_polls,
                    b.limits.run_deadline.unwrap(),
                )));
                Ok(Search::Inconclusive(
                    inconclusive(CheckError::limit("test unsplit", "work", 1, Some(2))).unwrap(),
                ))
            } else {
                let (work, polls, deadline) = first.get().unwrap();
                assert!(work + b.limits.max_work <= e.limits.max_work);
                assert!(polls + b.config.max_solver_polls <= e.config.max_solver_polls);
                assert!(b.limits.run_deadline.unwrap() >= deadline);
                assert!(b.limits.run_deadline.unwrap() <= end);
                Ok(Search::Exists("confirmed"))
            }
        },
    )
    .unwrap();
    assert!(matches!(got, Search::Exists("confirmed")));
    assert!(calls.get() > 1);
}

#[test]
fn ranking_counts_edges_across_components_and_reports_the_runner_up_within_the_cap() {
    let (mut c, _, _) = fixture(false, false, false);
    let input = c.relations().find(|r| r.name == "value").unwrap().id;
    let vs: Vec<_> = c.constants().map(|a| a.id).collect();
    let sort = c.constants().next().unwrap().sort;
    let guard = rel(&mut c, "two_values", false);
    for v in &vs[..2] {
        emit(&mut c, guard, &[(input, Some(*v), true)]);
    }
    for n in 0..3 {
        let r = rel(&mut c, &format!("loop{n}"), false);
        emit(&mut c, r, &[(guard, None, true), (r, None, false)]);
    }
    let v = c.verifications().next().unwrap().id;
    let e = prepare(&c, v, &[(sort, vs)].into());
    for cap in [2, 3] {
        let mut b = Budget::new(&e.limits);
        let state = fitting::Bundle::new(&e, &mut b).unwrap();
        let branch = state.engine(&e, &mut b).unwrap();
        let mut telemetry = vec![];
        let (winner, runner) = choose(
            &branch,
            &state,
            false,
            true,
            cap,
            &mut e.config.clone(),
            &mut telemetry,
            &mut 0,
            &mut b,
        )
        .unwrap()
        .unwrap();
        assert!(winner.child_count() <= cap);
        let chosen = telemetry.iter().find(|t| t.selected).unwrap();
        assert_eq!(chosen.checked_children, winner.child_count());
        assert!(chosen.disabled_edges > 0);
        if cap == 3 {
            assert!(runner.is_some());
            // Influence alone used to prefer three children; verified cuts can
            // prefer the cheaper two-child partition instead.
            assert!(
                telemetry
                    .iter()
                    .any(|r| r.children == 3 && r.checked_children == 3)
            );
        }
    }
}

#[test]
fn unsplit_progress_does_not_leak_into_the_following_question() {
    let (_, mut e, _) = fixture(false, false, false);
    let seen = Arc::new(std::sync::Mutex::new(vec![]));
    let output = seen.clone();
    e.limits.progress =
        crate::CheckingProgress::new(move |event| output.lock().unwrap().push(event));
    run(
        &e,
        false,
        true,
        &CheckOptions {
            split_depth: 2,
            ..Default::default()
        },
        1,
        |_, _| Ok(Search::<()>::None),
    )
    .unwrap();
    e.limits
        .progress
        .failure(&CheckError::limit("next question", "work", 0, Some(1)));
    let events = seen.lock().unwrap();
    assert!(
        events
            .iter()
            .any(|e| matches!(e.target, Some(crate::CheckingTarget::CompletionBranch(_))))
    );
    assert!(events.last().unwrap().target.is_none());
}

#[test]
fn cyclic_provider_decoy_cannot_beat_a_guard_that_cuts_every_child() {
    let mut c = Corpus::new();
    let decoy = rel(&mut c, "a_catch_all", true);
    let real = rel(&mut c, "z_format", true);
    let guard = rel(&mut c, "guard", false);
    let p = rel(&mut c, "accepted", false);
    let q = rel(&mut c, "ready", false);
    // Old provider traversal reached catch_all via guard -> accepted, but
    // catch_all alone cannot settle any member of this cycle.
    rule(&mut c, guard, &[(p, false), (decoy, false)]);
    rule(&mut c, guard, &[(p, false), (decoy, true)]);
    rule(&mut c, p, &[(real, false)]);
    rule(&mut c, p, &[(real, true), (q, false), (guard, false)]);
    rule(&mut c, q, &[(real, true)]);
    rule(&mut c, q, &[(real, false), (p, true), (guard, false)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let mut b = Budget::new(&e.limits);
    let state = fitting::Bundle::new(&e, &mut b).unwrap();
    let ix = |r| e.program.atom_index[&GroundAtom::new(r, [])];
    for value in [false, true] {
        let child = state.cone.child(&[(ix(decoy), value)], &mut b).unwrap();
        assert!(child.edge_live(ix(p), ix(q), false, &mut b).unwrap());
        assert!(child.edge_live(ix(q), ix(p), true, &mut b).unwrap());
    }
    let mut rows = vec![];
    let (winner, _) = choose(
        &e,
        &state,
        false,
        true,
        16,
        &mut e.config.clone(),
        &mut rows,
        &mut 0,
        &mut b,
    )
    .unwrap()
    .unwrap();
    assert_eq!(e.cone.atoms[winner.selected[0]].relation, real);
    let chosen = rows.iter().find(|r| r.selected).unwrap();
    assert!(chosen.cycles_cut_every_child > 0);
    assert!(rows.iter().all(|r| r.split.relation != decoy));
    let opts = CheckOptions {
        split_depth: 3,
        ..Default::default()
    };
    crate::sat_probe::completion_query::tests::scale::same_report(
        &e.check(&keys(&c), &opts).unwrap(),
        &e.check_enumerated(&keys(&c), &opts).unwrap(),
    );
    assert!(matches!(
        test_partition(&e, false, true, &opts).unwrap(),
        Search::None
    ));
}

#[test]
fn parallel_producer_preserves_an_edge_until_all_its_guards_die() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, p, &[(j, false), (p, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let ix = |r| e.program.atom_index[&GroundAtom::new(r, [])];
    let mut b = Budget::new(&e.limits);
    let state = fitting::State::new(e.cone.clone(), &mut b).unwrap();
    let first = state.child(&[(ix(i), false)], &mut b).unwrap();
    assert!(first.edge_live(ix(p), ix(p), true, &mut b).unwrap());
    let both = first.child(&[(ix(j), false)], &mut b).unwrap();
    assert!(!both.edge_live(ix(p), ix(p), true, &mut b).unwrap());
}

#[test]
fn inherited_h_view_never_replaces_w_in_classification_fallback() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let h = rel(&mut c, "h", false);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(p, true)]);
    rule(&mut c, h, &[(i, false), (p, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.pruning = Some(Arc::new(std::sync::Mutex::new(pruning::Cache::for_engine(
        &e,
    ))));
    let class = &*e.classification.as_ref().unwrap().0;
    let w = pruning::view(&e, class, false, e.limits.timeout).unwrap();
    let hview = pruning::view(&e, class, true, e.limits.timeout).unwrap();
    assert!(hview.rules.len() < w.rules.len() || hview.fixed != w.fixed);
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let ix = e.program.atom_index[&GroundAtom::new(i, [])];
    for value in [false, true] {
        let state = root.child(&[(ix, value)], &mut b).unwrap();
        assert_eq!(state.ranking(true, true).1, "W+H");
        let branch = state.engine(&e, &mut b).unwrap();
        let cone = &*branch.classification.as_ref().unwrap().0;
        let actual_w = pruning::view(&branch, cone, false, Duration::ZERO).unwrap();
        let actual_h = pruning::view(&branch, cone, true, Duration::ZERO).unwrap();
        assert!(*actual_w.rules == *w.rules);
        assert!(*actual_h.rules == *hview.rules);
        assert!(
            branch
                .pruning
                .as_ref()
                .unwrap()
                .lock()
                .unwrap()
                .report
                .records
                .is_empty()
        );
    }
    let opts = CheckOptions {
        prune: true,
        split_depth: 3,
        ..Default::default()
    };
    assert!(matches!(
        test_partition(&e, true, true, &opts).unwrap(),
        Search::Exists(())
    ));
    crate::sat_probe::completion_query::tests::scale::same_report(
        &e.check(&keys(&c), &opts).unwrap(),
        &e.check_enumerated(&keys(&c), &opts).unwrap(),
    );
}

#[test]
fn tentative_fitting_rejects_a_high_influence_tautological_guard() {
    let mut c = Corpus::new();
    let decoy = rel(&mut c, "a_input", true);
    let real = rel(&mut c, "z_input", true);
    let guard = rel(&mut c, "tautology", false);
    rule(&mut c, guard, &[(decoy, false)]);
    rule(&mut c, guard, &[(decoy, true)]);
    for n in 0..4 {
        let p = rel(&mut c, &format!("self_support{n}"), false);
        rule(&mut c, p, &[(guard, false), (p, false)]);
    }
    // Positive cycle: locally nonunique, but i=false breaks it.
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(real, false), (q, false)]);
    rule(&mut c, q, &[(p, false)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let mut b = Budget::new(&e.limits);
    let state = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut rows = vec![];
    let (winner, _) = choose(
        &e,
        &state,
        false,
        false,
        16,
        &mut e.config.clone(),
        &mut rows,
        &mut 0,
        &mut b,
    )
    .unwrap()
    .unwrap();
    assert_eq!(e.cone.atoms[winner.selected[0]].relation, real);
    let decoy = rows.iter().find(|r| r.split.relation == decoy).unwrap();
    assert_eq!(decoy.checked_children, decoy.children);
    assert_eq!(decoy.disabled_edges, 0);
    assert!(!decoy.selected);
    assert!(rows.iter().find(|r| r.selected).unwrap().disabled_edges > 0);
}

#[test]
fn no_useful_partition_runs_an_inconclusive_question_only_once() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "input_independent_cycle", false);
    rule(&mut c, p, &[(p, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let calls = std::cell::Cell::new(0);
    let options = CheckOptions {
        split_depth: 3,
        ..Default::default()
    };
    let cause = inconclusive(CheckError::deadline("test query", Duration::ZERO)).unwrap();
    let answer: Search<()> = run(&e, false, true, &options, 1, |_, _| {
        calls.set(calls.get() + 1);
        Ok(Search::Inconclusive(cause))
    })
    .unwrap();
    assert!(matches!(answer, Search::Inconclusive(_)));
    assert_eq!(
        calls.get(),
        1,
        "no fallback reruns the same unsplit question"
    );
}

#[test]
fn uncut_child_is_residual_checked_and_retains_its_real_failure() {
    let (c, mut e, _) = fixture(false, false, false);
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    let options = CheckOptions {
        split_depth: 4,
        ..Default::default()
    };
    let answer = test_partition(&e, false, true, &options).unwrap();
    assert!(answer.exists());
    assert!(
        e.check_enumerated(&keys(&c), &options)
            .unwrap()
            .meaning
            .no_meaning
            .exists()
    );
    let report = e.branches.as_ref().unwrap().lock().unwrap();
    assert!(report.records.iter().any(|r| r.state == "split"));
    assert!(
        report
            .records
            .iter()
            .any(|r| r.depth == 1 && r.state == "counterexample"),
        "the child retaining the self-negative cycle is checked, not discarded or recursively explored"
    );
}

#[test]
fn automatic_guards_survive_division_but_explicit_caps_and_deadlines_do_not_change() {
    let (_, mut e, _) = fixture(false, false, false);
    let end = Instant::now() + Duration::from_secs(1);
    e.limits.run_deadline = Some(end);
    e.limits.max_work = 7;
    e.config = QueryLimits {
        max_solves: 3,
        max_solver_polls: 5,
        max_conflicts: 7,
        max_propagations: 11,
    };
    let mut options = CheckOptions {
        max_worlds: 2,
        ..Default::default()
    };
    e.limits.search_guards = Some(crate::SearchGuards {
        work: Some(100_000),
        polls: Some(200_000),
        worlds: Some(100),
        ..Default::default()
    });
    guards(&mut e, &mut options);
    assert_eq!(e.limits.max_work, 100_000);
    assert_eq!(e.config.max_solver_polls, 200_000);
    assert_eq!(options.max_worlds, 100);
    assert_eq!(e.config.max_solves, 3);
    assert_eq!(e.config.max_conflicts, 7);
    assert_eq!(e.config.max_propagations, 11);
    assert_eq!(e.limits.run_deadline, Some(end));
    // A public/API caller with no automatic policy keeps every divided cap.
    e.limits.search_guards = None;
    e.config = divided(&e.config, 1000);
    guards(&mut e, &mut options);
    assert_eq!(e.config.max_solves, 0);
}

#[test]
fn closing_a_target_component_does_not_explore_an_unrelated_loop() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let mut b = Budget::new(&e.limits);
    let state = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut remaining = e.config.clone();
    let (choice, _) = choose(
        &e,
        &state,
        false,
        true,
        8,
        &mut remaining,
        &mut vec![],
        &mut 0,
        &mut b,
    )
    .unwrap()
    .unwrap();
    let n = choice
        .child_targets
        .iter()
        .position(|t| !t.is_empty())
        .unwrap();
    let child = state.child(&choice.children()[n].0, &mut b).unwrap();
    assert!(
        ranking::choose_in(
            &e,
            &child,
            false,
            true,
            8,
            Some(&choice.child_targets[n]),
            &mut remaining,
            &mut vec![],
            &mut 0,
            &mut b
        )
        .unwrap()
        .is_none()
    );
    assert!(
        choose(
            &e,
            &child,
            false,
            true,
            8,
            &mut remaining,
            &mut vec![],
            &mut 0,
            &mut b
        )
        .unwrap()
        .is_some(),
        "the unrelated loop still exists"
    );
    let branch = child.engine(&e, &mut b).unwrap();
    assert!(
        branch
            .symbolic_no_meaning_in(&BTreeMap::new(), false, false, &CheckOptions::default(), 1)
            .unwrap()
            .exists(),
        "residual checking still reports its failure"
    );
}
