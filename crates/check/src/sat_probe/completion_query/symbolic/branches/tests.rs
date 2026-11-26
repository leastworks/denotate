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
fn branch_solvers_inherit_their_sibling_share_deadline() {
    let (_, mut e, _) = fixture(false, false, false);
    let mut options = CheckOptions::default();
    options.split_depth = 2;
    let seen = std::cell::Cell::new(None);
    let outer = Instant::now() + e.limits.timeout;
    e.limits.run_deadline = Some(outer);
    let result = partition(&e, false, true, &options, 1, |branch, _| {
        let deadline = branch.limits.run_deadline.expect("absolute deadline");
        if let Some(old) = seen.get() {
            assert!(old < deadline, "later sibling keeps its own share");
        }
        seen.set(Some(deadline));
        assert!(deadline <= outer);
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
    for existence in [false, true] {
        for counterexample in [false, true] {
            let calls = std::cell::Cell::new(0);
            let got = run(
                &e,
                false,
                existence,
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
}
#[test]
fn inconclusive_unsplit_attempt_reserves_allowances_and_keeps_the_outer_deadline() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(i, false), (p, false)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    let calls = std::cell::Cell::new(0);
    let first = std::cell::Cell::new(None);
    let end = Instant::now() + e.limits.timeout;
    e.limits.run_deadline = Some(end);
    let got = run(
        &e,
        false,
        false,
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
    let mut e = prepare(&c, v, &[(sort, vs)].into());
    // The runner-up is reported only when every shortlisted candidate is tried.
    e.limits.completion_full_shortlist = true;
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
fn closing_a_target_component_still_ranks_an_untouched_loop() {
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
            Some(&choice.residual_only(n)),
            &mut remaining,
            &mut vec![],
            &mut 0,
            &mut b
        )
        .unwrap()
        .is_some()
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

#[test]
fn exploration_finishes_shortlisted_trials_without_the_wall_clock_floor() {
    let (c, mut e, _) = fixture(false, false, false);
    // The normal ranking quarter is below its 500 ms trial-start floor.
    // This is an eligibility check, not a timing/performance assertion.
    e.limits.timeout = Duration::from_secs(1);
    let state = fitting::Bundle::new(&e, &mut Budget::new(&e.limits)).unwrap();
    let normal = choose(
        &e,
        &state,
        false,
        true,
        512,
        &mut e.config.clone(),
        &mut vec![],
        &mut 0,
        &mut Budget::new(&e.limits),
    )
    .unwrap();
    assert!(normal.is_none());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    let state = fitting::Bundle::new(&e, &mut Budget::new(&e.limits)).unwrap();
    let mut telemetry = vec![];
    let mut omitted = 0;
    let selected = choose(
        &e,
        &state,
        false,
        true,
        512,
        &mut e.config.clone(),
        &mut telemetry,
        &mut omitted,
        &mut Budget::new(&e.limits),
    )
    .unwrap();
    assert!(selected.is_some());
    assert!(telemetry.iter().any(|t| t.state == "verified"));
    assert!(
        telemetry
            .iter()
            .all(|t| t.state == "verified" || t.state == "not-shortlisted")
    );
    let opts = CheckOptions {
        split_depth: 3,
        prune: false,
        force: false,
        ..Default::default()
    };
    let got = e.check(&keys(&c), &opts).unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(got.branches.splits > 0);
    // Neither an initial solve nor earlier branches may silently erase the
    // confirmed no-meaning observation in the remaining child.
    assert!(got.meaning.no_meaning.exists());
}

#[test]
fn exploration_ranks_the_root_and_both_subtrees_before_residual_search() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    let seen = std::cell::Cell::new(0);
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    // Test the scheduler separately from leaf semantics: do not stop at the
    // first failing observation, so both one-sided subtrees must be ranked.
    let result: Search<()> = run(&e, false, true, &options, 1, |b, _| {
        let ii = b.program.atom_index[&GroundAtom::new(i, [])];
        let jj = b.program.atom_index[&GroundAtom::new(j, [])];
        assert!(
            b.cone.fixed[ii].is_some() && b.cone.fixed[jj].is_some(),
            "a residual search ran before a useful split"
        );
        seen.set(seen.get() + 1);
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
    assert_eq!(seen.get(), 4);
    assert_eq!(
        e.branches
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .records
            .iter()
            .filter(|r| r.depth == 1 && r.state == "split")
            .count(),
        2
    );
}

#[test]
fn exploration_defers_leaf_searches_until_structural_work_is_done() {
    // `p :- i, !p` and `q :- j, !i, !q`: splitting on i leaves the i-true child
    // with only p's loop and nothing to split (a leaf at depth 1), while the
    // i-false child still splits on j. The early leaf must not search first.
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (i, true), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    let calls = std::cell::RefCell::new(vec![]);
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    let result: Search<()> = run(&e, false, true, &options, 1, |b, _| {
        let ii = b.program.atom_index[&GroundAtom::new(i, [])];
        let jj = b.program.atom_index[&GroundAtom::new(j, [])];
        calls
            .borrow_mut()
            .push((b.cone.fixed[ii], b.cone.fixed[jj]));
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
    let calls = calls.into_inner();
    let early = (Some(true), None);
    assert!(
        calls.contains(&early),
        "the i-true child is a depth-1 leaf: {calls:?}"
    );
    assert_ne!(
        calls[0], early,
        "a leaf searched before structural work ended"
    );
    let report = e.branches.as_ref().unwrap().lock().unwrap();
    let deferred: Vec<_> = report
        .records
        .iter()
        .filter(|r| r.state == "leaf-deferred")
        .collect();
    assert!(!deferred.is_empty());
    // Ranking ran there and found nothing: the record says why and which cycle.
    let gap = deferred[0].ranking_gap.as_ref().expect("ranking gap");
    assert!(gap.targets > 0 || gap.reason == "no-target");
    assert!(
        gap.witness.contains(&GroundAtom::new(p, [])),
        "witness {:?} ({})",
        gap.witness,
        gap.reason
    );
    assert!(
        report
            .records
            .iter()
            .any(|r| r.depth == 1 && r.state == "split")
    );
}

#[test]
fn deferred_leaves_stay_inconclusive_when_the_deadline_arrives_first() {
    // Same shape as the deferral test: two leaves wait while the last structural
    // unit searches. That search outlasts the deadline, so the waiting leaves
    // are never checked and the question stays inconclusive.
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (i, true), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    e.limits.timeout = Duration::from_millis(3000);
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    let calls = std::cell::Cell::new(0);
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    let result: Search<()> = run(&e, false, true, &options, 1, |b, _| {
        calls.set(calls.get() + 1);
        // Outlast the unit's own deadline, whatever the runner's load: no
        // fixed sleep has to beat a fixed timeout.
        let deadline = b.limits.run_deadline.expect("leaf deadline");
        while Instant::now() <= deadline {
            std::thread::sleep(Duration::from_millis(20));
        }
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::Inconclusive(_)));
    // On a heavily loaded runner the deadline may even fire before any leaf
    // search starts; either way no leaf is searched after it.
    assert!(calls.get() <= 1, "deferred leaves ran after the deadline");
    let report = e.branches.as_ref().unwrap().lock().unwrap();
    assert!(report.pending_units > 0);
    if calls.get() == 1 {
        assert!(report.records.iter().any(|r| r.state == "leaf-deferred"));
    }
}

#[test]
fn resumed_leaf_work_reduces_the_next_leaf_allowance() {
    // Three leaves (one searched at once, two resumed). Each search charges
    // 100,000 work to its counter; every later leaf must see that consumed.
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (i, true), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    e.limits.max_work = 1_000_000;
    let allowances = std::cell::RefCell::new(vec![]);
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    let result: Search<()> = run(&e, false, true, &options, 1, |b, _| {
        allowances.borrow_mut().push(b.limits.max_work);
        b.exploration_work
            .as_ref()
            .expect("leaf work counter")
            .fetch_add(100_000, std::sync::atomic::Ordering::Relaxed);
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
    let allowances = allowances.into_inner();
    assert_eq!(allowances.len(), 3, "{allowances:?}");
    for pair in allowances.windows(2) {
        assert!(
            pair[1] + 100_000 <= pair[0],
            "a leaf reused work an earlier leaf consumed: {allowances:?}"
        );
    }
}

#[test]
fn exploration_probe_closes_questions_before_ranking_or_forcing() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(i, false)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    let options = CheckOptions {
        prune: true,
        force: true,
        split_depth: 3,
        ..Default::default()
    };
    let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
    let got = e.check(&keys(&c), &options).unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(&got, &expected);
    assert!(
        got.branches
            .records
            .iter()
            .any(|r| r.phase == "completion unsplit probe" && r.state == "completed")
    );
    assert_eq!(got.branches.splits, 0);
    assert!(
        got.branches
            .records
            .iter()
            .all(|r| r.candidates.is_empty() && r.forcing.is_empty())
    );
}

#[test]
fn exploration_probe_cutoff_is_charged_and_leaves_the_structural_driver_available() {
    let (c, mut e, _) = fixture(false, false, false);
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 1;
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
    assert!(
        got.branches
            .records
            .iter()
            .any(|r| r.phase == "completion unsplit probe" && r.state == "cut-off")
    );
    assert!(got.branches.splits > 0);
    assert!(got.meaning.no_meaning.exists());
}

#[test]
fn default_classification_existence_splits_before_cover_search() {
    let (mut c, _, _) = fixture(false, false, false);
    let p = c.relations().find(|r| r.name == "p").unwrap().id;
    let input = c.relations().find(|r| r.name == "value").unwrap().id;
    let values: Vec<_> = c.constants().map(|v| v.id).collect();
    let sort = c.constants().next().unwrap().sort;
    let assumption = c.assumptions().next().unwrap().id;
    let v = verification(&mut c, Some(p), &[assumption]);
    let e = prepare(&c, v, &[(sort, values.clone())].into());
    let third = e.program.atom_index[&GroundAtom::new(input, [values[2]])];
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    let result: Search<()> = run(&e, true, true, &options, 1, |branch, _| {
        assert!(
            branch.cone.fixed[third].is_some(),
            "cover ran before its cutting split"
        );
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
}

#[test]
fn exploration_existence_probe_reports_a_counterexample_found_by_its_cover() {
    let (_, mut e, _) = fixture(false, false, false);
    e.limits.completion_exploration = true;
    e.probe = true;
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let result = e
        .symbolic_no_meaning(false, true, &Default::default(), 1)
        .unwrap();
    assert!(matches!(result, Search::Exists(_)));
}

/// `p :- value(c), !p` and `p :- value(c)`: the negative self-loop keeps an odd
/// component, so no structural certificate applies, yet p = value(c) always has a
/// model. A short cover proves existence inside the probe.
fn covered_odd_loop() -> (Corpus, Engine) {
    let (mut c, _, _) = fixture(false, false, false);
    let p = c.relations().find(|r| r.name == "p").unwrap().id;
    let input = c.relations().find(|r| r.name == "value").unwrap().id;
    let third = c.constants().nth(2).unwrap().id;
    let head = c.atom(p, []).unwrap();
    let source = c.atom(input, [Term::Constant(third)]).unwrap();
    c.add_rule(head, [Literal::Positive(source)]).unwrap();
    let values: Vec<_> = c.constants().map(|v| v.id).collect();
    let sort = c.constants().next().unwrap().sort;
    let assumption = c.assumptions().next().unwrap().id;
    let v = verification(&mut c, None, &[assumption]);
    let e = prepare(&c, v, &[(sort, values)].into());
    (c, e)
}

#[test]
fn exploration_existence_probe_proves_a_short_cover_and_skips_structure() {
    let (c, mut e) = covered_odd_loop();
    let mut probe = e.clone();
    probe.limits.completion_exploration = true;
    probe.probe = true;
    let sizes = crate::CompletionSizes::default();
    probe.limits.completion_sizes = Some(sizes.clone());
    let result = probe
        .symbolic_no_meaning(false, true, &Default::default(), 1)
        .unwrap();
    assert!(matches!(result, Search::None));
    assert!(
        sizes
            .snapshot()
            .searches
            .iter()
            .any(|s| s.existence.rounds > 0),
        "the odd component needed a cover"
    );
    e.limits.completion_exploration = true;
    let options = CheckOptions {
        force: true,
        prune: true,
        split_depth: 2,
        ..Default::default()
    };
    let got = e.check(&keys(&c), &options).unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(!got.meaning.no_meaning.exists());
    assert_eq!(got.branches.splits, 0, "a completed probe skips structure");
    assert!(
        got.branches
            .records
            .iter()
            .filter(|r| r.phase == "completion unsplit probe")
            .all(|r| r.state == "completed")
    );
}

#[test]
fn exhausted_existence_probe_is_charged_and_never_a_proof() {
    let (c, mut e) = covered_odd_loop();
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 1;
    let got = e
        .check(
            &keys(&c),
            &CheckOptions {
                split_depth: 2,
                ..Default::default()
            },
        )
        .unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    let probes: Vec<_> = got
        .branches
        .records
        .iter()
        .filter(|r| r.phase == "completion unsplit probe")
        .collect();
    assert!(!probes.is_empty());
    assert!(probes.iter().all(|r| r.state == "cut-off" && r.work > 0));
}

/// Probe existence with an explicit work cap: the answer, cover rounds started,
/// and the work charged to the probe's question.
fn capped_existence_probe(e: &Engine, cap: usize) -> (Search<Observation>, usize, usize) {
    let mut probe = e.clone();
    probe.limits.completion_exploration = true;
    probe.probe = true;
    probe.limits.max_work = cap;
    let sizes = crate::CompletionSizes::default();
    probe.limits.completion_sizes = Some(sizes.clone());
    let work = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    probe.exploration_work = Some(work.clone());
    let result = probe
        .symbolic_no_meaning(false, true, &Default::default(), 1)
        .unwrap();
    let rounds = sizes
        .snapshot()
        .searches
        .iter()
        .map(|s| s.existence.rounds)
        .sum();
    (
        result,
        rounds,
        work.load(std::sync::atomic::Ordering::Relaxed),
    )
}

#[test]
fn probe_exhausted_inside_its_cover_stays_inconclusive_and_charged() {
    let (c, e) = covered_odd_loop();
    let (complete, rounds, full) = capped_existence_probe(&e, usize::MAX);
    assert!(matches!(complete, Search::None) && rounds > 0);
    // Work is deterministic, so cover progress is monotone in the cap. Find the
    // smallest cap that starts covering; no work count is asserted.
    let (mut lo, mut hi) = (1, full);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if capped_existence_probe(&e, mid).1 > 0 {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let (result, started, charged) = capped_existence_probe(&e, lo);
    assert!(started > 0);
    assert!(
        matches!(result, Search::Inconclusive(_)),
        "the cover finished within its first round; the fixture needs more rounds"
    );
    assert!(charged > 0);
    let mut explore = e.clone();
    explore.limits.completion_exploration = true;
    explore.limits.completion_probe_work = lo;
    let got = explore
        .check(
            &keys(&c),
            &CheckOptions {
                split_depth: 2,
                ..Default::default()
            },
        )
        .unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(
        got.branches
            .records
            .iter()
            .any(|r| r.phase == "completion unsplit probe" && r.state == "cut-off" && r.work > 0)
    );
}

#[test]
fn exploration_rejection_probe_covers_hypothesis_models_within_its_cap() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(h, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.probe = true;
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let result = e.symbolic_rejected(&Default::default(), 1).unwrap();
    assert!(matches!(result, Search::None));
    assert!(
        sizes
            .snapshot()
            .searches
            .iter()
            .any(|s| s.existence.cubes > 0),
        "the probe settles rejection with its own cover"
    );
    e.probe = false;
    let got = e
        .check(
            &keys(&c),
            &CheckOptions {
                force: true,
                prune: true,
                split_depth: 2,
                ..Default::default()
            },
        )
        .unwrap();
    crate::sat_probe::completion_query::tests::scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(matches!(got.classification.unwrap().rejected, Search::None));
}

/// Odd self-loops `x :- [guard], !x`, one per (name, guard, polarity); `true`
/// means the guard appears negated in the body.
fn guarded_loops(c: &mut Corpus, loops: &[(&str, RelationId, bool)]) {
    for (name, guard, negated) in loops {
        let x = rel(c, name, false);
        rule(c, x, &[(*guard, *negated), (x, true)]);
    }
}

fn rank(e: &Engine) -> (Choice, Vec<SplitCandidate>) {
    let mut b = Budget::new(&e.limits);
    let state = fitting::Bundle::new(e, &mut b).unwrap();
    let branch = state.engine(e, &mut b).unwrap();
    let mut telemetry = vec![];
    let (winner, _) = choose(
        &branch,
        &state,
        false,
        true,
        8,
        &mut e.config.clone(),
        &mut telemetry,
        &mut 0,
        &mut b,
    )
    .unwrap()
    .unwrap();
    (winner, telemetry)
}

#[test]
fn ranking_stops_at_the_first_trial_that_cuts_in_every_child() {
    // i guards two loops of opposite polarity (each child cuts one); j guards one.
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    guarded_loops(&mut c, &[("p", i, false), ("q", i, true), ("r", j, false)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    let (winner, telemetry) = rank(&e);
    let ii = e.program.atom_index[&GroundAtom::new(i, [])];
    assert_eq!(winner.selected, vec![ii]);
    let j_row = telemetry
        .iter()
        .find(|r| r.split == GroundAtom::new(j, []))
        .unwrap();
    assert_eq!(j_row.state, "not-started", "ranking stopped early");
    e.limits.completion_full_shortlist = true;
    let (full, telemetry) = rank(&e);
    assert_eq!(full.selected, vec![ii]);
    let j_row = telemetry
        .iter()
        .find(|r| r.split == GroundAtom::new(j, []))
        .unwrap();
    assert_ne!(
        j_row.state, "not-started",
        "comparison mode tries every candidate"
    );
}

#[test]
fn a_one_sided_trial_is_a_fallback_while_ranking_widens() {
    // a and z each guard three loops, all cut only when false (one-sided, tried
    // first, higher scores); b guards two loops of opposite polarity (cuts in both
    // children). Two higher-scoring fallbacks would hold the top-two prepared
    // child states; the early-stop winner must keep its own.
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let z = rel(&mut c, "z", true);
    let b = rel(&mut c, "b", true);
    guarded_loops(
        &mut c,
        &[
            ("p1", a, false),
            ("p2", a, false),
            ("p3", a, false),
            ("r1", z, false),
            ("r2", z, false),
            ("r3", z, false),
            ("q1", b, false),
            ("q2", b, true),
        ],
    );
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let (winner, telemetry) = rank(&e);
    let bi = e.program.atom_index[&GroundAtom::new(b, [])];
    for one_sided in [a, z] {
        let row = telemetry
            .iter()
            .find(|r| r.split == GroundAtom::new(one_sided, []))
            .unwrap();
        assert_ne!(row.state, "not-started", "the one-sided trials ran first");
    }
    assert_eq!(
        winner.selected,
        vec![bi],
        "the all-child cut wins over the higher-scoring one-sided ones"
    );
    assert_eq!(
        winner.child_states.len(),
        2,
        "the winner keeps its prepared children"
    );
    // With no all-child cut anywhere, the one-sided trial is the fallback.
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    guarded_loops(&mut c, &[("p1", a, false), ("p2", a, false)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let (winner, _) = rank(&e);
    assert_eq!(
        winner.selected,
        vec![e.program.atom_index[&GroundAtom::new(a, [])]]
    );
}

#[test]
fn leaves_run_smallest_residual_first_and_ties_keep_queue_order() {
    let mut leaves = vec![(1, 0, 'a'), (0, 1, 'b'), (1, 2, 'c'), (0, 3, 'd')];
    let mut order = vec![];
    while let Some(x) = pop_smallest(&mut leaves) {
        order.push(x);
    }
    assert_eq!(order, ['b', 'd', 'a', 'c']);
}

#[test]
fn a_large_final_unit_waits_behind_a_smaller_deferred_leaf() {
    // Root splits on i. The i-true child keeps only `p :- i, !p` (size 1) and is
    // deferred first. The i-false child splits on j: j true kills the four-atom
    // loop (size 0); j false, the last structural unit, keeps it (size 4).
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    let q: Vec<_> = (1..=4)
        .map(|n| rel(&mut c, &format!("q{n}"), false))
        .collect();
    rule(&mut c, q[0], &[(j, true), (i, true), (q[1], true)]);
    rule(&mut c, q[1], &[(q[2], false)]);
    rule(&mut c, q[2], &[(q[3], false)]);
    rule(&mut c, q[3], &[(q[0], false)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.limits.completion_exploration = true;
    e.limits.completion_probe_work = 0;
    e.branches = Some(Arc::new(std::sync::Mutex::new(BranchReport::default())));
    let calls = std::cell::RefCell::new(vec![]);
    let options = CheckOptions {
        split_depth: 2,
        ..Default::default()
    };
    let result: Search<()> = run(&e, false, true, &options, 1, |b, _| {
        let ii = b.program.atom_index[&GroundAtom::new(i, [])];
        let jj = b.program.atom_index[&GroundAtom::new(j, [])];
        calls
            .borrow_mut()
            .push((b.cone.fixed[ii], b.cone.fixed[jj]));
        Ok(Search::None)
    })
    .unwrap();
    assert!(matches!(result, Search::None));
    let calls = calls.into_inner();
    assert_eq!(
        calls,
        [
            (Some(false), Some(true)),
            (Some(true), None),
            (Some(false), Some(false)),
        ],
        "leaves by residual size: 0, 1, 4"
    );
}
