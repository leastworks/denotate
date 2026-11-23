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
        assert!(
            got.branches
                .records
                .iter()
                .any(|r| r.rest && r.state == "split")
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
    let result = run(&e, false, true, &options, 1, |branch, _| {
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
