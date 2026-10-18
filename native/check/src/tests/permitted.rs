use super::rewrites::{rel, stable_models, subsets};
use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

fn fixture() -> (Corpus, Domains, RelationId, Vec<GroundAtom>) {
    let mut c = Corpus::new();
    let sort = c.declare_sort("Value").unwrap();
    let values: Vec<_> = ["one", "two", "other"]
        .iter()
        .map(|n| c.declare_constant(*n, sort).unwrap())
        .collect();
    let r = c
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", sort)])
        .unwrap();
    let atoms = values.iter().map(|v| GroundAtom::new(r, [*v])).collect();
    (c, Domains::from([(sort, values)]), r, atoms)
}
fn add(c: &mut Corpus, head: RelationId, body: &[(GroundAtom, bool)]) {
    let h = c.atom(head, []).unwrap();
    let b: Vec<_> = body
        .iter()
        .map(|(a, n)| {
            let atom = c
                .atom(a.relation, a.arguments.iter().copied().map(Term::Constant))
                .unwrap();
            if *n {
                Literal::Negative(atom)
            } else {
                Literal::Positive(atom)
            }
        })
        .collect();
    c.add_rule(h, b).unwrap();
}
fn prepare(c: &Corpus, d: &Domains, r: RelationId) -> GroundProgram {
    GroundProgram::prepare_with_input_groups(
        c,
        d,
        &[InputAtMostOne {
            relation: r,
            group_by: vec![],
        }],
        &Limits::default(),
    )
    .unwrap()
}
#[test]
fn exclusive_input_worlds_queries_witnesses_and_replay_agree() {
    let (c, d, r, a) = fixture();
    let limits = Limits::default();
    let p = prepare(&c, &d, r);
    let ctx = p.condition_context(&limits).unwrap();
    let x = ctx.input(&a[0], &limits).unwrap();
    let y = ctx.input(&a[1], &limits).unwrap();
    assert!(!ctx.may_overlap(&x, &y, &limits).unwrap());
    assert!(
        ctx.implies(&x, &ctx.not(&y, &limits).unwrap(), &limits)
            .unwrap()
    );
    // Raw algebra still represents impossible input combinations.
    let both = ctx.and(&x, &y, &limits).unwrap();
    assert!(both.can_hold());
    assert!(
        ctx.equivalent(&both, &ctx.false_condition(), &limits)
            .unwrap()
    );
    assert!(ctx.witness(&both, &limits).unwrap().is_none());
    for world in subsets(&a) {
        let valid = world.len() <= 1;
        assert_eq!(p.evaluate(world.iter().cloned(), &limits).is_ok(), valid);
        let result = ctx.evaluate(&ctx.permitted_worlds(), world.iter().cloned(), &limits);
        if valid {
            assert!(result.unwrap());
            for sub in subsets(&world.iter().cloned().collect::<Vec<_>>()) {
                assert!(p.evaluate(sub, &limits).is_ok());
            }
        } else {
            assert!(result.is_err());
        }
    }
    let observation = ctx.witness(&x, &limits).unwrap().unwrap();
    let next = ctx
        .present_dont_cares(&x, &observation, &mut crate::limits::Budget::new(&limits))
        .unwrap();
    assert_eq!(next.present, BTreeSet::from([a[0].clone()]));
    assert!(p.evaluate(next.present, &limits).is_ok());
    let raw = GroundProgram::prepare(&c, &d, &limits).unwrap();
    assert!(raw.evaluate(a.clone(), &limits).is_ok());
    assert!(
        raw.condition_context(&limits)
            .unwrap()
            .permitted_worlds()
            .is_true()
    );
}
#[test]
fn mutually_exclusive_cycles_discharge_only_under_w_and_preserve_stable_models() {
    let (mut c, d, r, a) = fixture();
    let limits = Limits::default();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    add(
        &mut c,
        p,
        &[(a[0].clone(), false), (GroundAtom::new(q, []), true)],
    );
    add(
        &mut c,
        q,
        &[(a[1].clone(), false), (GroundAtom::new(p, []), true)],
    );
    let raw = GroundProgram::prepare(&c, &d, &limits).unwrap();
    assert!(!raw.clone().admit(&limits).unwrap().is_admitted());
    let admitted = prepare(&c, &d, r).admit(&limits).unwrap();
    assert!(admitted.is_admitted());
    assert_eq!(admitted.rewrite_proofs().count(), 2);
    let inputs = raw.input_atoms().cloned().collect();
    let atoms = raw.atoms().cloned().collect::<Vec<_>>();
    let rules = raw.rules().cloned().collect::<Vec<_>>();
    for world in subsets(&a).into_iter().filter(|w| w.len() <= 1) {
        let expected = stable_models(&atoms, &inputs, &rules, &world);
        assert_eq!(expected.len(), 1);
        let replay = admitted.evaluate(world, &limits).unwrap();
        assert_eq!(
            BTreeSet::from([replay.established_facts().cloned().collect::<BTreeSet<_>>()]),
            expected
        );
    }
}
#[test]
fn completion_excludes_impossible_worlds_but_keeps_every_permitted_world() {
    for unconditional in [false, true] {
        let (mut c, d, r, a) = fixture();
        let limits = Limits::default();
        let p = rel(&mut c, "p", false);
        let mut body = if unconditional {
            vec![]
        } else {
            vec![(a[0].clone(), false), (a[1].clone(), false)]
        };
        body.push((GroundAtom::new(p, []), true));
        add(&mut c, p, &body);
        let ground = prepare(&c, &d, r);
        let m = ground.symbolic(&limits).unwrap();
        let report = m.verify_at_most_one(&limits).unwrap();
        match &report.unresolved[0].completion {
            CompletionOutcome::NoMeaning(f) if unconditional => assert!(
                m.context()
                    .equivalent(&f.bad_input, &m.context().permitted_worlds(), &limits)
                    .unwrap()
            ),
            CompletionOutcome::NoContradiction if !unconditional => {}
            other => panic!("{other:?}"),
        }
    }
}
#[test]
fn input_group_validation_and_budgets_are_explicit() {
    let (mut c, d, r, _) = fixture();
    let derived = rel(&mut c, "derived", false);
    let limits = Limits::default();
    for constraint in [
        InputAtMostOne {
            relation: derived,
            group_by: vec![],
        },
        InputAtMostOne {
            relation: r,
            group_by: vec![1],
        },
        InputAtMostOne {
            relation: r,
            group_by: vec![0, 0],
        },
    ] {
        assert!(matches!(
            GroundProgram::prepare_with_input_groups(&c, &d, &[constraint], &limits),
            Err(CheckError::InvalidInputGroup(_))
        ));
    }
    let p = prepare(&c, &d, r);
    for constrained in [
        Limits {
            max_work: 0,
            ..limits.clone()
        },
        Limits {
            max_bdd_nodes: 2,
            ..limits.clone()
        },
        Limits {
            max_condition_nodes: 2,
            ..limits.clone()
        },
    ] {
        assert!(matches!(
            p.condition_context(&constrained),
            Err(CheckError::LimitExceeded { .. })
        ));
    }
}

#[test]
fn producer_coverage_uses_w_without_changing_authored_stable_models() {
    let (mut c, d, r, a) = fixture();
    let limits = Limits::default();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    add(
        &mut c,
        p,
        &[(a[0].clone(), false), (GroundAtom::new(q, []), true)],
    );
    add(
        &mut c,
        q,
        &[(a[1].clone(), false), (GroundAtom::new(p, []), true)],
    );
    add(&mut c, p, &[(a[1].clone(), true)]);
    let raw = GroundProgram::prepare(&c, &d, &limits).unwrap();
    assert!(!raw.clone().admit(&limits).unwrap().is_admitted());
    let admitted = prepare(&c, &d, r).admit(&limits).unwrap();
    assert!(admitted.is_admitted());
    assert!(
        admitted
            .rewrite_proofs()
            .any(|p| p.kind == RewriteKind::RedundantProducer)
    );
    let atoms = raw.atoms().cloned().collect::<Vec<_>>();
    let inputs = raw.input_atoms().cloned().collect();
    let rules = raw.rules().cloned().collect::<Vec<_>>();
    for world in subsets(&a).into_iter().filter(|w| w.len() <= 1) {
        let expected = stable_models(&atoms, &inputs, &rules, &world);
        assert_eq!(expected.len(), 1);
        assert_eq!(
            expected,
            BTreeSet::from([admitted
                .evaluate(world, &limits)
                .unwrap()
                .established_facts()
                .cloned()
                .collect()])
        );
    }
}

#[test]
fn universal_permitted_failure_is_not_a_vacuous_overlap_qualifier() {
    let (mut c, d, r, a) = fixture();
    let limits = Limits::default();
    let p = rel(&mut c, "p", false);
    add(&mut c, p, &[(GroundAtom::new(p, []), true)]);
    let sort = c.relation(r).unwrap().parameters[0].sort;
    let result = c
        .declare_relation("result", RelationRole::Derived, [Parameter::new("v", sort)])
        .unwrap();
    for atom in &a[..2] {
        let head = c.atom(result, [Term::Constant(atom.arguments[0])]).unwrap();
        c.add_rule(head, []).unwrap();
    }
    c.at_most_one("unique", result, [], "unique").unwrap();
    let ground = prepare(&c, &d, r).admit(&limits).unwrap();
    let m = ground.symbolic(&limits).unwrap();
    let report = m.verify_at_most_one(&limits).unwrap();
    let CompletionOutcome::NoMeaning(f) = &report.unresolved[0].completion else {
        panic!()
    };
    assert!(!f.bad_input.is_true());
    assert!(
        m.context()
            .equivalent(&f.bad_input, &m.context().permitted_worlds(), &limits)
            .unwrap()
    );
    let VerifiedOutcome::Counterexample(example) = &report.groups[0].outcome else {
        panic!()
    };
    assert!(example.confined_to_no_meaning.is_empty());
    assert!(example.observation.present.len() <= 1);
    assert!(ground.certify_observation(a.clone(), &limits).is_err());
}

#[test]
fn settled_input_negations_cannot_discharge_each_others_assumptions() {
    let (mut c, d, r, a) = fixture();
    let sort = c.relation(r).unwrap().parameters[0].sort;
    let s = c
        .declare_relation("second", RelationRole::Input, [Parameter::new("v", sort)])
        .unwrap();
    let b: Vec<_> = a
        .iter()
        .map(|v| GroundAtom::new(s, v.arguments.clone()))
        .collect();
    let g = rel(&mut c, "guard", false);
    let h = rel(&mut c, "head", false);
    // Within W the guard means a[0] == b[0]. The last two alternatives
    // distinguish them only outside W, so each negation appears individually
    // W-redundant if the other negation is retained.
    for body in [
        vec![(a[0].clone(), false), (b[0].clone(), false)],
        vec![(a[0].clone(), true), (b[0].clone(), true)],
        vec![(a[0].clone(), false), (a[1].clone(), false)],
        vec![(b[0].clone(), false), (b[1].clone(), false)],
    ] {
        add(&mut c, g, &body);
    }
    add(
        &mut c,
        h,
        &[
            (GroundAtom::new(g, []), false),
            (a[0].clone(), true),
            (b[0].clone(), true),
        ],
    );
    let limits = Limits::default();
    let raw = GroundProgram::prepare_with_input_groups(
        &c,
        &d,
        &[
            InputAtMostOne {
                relation: r,
                group_by: vec![],
            },
            InputAtMostOne {
                relation: s,
                group_by: vec![],
            },
        ],
        &limits,
    )
    .unwrap();
    let admitted = raw.clone().admit(&limits).unwrap();
    assert_eq!(admitted.rewrite_proofs().count(), 1);
    let atoms = raw.atoms().cloned().collect::<Vec<_>>();
    let inputs = raw.input_atoms().cloned().collect();
    let rules = raw.rules().cloned().collect::<Vec<_>>();
    for x in subsets(&a).into_iter().filter(|w| w.len() <= 1) {
        for y in subsets(&b).into_iter().filter(|w| w.len() <= 1) {
            let world = x.union(&y).cloned().collect();
            let expected = stable_models(&atoms, &inputs, &rules, &world);
            assert_eq!(expected.len(), 1);
            assert_eq!(
                expected,
                BTreeSet::from([admitted
                    .evaluate(world, &limits)
                    .unwrap()
                    .established_facts()
                    .cloned()
                    .collect()])
            );
        }
    }
}
