use super::*;
use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets};
use denotate_ir::*;

fn engine(c: &mut Corpus, assumptions: &[AssumptionId]) -> Engine {
    let id = c
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
        id,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
}
fn pin(r: RelationId, value: bool) -> Query {
    Query {
        pins: vec![(atom(r), value)],
        ..Query::default()
    }
}
fn conjunction(a: RelationId, b: RelationId) -> Expression {
    Expression {
        nodes: vec![
            ExpressionNode::Atom(atom(a)),
            ExpressionNode::Atom(atom(b)),
            ExpressionNode::Not(1),
            ExpressionNode::And(vec![0, 2]),
        ],
        root: 3,
    }
}
fn synthesized(a: SynthesisAnswer) -> Expression {
    match a {
        SynthesisAnswer::Expression(e) => e,
        other => panic!("expected expression: {other:?}"),
    }
}
#[test]
fn nonconstant_expression_uses_only_available_values_and_agrees_cold_warm() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(a, false), (b, true)]);
    let mut e = engine(&mut c, &[]);
    let q = Query::default();
    let k = [atom(a), atom(b)];
    let allowance = OracleLimits::default();
    assert!(matches!(
        e.constant(&q, &atom(x), &allowance).unwrap(),
        ConstantAnswer::Varying { .. }
    ));
    let got = synthesized(e.synthesize(&q, &atom(x), &k, &allowance).unwrap());
    assert_eq!(got.dependencies().unwrap(), k.iter().cloned().collect());
    for av in [false, true] {
        for bv in [false, true] {
            assert_eq!(
                got.evaluate(|v| if v == &atom(a) {
                    Some(av)
                } else if v == &atom(b) {
                    Some(bv)
                } else {
                    None
                }),
                Some(av && !bv)
            );
        }
    }
    for expression in [&got, &conjunction(a, b)] {
        assert!(matches!(
            e.equivalent(&q, &atom(x), &k, expression, &allowance)
                .unwrap(),
            EquivalenceAnswer::Equivalent
        ));
    }
    let warm = synthesized(e.synthesize(&q, &atom(x), &k, &allowance).unwrap());
    let mut fresh = engine(&mut c, &[]);
    assert_eq!(got, warm);
    assert_eq!(
        got,
        synthesized(fresh.synthesize(&q, &atom(x), &k, &allowance).unwrap())
    );
    // Availability of a does not pin a true; partial K cannot compute x.
    let SynthesisAnswer::NotDetermined {
        when_true,
        when_false,
    } = e.synthesize(&q, &atom(x), &[atom(a)], &allowance).unwrap()
    else {
        panic!()
    };
    assert_eq!(when_true.value(&atom(a)), when_false.value(&atom(a)));
    assert_eq!(when_true.value(&atom(x)), Some(true));
    assert_eq!(when_false.value(&atom(x)), Some(false));
}
#[test]
fn supplied_expression_is_checked_under_context_and_queries_do_not_leak() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(a, false), (b, true)]);
    let mut e = engine(&mut c, &[]);
    let expression = Expression {
        nodes: vec![ExpressionNode::Atom(atom(a))],
        root: 0,
    };
    let k = [atom(a)];
    let l = OracleLimits::default();
    for _ in 0..2 {
        assert!(matches!(
            e.equivalent(&pin(b, false), &atom(x), &k, &expression, &l)
                .unwrap(),
            EquivalenceAnswer::Equivalent
        ));
        let EquivalenceAnswer::Counterexample(m) = e
            .equivalent(&Query::default(), &atom(x), &k, &expression, &l)
            .unwrap()
        else {
            panic!()
        };
        assert_ne!(m.value(&atom(x)), expression.evaluate(|a| m.value(a)));
        // Excluded cubes are part of C, for both the initial feasibility and mismatch query.
        let q = Query {
            exclude: vec![vec![(atom(b), true)]],
            ..Query::default()
        };
        assert!(matches!(
            e.equivalent(&q, &atom(x), &k, &expression, &l).unwrap(),
            EquivalenceAnswer::Equivalent
        ));
        assert!(matches!(
            e.feasible(&pin(b, true)).unwrap(),
            Answer::Model(_)
        ));
        assert!(matches!(e.worlds(&pin(b, true)).unwrap(), Answer::Model(_)));
    }
}
#[test]
fn infeasibility_is_not_vacuous_constant_or_equivalence_or_no_permitted_worlds() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(a, false), (p, true)]);
    let mut e = engine(&mut c, &[]);
    let q = pin(a, true);
    let l = OracleLimits::default();
    let expression = Expression {
        nodes: vec![ExpressionNode::Constant(true)],
        root: 0,
    };
    assert!(matches!(e.feasible(&q).unwrap(), Answer::NoModel));
    assert!(matches!(
        e.constant(&q, &atom(p), &l).unwrap(),
        ConstantAnswer::Infeasible
    ));
    assert!(matches!(
        e.equivalent(&q, &atom(p), &[], &expression, &l).unwrap(),
        EquivalenceAnswer::Infeasible
    ));
    assert!(matches!(
        e.synthesize(&q, &atom(p), &[], &l).unwrap(),
        SynthesisAnswer::Infeasible
    ));
    assert!(matches!(e.worlds(&q).unwrap(), Answer::Model(_)));
    // A partial no-meaning context is not claimed total by this expression proof.
    assert!(matches!(
        e.constant(&Query::default(), &atom(p), &l).unwrap(),
        ConstantAnswer::Constant(false)
    ));
}
#[test]
fn stable_support_multiple_meanings_and_available_derived_atoms() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let p = rel(&mut c, "p", false);
    let x = rel(&mut c, "x", false);
    rule(&mut c, p, &[(a, false)]);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, x, &[(p, true)]);
    let mut e = engine(&mut c, &[]);
    let l = OracleLimits::default();
    assert!(matches!(
        e.constant(&pin(a, false), &atom(p), &l).unwrap(),
        ConstantAnswer::Constant(false)
    ));
    let expr = synthesized(
        e.synthesize(&Query::default(), &atom(x), &[atom(p)], &l)
            .unwrap(),
    );
    assert_eq!(expr.dependencies().unwrap(), BTreeSet::from([atom(p)]));
    assert!(matches!(
        e.equivalent(&Query::default(), &atom(x), &[atom(p)], &expr, &l)
            .unwrap(),
        EquivalenceAnswer::Equivalent
    ));
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    let mut e = engine(&mut c, &[]);
    assert!(matches!(
        e.synthesize(&Query::default(), &atom(p), &[], &l).unwrap(),
        SynthesisAnswer::NotDetermined { .. }
    ));
    let expr = synthesized(
        e.synthesize(&Query::default(), &atom(p), &[atom(q)], &l)
            .unwrap(),
    );
    assert_eq!(expr.evaluate(|_| Some(true)), Some(false));
    assert_eq!(expr.evaluate(|_| Some(false)), Some(true));
}
#[test]
fn selected_assumptions_are_isolated_a_none_a() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(a, false)]);
    let assumption = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "required", p, [])
        .unwrap();
    for assumptions in [vec![assumption], vec![], vec![assumption]] {
        let mut e = engine(&mut c, &assumptions);
        let l = OracleLimits::default();
        for _ in 0..2 {
            let answer = e.synthesize(&Query::default(), &atom(p), &[], &l).unwrap();
            if assumptions.is_empty() {
                assert!(matches!(answer, SynthesisAnswer::NotDetermined { .. }));
            } else {
                assert_eq!(synthesized(answer).evaluate(|_| None), Some(true));
            }
        }
    }
}
#[test]
fn invalid_expressions_and_unavailable_leaves_are_errors_even_in_empty_contexts() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let mut e = engine(&mut c, &[]);
    let l = OracleLimits::default();
    let q = Query {
        exclude: vec![vec![]],
        ..Query::default()
    };
    for expression in [
        Expression {
            nodes: vec![],
            root: 0,
        },
        Expression {
            nodes: vec![ExpressionNode::Not(0)],
            root: 0,
        },
        Expression {
            nodes: vec![ExpressionNode::Atom(atom(a))],
            root: 0,
        },
    ] {
        assert!(matches!(
            e.equivalent(&q, &atom(a), &[], &expression, &l),
            Err(CheckError::InvalidRequest(_))
        ));
    }
    let invalid = Expression {
        nodes: vec![ExpressionNode::Not(1)],
        root: 0,
    };
    assert_eq!(invalid.evaluate(|_| None), None);
    assert_eq!(invalid.dependencies(), None);
}
#[test]
fn exhaustion_never_becomes_a_proof_and_does_not_contaminate_later_queries() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(a, false), (b, true)]);
    let mut e = engine(&mut c, &[]);
    let q = Query::default();
    let k = [atom(a), atom(b)];
    for l in [
        OracleLimits {
            max_queries: 0,
            ..OracleLimits::default()
        },
        OracleLimits {
            max_branches: 0,
            ..OracleLimits::default()
        },
        OracleLimits {
            max_expression_nodes: 0,
            ..OracleLimits::default()
        },
        OracleLimits {
            max_available: 0,
            ..OracleLimits::default()
        },
    ] {
        assert!(matches!(
            e.synthesize(&q, &atom(x), &k, &l).unwrap(),
            SynthesisAnswer::Inconclusive(_)
        ));
    }
    let expr = synthesized(
        e.synthesize(&q, &atom(x), &k, &OracleLimits::default())
            .unwrap(),
    );
    assert!(matches!(
        e.equivalent(&q, &atom(x), &k, &expr, &OracleLimits::default())
            .unwrap(),
        EquivalenceAnswer::Equivalent
    ));
    e.cache.clear();
    e.config.max_solves = 0;
    assert!(matches!(
        e.constant(&q, &atom(x), &OracleLimits::default()).unwrap(),
        ConstantAnswer::Inconclusive(_)
    ));
    e.config.max_solves = 128;
    e.limits.timeout = std::time::Duration::ZERO;
    assert!(matches!(
        e.synthesize(&q, &atom(x), &k, &OracleLimits::default())
            .unwrap(),
        SynthesisAnswer::Inconclusive(_)
    ));
}
#[test]
fn tiny_original_programs_exhaustively_validate_synthesized_expressions_and_constants() {
    for a in 0..6 {
        for b in 0..6 {
            let mut c = Corpus::new();
            let input = rel(&mut c, "input", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let rs = [input, p, q];
            rule(&mut c, p, &[(rs[a / 2], a % 2 == 1)]);
            rule(&mut c, q, &[(rs[b / 2], b % 2 == 1)]);
            let original =
                GroundProgram::prepare_cartesian(&c, &Domains::new(), &Limits::default()).unwrap();
            let atoms = rs.map(atom);
            let inputs = BTreeSet::from([atom(input)]);
            let rules: Vec<_> = original.rules().cloned().collect();
            let all: Vec<_> = subsets(&[atom(input)])
                .into_iter()
                .flat_map(|world| stable_models(&atoms, &inputs, &rules, &world))
                .collect();
            let mut e = engine(&mut c, &[]);
            let l = OracleLimits::default();
            for context in [Query::default(), pin(input, false), pin(input, true)] {
                let expected: Vec<_> = all
                    .iter()
                    .filter(|m| context.pins.iter().all(|(a, v)| m.contains(a) == *v))
                    .collect();
                for k in [
                    vec![],
                    vec![atom(input)],
                    vec![atom(q)],
                    vec![atom(input), atom(q)],
                ] {
                    let result = e.synthesize(&context, &atom(p), &k, &l).unwrap();
                    match result {
                        SynthesisAnswer::Infeasible => assert!(expected.is_empty()),
                        SynthesisAnswer::Expression(expr) => {
                            assert!(!expected.is_empty());
                            assert!(expr.dependencies().unwrap().iter().all(|a| k.contains(a)));
                            for m in &expected {
                                assert_eq!(
                                    expr.evaluate(|a| Some(m.contains(a))),
                                    Some(m.contains(&atom(p)))
                                );
                            }
                            assert!(matches!(
                                e.equivalent(&context, &atom(p), &k, &expr, &l).unwrap(),
                                EquivalenceAnswer::Equivalent
                            ));
                        }
                        SynthesisAnswer::NotDetermined {
                            when_true,
                            when_false,
                        } => {
                            for a in &k {
                                assert_eq!(when_true.value(a), when_false.value(a));
                            }
                            for (m, v) in [(when_true, true), (when_false, false)] {
                                assert_eq!(m.value(&atom(p)), Some(v));
                                assert!(expected.iter().any(|set| {
                                    atoms.iter().all(|a| m.value(a) == Some(set.contains(a)))
                                }));
                            }
                        }
                        other => panic!("unexpected {other:?}"),
                    }
                }
            }
        }
    }
}

#[test]
fn supplied_boolean_dags_match_an_independent_truth_table() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(a, false), (b, true)]);
    let mut e = engine(&mut c, &[]);
    let k = [atom(a), atom(b)];
    let l = OracleLimits::default();
    let leaves = vec![ExpressionNode::Atom(atom(a)), ExpressionNode::Atom(atom(b))];
    let cases = [
        ExpressionNode::And(vec![]),
        ExpressionNode::Or(vec![]),
        ExpressionNode::And(vec![0, 1]),
        ExpressionNode::Or(vec![0, 1]),
        ExpressionNode::Not(1),
        ExpressionNode::Constant(false),
        ExpressionNode::If {
            atom: atom(a),
            when_true: 0,
            when_false: 1,
        },
    ];
    for tail in cases {
        let mut nodes = leaves.clone();
        nodes.push(tail);
        let expr = Expression { nodes, root: 2 };
        for av in [false, true] {
            for bv in [false, true] {
                let query = Query {
                    pins: vec![(atom(a), av), (atom(b), bv)],
                    exclude: vec![],
                };
                let same = expr
                    .evaluate(|v| Some(if v == &atom(a) { av } else { bv }))
                    .unwrap()
                    == (av && !bv);
                match e.equivalent(&query, &atom(x), &k, &expr, &l).unwrap() {
                    EquivalenceAnswer::Equivalent => assert!(same),
                    EquivalenceAnswer::Counterexample(m) => {
                        assert!(!same);
                        assert_eq!(m.value(&atom(a)), Some(av));
                        assert_eq!(m.value(&atom(b)), Some(bv));
                    }
                    other => panic!("{other:?}"),
                }
            }
        }
    }
}
#[test]
fn oracle_cancellation_and_partial_cnf_emission_are_not_reused_as_proofs() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let x = rel(&mut c, "x", false);
    rule(&mut c, x, &[(a, false), (b, true)]);
    let mut e = engine(&mut c, &[]);
    let k = [atom(a), atom(b)];
    let l = OracleLimits::default();
    let q = Query::default();
    let expr = conjunction(a, b);
    // Prime just feasibility; permit one further selector, then fail in expression encoding.
    assert!(matches!(e.feasible(&q).unwrap(), Answer::Model(_)));
    e.limits.max_atoms = e.cnf.solver.num_vars() as usize + 1;
    assert!(matches!(
        e.equivalent(&q, &atom(x), &k, &expr, &l).unwrap(),
        EquivalenceAnswer::Inconclusive(_)
    ));
    assert!(e.append_failed.is_some());
    e.limits.max_atoms = Limits::default().max_atoms;
    assert!(matches!(
        e.constant(&q, &atom(x), &l).unwrap(),
        ConstantAnswer::Inconclusive(_)
    ));
    let mut e = engine(&mut c, &[]);
    e.limits.cancellation.cancel();
    assert!(matches!(
        e.constant(&q, &atom(x), &l),
        Err(CheckError::Cancelled)
    ));
    assert!(matches!(
        e.equivalent(&q, &atom(x), &k, &expr, &l),
        Err(CheckError::Cancelled)
    ));
    assert!(matches!(
        e.synthesize(&q, &atom(x), &k, &l),
        Err(CheckError::Cancelled)
    ));
}
