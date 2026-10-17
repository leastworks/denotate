use denotate_normalize::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
fn leaf(key: usize, variable: bool) -> Expression<&'static str, usize> {
    Expression {
        key,
        kind: ExpressionKind::Leaf {
            payload: "arbitrary DSL leaf",
            arguments: vec![Argument {
                key: key + 1000,
                variable,
            }],
        },
    }
}
fn not(key: usize, e: Expression<&'static str, usize>) -> Expression<&'static str, usize> {
    Expression {
        key,
        kind: ExpressionKind::Not(Box::new(e)),
    }
}
fn pair(
    key: usize,
    a: Expression<&'static str, usize>,
    b: Expression<&'static str, usize>,
    or: bool,
) -> Expression<&'static str, usize> {
    Expression {
        key,
        kind: if or {
            ExpressionKind::Or(Box::new(a), Box::new(b))
        } else {
            ExpressionKind::And(Box::new(a), Box::new(b))
        },
    }
}
fn definition(body: Expression<&'static str, usize>) -> Definition<u8, &'static str, usize> {
    Definition {
        head: Atom {
            key: 999,
            payload: 42,
            arguments: vec![Argument {
                key: 998,
                variable: false,
            }],
        },
        body: Some(body),
    }
}
#[test]
fn cancelled_negations_and_split_heads_have_factual_records_and_plain_value_traits() {
    let d = definition(not(
        0,
        not(1, pair(2, leaf(3, false), leaf(4, false), true)),
    ));
    let r = normalize(&d).unwrap();
    let leaves: Vec<_> = r
        .records()
        .values()
        .flatten()
        .filter(|r| r.kind == OutputKind::Literal)
        .collect();
    assert_eq!(leaves.len(), 2);
    for (i, r) in leaves.iter().enumerate() {
        assert_eq!(r.negations, [0, 1]);
        assert_eq!(r.polarity, Some(Polarity::Positive));
        assert_eq!(r.node, i + 3);
        assert_eq!(r.root, 999);
        assert_eq!(r.alternatives, [i + 3]);
    }
    let heads: Vec<_> = r
        .records()
        .iter()
        .filter(|(_, rs)| rs[0].kind == OutputKind::Head)
        .collect();
    assert_eq!(heads.len(), 2);
    assert_ne!(heads[0].0, heads[1].0);
    for (_, rs) in heads {
        assert_eq!(rs[0].node, 999);
        assert_eq!(rs[0].polarity, None);
    }
    let args: Vec<_> = r
        .records()
        .values()
        .flatten()
        .filter(|r| r.argument == Some(998))
        .collect();
    assert_eq!(args.len(), 2);
    assert_ne!(args[0].alternatives, args[1].alternatives);
    let policy_outer: Vec<_> = leaves
        .iter()
        .map(|r| r.negations.first().copied().unwrap_or(r.node))
        .collect();
    let policy_leaf: Vec<_> = leaves.iter().map(|r| r.node).collect();
    assert_eq!(policy_outer, [0, 0]);
    assert_eq!(policy_leaf, [3, 4]);
    let hash = |v: &Recipe<u8, &str, usize>| {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    };
    assert_eq!(r, r.clone());
    assert_eq!(hash(&r), hash(&r.clone()));
    assert_eq!(r, normalize(&d).unwrap());
}
#[test]
fn helper_definition_resets_use_negation_but_retains_inner_negations() {
    let r = normalize(&definition(not(
        0,
        pair(1, leaf(2, false), not(3, leaf(4, false)), false),
    )))
    .unwrap();
    let records: Vec<_> = r.records().values().flatten().collect();
    let use_record = records
        .iter()
        .find(|r| matches!(r.helper, HelperRole::Use(_)))
        .unwrap();
    assert_eq!(use_record.negations, [0]);
    assert_eq!(use_record.polarity, Some(Polarity::Negative));
    let helper = match use_record.helper {
        HelperRole::Use(h) => h,
        _ => unreachable!(),
    };
    for r in records
        .iter()
        .filter(|r| r.helper == HelperRole::Definition(helper))
    {
        assert!(!r.negations.contains(&0));
    }
    let inner = records
        .iter()
        .find(|r| r.node == 4 && r.kind == OutputKind::Literal)
        .unwrap();
    assert_eq!(inner.negations, [3]);
    assert_eq!(inner.polarity, Some(Polarity::Negative));
}
#[test]
fn helper_capture_rejects_variables_local_to_subexpression_but_allows_ground_helpers() {
    // p :- q and not (r(X) and s(X)); X need not occur in p or q.
    let build = |variable| {
        definition(pair(
            0,
            leaf(1, false),
            not(2, pair(3, leaf(4, variable), leaf(5, variable), false)),
            false,
        ))
    };
    assert_eq!(
        normalize(&build(true)),
        Err(ConstructionError::HelperCapturesVariables { expression: 3 })
    );
    assert!(normalize(&build(false)).is_ok());
    let mixed = definition(pair(
        0,
        leaf(1, true),
        pair(2, leaf(3, false), leaf(4, false), true),
        false,
    ));
    assert!(normalize(&mixed).is_ok());
    // Root OR and double-negation cancellation do not require a helper.
    assert!(
        normalize(&definition(not(
            0,
            not(1, pair(2, leaf(3, true), leaf(4, true), true))
        )))
        .is_ok()
    );
}
#[test]
fn duplicate_input_keys_are_creator_errors() {
    assert_eq!(
        normalize(&definition(pair(0, leaf(1, false), leaf(1, false), false))),
        Err(ConstructionError::DuplicateInputKey(1))
    );
}
#[test]
fn conjunction_of_disjunctions_stays_linear() {
    let mut body = leaf(0, false);
    for i in 0..40 {
        let k = 3 * i + 1;
        body = pair(
            500 + i,
            body,
            pair(k, leaf(k + 1, false), leaf(k + 2, false), true),
            false,
        );
    }
    let r = normalize(&definition(body)).unwrap();
    assert_eq!(
        r.instructions()
            .iter()
            .filter(|i| matches!(i, Instruction::Helper { .. }))
            .count(),
        40
    );
    assert_eq!(
        r.instructions()
            .iter()
            .filter(|i| matches!(i, Instruction::Rule { .. }))
            .count(),
        81
    );
    assert!(r.instructions().len() < 500);
}
