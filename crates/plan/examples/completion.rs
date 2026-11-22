//! Run with `just plan-completion-example`: export, then execute both outcomes.
use denotate_check::{AtomKey, Domains, GroundAtom, Limits};
use denotate_ir::*;
use denotate_plan::{
    Options, Order, Output,
    completion::{Build, Planner},
};
use std::collections::{BTreeMap, BTreeSet};
fn main() {
    let mut c = Corpus::new();
    let mut keys = SemanticKeys::default();
    let mut relation = |name, role| {
        let r = c.declare_relation(name, role, []).unwrap();
        keys.bind_relation(
            &c,
            r,
            RelationKey::Named(QualifiedKey::new("example", name)),
        )
        .unwrap();
        r
    };
    let raw = relation("ready", RelationRole::Input);
    let h = relation("accepted", RelationRole::Derived);
    let result = relation("result", RelationRole::Derived);
    for (name, head, positive) in [("accept", h, true), ("result", result, false)] {
        let head = c.atom(head, []).unwrap();
        let body = c.atom(raw, []).unwrap();
        let rule = c
            .add_rule(
                head,
                [if positive {
                    Literal::Positive(body)
                } else {
                    Literal::Negative(body)
                }],
            )
            .unwrap();
        keys.bind_rule(
            &c,
            rule,
            RuleKey::Library(QualifiedKey::new("example", name)),
        )
        .unwrap();
    }
    for rule in c.rules() {
        let key = keys.rule(rule.id).unwrap().clone();
        for (i, a) in std::iter::once(&rule.head)
            .chain(rule.body.iter().map(Literal::atom))
            .enumerate()
        {
            keys.bind_occurrence(
                &c,
                a.id(),
                OccurrenceKey::Library {
                    rule: key.clone(),
                    atom: i,
                    argument: None,
                },
            )
            .unwrap();
        }
    }
    let v = c
        .verification_with_options_in(
            Namespace::new(["example"]).unwrap(),
            "checks",
            [],
            [],
            [],
            VerificationOptions {
                semantics: Semantics::Completion,
                hypothesis: Some(h),
                decisions: Some(BTreeSet::from([result])),
            },
        )
        .unwrap();
    keys.bind_verification(
        &c,
        v,
        VerificationKey(QualifiedKey::new("example", "checks")),
    )
    .unwrap();
    let planner = Planner::prepare(
        &c,
        &Domains::new(),
        &keys,
        v,
        &Limits::default(),
        Default::default(),
    )
    .unwrap();
    let Build::Ready(plan) = planner
        .build(
            &[Output {
                atom: GroundAtom::new(result, []),
                priority: 0,
            }],
            &Options::default(),
        )
        .unwrap()
    else {
        panic!("expected a complete plan")
    };
    println!("{}", serde_json::to_string_pretty(&plan.to_json()).unwrap());
    for value in [false, true] {
        let input = BTreeMap::from([(
            AtomKey::from_atom(&keys, &GroundAtom::new(raw, [])).unwrap(),
            value,
        )]);
        for order in [
            Order::Semantic,
            Order::ReverseSemantic,
            Order::OutputPriority,
        ] {
            let run = plan.execute_permitted(&input, order, 1000).unwrap();
            println!("ready={value}, {order:?}: {:?}", run.outcome);
        }
    }
}
