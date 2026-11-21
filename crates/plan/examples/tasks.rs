//! A condition-dependent order: left then right, or right then left.
//! Run with `just plan-task-example`. The callbacks are pure Boolean functions.
use denotate_check::{Domains, GroundAtom, Limits, stable_query::QueryLimits};
use denotate_ir::*;
use denotate_plan::{Build, Options, Order, Output, Planner, Task};
use std::collections::{BTreeMap, BTreeSet};

fn main() {
    let mut corpus = Corpus::new();
    let mut keys = SemanticKeys::default();
    let mut relation = |name, role| {
        let r = corpus.declare_relation(name, role, []).unwrap();
        keys.bind_relation(
            &corpus,
            r,
            RelationKey::Named(QualifiedKey::new("example", name)),
        )
        .unwrap();
        r
    };
    let forward = relation("forward", RelationRole::Input);
    let seed = relation("seed", RelationRole::Input);
    let left = relation("left", RelationRole::Input);
    let right = relation("right", RelationRole::Input);
    let left_arg = relation("left_argument", RelationRole::Derived);
    let right_arg = relation("right_argument", RelationRole::Derived);
    let mut rule = |name: &str, head, body: &[(RelationId, bool)]| {
        let h = corpus.atom(head, []).unwrap();
        let body = body
            .iter()
            .map(|(r, positive)| {
                let a = corpus.atom(*r, []).unwrap();
                if *positive {
                    Literal::Positive(a)
                } else {
                    Literal::Negative(a)
                }
            })
            .collect::<Vec<_>>();
        let r = corpus.add_rule(h, body).unwrap();
        keys.bind_rule(
            &corpus,
            r,
            RuleKey::Library(QualifiedKey::new("example", name)),
        )
        .unwrap();
    };
    rule("left_first", left_arg, &[(forward, true), (seed, true)]);
    rule("left_second", left_arg, &[(forward, false), (right, true)]);
    rule("right_first", right_arg, &[(forward, false), (seed, true)]);
    rule("right_second", right_arg, &[(forward, true), (left, true)]);
    let v = corpus
        .verification_in(Namespace::new(["example"]).unwrap(), "checks", [], [])
        .unwrap();
    keys.bind_verification(
        &corpus,
        v,
        VerificationKey(QualifiedKey::new("example", "checks")),
    )
    .unwrap();
    let a = |r| GroundAtom::new(r, []);
    let tasks = vec![
        Task {
            key: QualifiedKey::new("example", "left"),
            when: None,
            arguments: vec![a(left_arg)],
            results: vec![a(left)],
            sources: BTreeSet::new(),
        },
        Task {
            key: QualifiedKey::new("example", "right"),
            when: None,
            arguments: vec![a(right_arg)],
            results: vec![a(right)],
            sources: BTreeSet::new(),
        },
    ];
    let mut planner = Planner::prepare(
        &corpus,
        &Domains::new(),
        &keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap();
    let outputs = [left, right].map(|r| Output {
        atom: a(r),
        priority: 0,
    });
    let Build::Ready(plan) = planner
        .build_with_tasks(&outputs, &tasks, &Options::default())
        .unwrap()
    else {
        panic!("example must plan")
    };
    println!("{}", serde_json::to_string_pretty(&plan.to_json()).unwrap());
    let key = |r| denotate_check::AtomKey::from_atom(&keys, &a(r)).unwrap();
    for direction in [false, true] {
        let input = BTreeMap::from([(key(forward), direction), (key(seed), true)]);
        let run = plan
            .execute_with_tasks(&input, Order::Semantic, 10000, &mut |call| {
                Ok(call
                    .results
                    .iter()
                    .map(|k| (k.clone(), !call.arguments[0].1))
                    .collect())
            })
            .unwrap();
        eprintln!(
            "forward={direction}: calls {:?}; left={}, right={}",
            run.tasks
                .iter()
                .map(|e| e.task.name.as_ref())
                .collect::<Vec<_>>(),
            run.outputs[&key(left)],
            run.outputs[&key(right)]
        );
    }
}
