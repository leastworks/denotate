use super::*;

fn task(name: &str, when: Option<RelationId>, args: &[RelationId], results: &[RelationId]) -> Task {
    Task {
        key: QualifiedKey::new("tasks", name),
        when: when.map(atom),
        arguments: args.iter().map(|r| atom(*r)).collect(),
        results: results.iter().map(|r| atom(*r)).collect(),
        sources: BTreeSet::new(),
    }
}
fn key(k: &SemanticKeys, r: RelationId) -> AtomKey {
    AtomKey::from_atom(k, &atom(r)).unwrap()
}
fn model_matches(
    c: &Corpus,
    k: &SemanticKeys,
    entry: &BTreeMap<AtomKey, bool>,
    execution: &Execution,
) {
    let g = GroundProgram::prepare(c, &Domains::new(), &Limits::default()).unwrap();
    let mut observation = entry.clone();
    for t in &execution.tasks {
        observation.extend(t.results.clone());
    }
    let inputs: BTreeSet<_> = g.input_atoms().cloned().collect();
    let world = inputs
        .iter()
        .filter(|a| observation.get(&AtomKey::from_atom(k, a).unwrap()) == Some(&true))
        .cloned()
        .collect();
    let models = stable_models(
        &g.atoms().cloned().collect::<Vec<_>>(),
        &inputs,
        &g.rules().cloned().collect::<Vec<_>>(),
        &world,
    );
    assert_eq!(models.len(), 1);
    for (a, v) in &execution.outputs {
        assert_eq!(
            *v,
            models
                .first()
                .unwrap()
                .iter()
                .any(|b| AtomKey::from_atom(k, b).unwrap() == *a)
        );
    }
}

#[test]
fn task_outputs_are_produced_not_entry_inputs_and_callbacks_are_checked() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let r = rel(&mut c, "r", true);
    let out = rel(&mut c, "out", false);
    rule(&mut c, out, &[(r, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let tasks = vec![task("flip", None, &[x], &[r])];
    let mut p = planner(&c, &k, v);
    let plan = ready(
        p.build_with_tasks(&outputs(&[out]), &tasks, &Options::default())
            .unwrap(),
    );
    assert_eq!(
        plan,
        ready(
            p.build_with_tasks(&outputs(&[out]), &tasks, &Options::default())
                .unwrap()
        )
    );
    assert_eq!(
        plan,
        ready(
            planner(&c, &k, v)
                .build_with_tasks(&outputs(&[out]), &tasks, &Options::default())
                .unwrap()
        )
    );
    assert_eq!(plan.inputs(), &BTreeSet::from([key(&k, x)]));
    assert_eq!(plan.produced_inputs(), &BTreeSet::from([key(&k, r)]));
    assert_eq!(plan.to_json()["version"], 4);
    assert!(
        plan.to_json()["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n["operation"]["kind"] == "call")
    );
    for value in [false, true] {
        let entry = BTreeMap::from([(key(&k, x), value)]);
        for order in [
            Order::Semantic,
            Order::ReverseSemantic,
            Order::OutputPriority,
        ] {
            let mut calls = 0;
            let e = plan
                .execute_with_tasks(&entry, order, 1000, &mut |inv| {
                    calls += 1;
                    assert_eq!(inv.arguments, vec![(key(&k, x), value)]);
                    Ok(BTreeMap::from([(key(&k, r), !value)]))
                })
                .unwrap();
            assert_eq!(calls, 1);
            assert_eq!(e.outputs[&key(&k, out)], value);
            model_matches(&c, &k, &entry, &e);
        }
        assert!(matches!(
            plan.execute_permitted(&entry, Order::Semantic, 1000),
            Err(ExecutionError::TaskCallbackRequired)
        ));
        assert!(matches!(
            plan.execute_with_tasks(&entry, Order::Semantic, 1000, &mut |_| Ok(BTreeMap::new())),
            Err(ExecutionError::InvalidTaskResults(_))
        ));
        assert!(matches!(
            plan.execute_with_tasks(&entry, Order::Semantic, 1000, &mut |_| Err("failed".into())),
            Err(ExecutionError::TaskFailed(_, _))
        ));
        let mut spoof = entry;
        spoof.insert(key(&k, r), true);
        assert!(matches!(
            plan.execute_with_tasks(&spoof, Order::Semantic, 1000, &mut |_| panic!(
                "must not run"
            )),
            Err(ExecutionError::ProducedInputAtEntry(_))
        ));
    }
}

#[test]
fn opposite_task_orders_and_multi_result_calls_agree_with_oracle() {
    let mut c = Corpus::new();
    let d = rel(&mut c, "direction", true);
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", true);
    let extra = rel(&mut c, "a_extra", true);
    let b = rel(&mut c, "b", true);
    let ai = rel(&mut c, "a_arg", false);
    let bi = rel(&mut c, "b_arg", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, ai, &[(d, false), (x, false)]);
    rule(&mut c, ai, &[(d, true), (b, false)]);
    rule(&mut c, bi, &[(d, true), (x, false)]);
    rule(&mut c, bi, &[(d, false), (a, false)]);
    rule(&mut c, out, &[(extra, false), (b, false)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let tasks = vec![
        task("a", None, &[ai], &[a, extra]),
        task("b", None, &[bi], &[b]),
    ];
    let mut p = planner(&c, &k, v);
    let plan = ready(
        p.build_with_tasks(&outputs(&[a, b, out]), &tasks, &Options::default())
            .unwrap(),
    );
    assert!(plan.to_json()["size"]["branches"].as_u64().unwrap() > 0);
    assert_eq!(
        plan,
        ready(
            p.build_with_tasks(&outputs(&[a, b, out]), &tasks, &Options::default())
                .unwrap()
        )
    );
    for direction in [false, true] {
        for value in [false, true] {
            let entry = BTreeMap::from([(key(&k, d), direction), (key(&k, x), value)]);
            for order in [
                Order::Semantic,
                Order::ReverseSemantic,
                Order::OutputPriority,
            ] {
                let e = plan
                    .execute_with_tasks(&entry, order, 10000, &mut |inv| {
                        let v = inv.arguments[0].1;
                        Ok(inv.results.iter().map(|k| (k.clone(), !v)).collect())
                    })
                    .unwrap();
                assert_eq!(e.tasks.len(), 2);
                assert_eq!(
                    e.tasks[0].task.name.as_ref(),
                    if direction { "a" } else { "b" }
                );
                assert_eq!(
                    e.tasks
                        .iter()
                        .map(|t| t.task.clone())
                        .collect::<BTreeSet<_>>()
                        .len(),
                    2
                );
                model_matches(&c, &k, &entry, &e);
            }
        }
    }
}

#[test]
fn inactive_task_does_not_read_unavailable_arguments_or_call_and_true_cycle_is_unresolved() {
    let mut c = Corpus::new();
    let no = rel(&mut c, "no", false);
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let tasks = vec![task("a", Some(no), &[b], &[a]), task("b", None, &[a], &[b])];
    let mut p = planner(&c, &k, v);
    let plan = ready(
        p.build_with_tasks(&outputs(&[a, b]), &tasks, &Options::default())
            .unwrap(),
    );
    let e = plan
        .execute_with_tasks(&BTreeMap::new(), Order::ReverseSemantic, 1000, &mut |inv| {
            assert_eq!(inv.task.name.as_ref(), "b");
            assert!(!inv.arguments[0].1);
            Ok(inv.results.iter().map(|k| (k.clone(), true)).collect())
        })
        .unwrap();
    assert!(!e.outputs[&key(&k, a)]);
    assert!(e.outputs[&key(&k, b)]);
    assert!(!e.tasks[0].invoked);
    assert!(e.tasks[1].invoked);
    model_matches(&c, &k, &BTreeMap::new(), &e);
    let cyclic = vec![task("a", None, &[b], &[a]), task("b", None, &[a], &[b])];
    assert!(matches!(
        p.build_with_tasks(&outputs(&[a, b]), &cyclic, &Options::default())
            .unwrap(),
        Build::Problem(Problem::Unresolved { .. })
    ));
}

#[test]
fn task_metadata_expands_original_scope_and_edits_invalidate_preparation() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let r = rel(&mut c, "r", true);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, bad, &[(bad, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    let good = vec![task("produce", None, &[x], &[r])];
    let old = ready(
        p.build_with_tasks(&outputs(&[r]), &good, &Options::default())
            .unwrap(),
    );
    let bad_task = vec![task("produce", None, &[bad], &[r])];
    assert!(matches!(
        p.build_with_tasks(&outputs(&[r]), &bad_task, &Options::default())
            .unwrap(),
        Build::Problem(Problem::Meaning(_))
    ));
    assert_eq!(
        old,
        ready(
            p.build_with_tasks(&outputs(&[r]), &good, &Options::default())
                .unwrap()
        )
    );
    let plain = ready(p.build(&outputs(&[r]), &Options::default()).unwrap());
    assert!(plain.produced_inputs().is_empty());
    assert!(plain.inputs().contains(&key(&k, r)));
}

#[test]
fn task_validation_and_bounds_never_publish_partial_plans() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let r = rel(&mut c, "r", true);
    let d = rel(&mut c, "derived", false);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    for ts in [
        vec![task("t", None, &[x], &[])],
        vec![task("t", None, &[x], &[d])],
        vec![task("t", None, &[x], &[r, r])],
        vec![task("a", None, &[], &[r]), task("b", None, &[], &[r])],
    ] {
        assert!(
            p.build_with_tasks(&outputs(&[r]), &ts, &Options::default())
                .is_err()
        );
        assert!(p.scope().is_none());
    }
    let task = vec![task("t", None, &[x], &[r])];
    let options = Options {
        max_nodes: 0,
        ..Options::default()
    };
    assert!(matches!(
        p.build_with_tasks(&outputs(&[r]), &task, &options).unwrap(),
        Build::Inconclusive(_)
    ));
    let plan = ready(
        p.build_with_tasks(&outputs(&[r]), &task, &Options::default())
            .unwrap(),
    );
    assert!(matches!(
        plan.execute_with_tasks(&BTreeMap::new(), Order::Semantic, 0, &mut |_| panic!()),
        Err(ExecutionError::WorkLimit)
    ));
}

#[test]
fn w_pinned_result_still_requires_its_call_and_relational_kernels_remain_pure() {
    let mut c = Corpus::new();
    let r = rel(&mut c, "result", true);
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, false)]);
    rule(&mut c, a, &[(b, false)]);
    rule(&mut c, b, &[(a, false)]);
    let assumption = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "required", r, [])
        .unwrap();
    let v = verification(&mut c, &[assumption]);
    let k = keys(&c);
    let ts = vec![task("pinned", None, &[b], &[r])];
    let plan = ready(
        planner(&c, &k, v)
            .build_with_tasks(&outputs(&[r]), &ts, &Options::default())
            .unwrap(),
    );
    assert!(
        plan.nodes()
            .values()
            .any(|n| matches!(n.operation, Operation::Call { .. }))
    );
    assert!(
        plan.nodes()
            .values()
            .any(|n| matches!(n.operation, Operation::Fixpoint { .. }))
    );
    let e = plan
        .execute_with_tasks(
            &BTreeMap::from([(key(&k, x), false)]),
            Order::Semantic,
            1000,
            &mut |inv| {
                assert!(!inv.arguments[0].1);
                Ok(BTreeMap::from([(key(&k, r), true)]))
            },
        )
        .unwrap();
    assert_eq!(e.tasks.len(), 1);
    assert!(e.tasks[0].invoked);
    assert!(e.outputs[&key(&k, r)]);
}

#[test]
fn runtime_guard_skips_callback_and_unused_task_does_not_import_a_paradox() {
    let mut c = Corpus::new();
    let guard = rel(&mut c, "guard", true);
    let x = rel(&mut c, "x", true);
    let r = rel(&mut c, "r", true);
    let unused = rel(&mut c, "unused", true);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, bad, &[(bad, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let ts = vec![
        task("used", Some(guard), &[x], &[r]),
        task("unused", None, &[bad], &[unused]),
    ];
    let mut p = planner(&c, &k, v);
    let plan = ready(
        p.build_with_tasks(&outputs(&[r]), &ts, &Options::default())
            .unwrap(),
    );
    assert!(!plan.produced_inputs().contains(&key(&k, unused)));
    let mut reversed = ts.clone();
    reversed.reverse();
    assert_eq!(
        plan,
        ready(
            p.build_with_tasks(&outputs(&[r]), &reversed, &Options::default())
                .unwrap()
        )
    );
    for enabled in [false, true] {
        for value in [false, true] {
            let entry = BTreeMap::from([(key(&k, guard), enabled), (key(&k, x), value)]);
            let e = plan
                .execute_with_tasks(&entry, Order::Semantic, 1000, &mut |inv| {
                    assert!(enabled);
                    assert_eq!(inv.task.name.as_ref(), "used");
                    Ok(BTreeMap::from([(key(&k, r), inv.arguments[0].1)]))
                })
                .unwrap();
            assert_eq!(e.outputs[&key(&k, r)], enabled && value);
            assert_eq!(e.tasks.len(), 1);
            assert_eq!(e.tasks[0].invoked, enabled);
        }
    }
}
