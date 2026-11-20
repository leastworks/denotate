use super::*;
use denotate_check::{
    CheckError, Domains, GroundAtom, GroundProgram, Limits,
    stable_query::{Existence, QueryLimits, Uniqueness},
    test_support::rewrites::{atom, rel, rule, stable_models, subsets},
};
use denotate_ir::*;

fn keys(c: &Corpus) -> SemanticKeys {
    let mut k = SemanticKeys::default();
    for r in c.relations() {
        k.bind_relation(
            c,
            r.id,
            RelationKey::Named(QualifiedKey::new("test", r.name.as_str())),
        )
        .unwrap();
    }
    for r in c.rules() {
        let name = format!(
            "{}:{:?}",
            c.relation(r.head.relation()).unwrap().name,
            r.body
                .iter()
                .map(|l| (
                    c.relation(l.atom().relation()).unwrap().name.as_str(),
                    matches!(l, Literal::Negative(_))
                ))
                .collect::<Vec<_>>()
        );
        k.bind_rule(c, r.id, RuleKey::Library(QualifiedKey::new("test", name)))
            .unwrap();
    }
    for a in c.assumptions() {
        k.bind_assumption(
            c,
            a.id,
            AssumptionKey(QualifiedKey::new("test", a.name.as_str())),
        )
        .unwrap();
    }
    for v in c.verifications() {
        k.bind_verification(
            c,
            v.id,
            VerificationKey(QualifiedKey::new("test", v.name.as_str())),
        )
        .unwrap();
    }
    k
}
fn verification(c: &mut Corpus, assumptions: &[AssumptionId]) -> VerificationId {
    c.verification_in(
        Namespace::new(["test"]).unwrap(),
        "checks",
        assumptions.iter().copied(),
        [],
    )
    .unwrap()
}
fn planner<'a>(c: &'a Corpus, k: &'a SemanticKeys, v: VerificationId) -> Planner<'a> {
    Planner::prepare(
        c,
        &Domains::new(),
        k,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
}
fn outputs(rs: &[RelationId]) -> Vec<Output> {
    rs.iter()
        .map(|r| Output {
            atom: atom(*r),
            priority: 0,
        })
        .collect()
}
fn ready(result: Build) -> Plan {
    match result {
        Build::Ready(p) => p,
        other => panic!("{other:?}"),
    }
}
fn compare_worlds(c: &Corpus, k: &SemanticKeys, plan: &Plan, outputs: &[GroundAtom]) {
    let g = GroundProgram::prepare(c, &Domains::new(), &Limits::default()).unwrap();
    let atoms: Vec<_> = g.atoms().cloned().collect();
    let inputs: BTreeSet<_> = g.input_atoms().cloned().collect();
    let rules: Vec<_> = g.rules().cloned().collect();
    for world in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        let models = stable_models(&atoms, &inputs, &rules, &world);
        assert_eq!(models.len(), 1);
        let expected = models.first().unwrap();
        let values = inputs
            .iter()
            .map(|a| (AtomKey::from_atom(k, a).unwrap(), world.contains(a)))
            .collect();
        for order in [
            Order::Semantic,
            Order::ReverseSemantic,
            Order::OutputPriority,
        ] {
            let run = plan.execute_permitted(&values, order, 100_000).unwrap();
            for a in outputs {
                assert_eq!(
                    run.outputs[&AtomKey::from_atom(k, a).unwrap()],
                    expected.contains(a)
                );
            }
        }
    }
}
#[test]
fn positive_kernel_and_negation_match_independent_stable_models_cold_and_warm() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "input", true);
    let gate = rel(&mut c, "gate", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, a, &[(i, false)]);
    rule(&mut c, a, &[(b, false)]);
    rule(&mut c, b, &[(a, false), (gate, false)]);
    rule(&mut c, out, &[(b, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    let first = ready(
        p.build(&outputs(&[a, b, out]), &Options::default())
            .unwrap(),
    );
    assert!(
        first
            .nodes
            .values()
            .any(|n| matches!(n.operation, Operation::Fixpoint { .. }))
    );
    let warm = ready(
        p.build(&outputs(&[a, b, out]), &Options::default())
            .unwrap(),
    );
    let cold = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b, out]), &Options::default())
            .unwrap(),
    );
    assert_eq!(first, warm);
    assert_eq!(first, cold);
    assert_eq!(first.to_json(), warm.to_json());
    compare_worlds(&c, &k, &first, &[atom(a), atom(b), atom(out)]);
}
#[test]
fn unique_negative_cycle_extracts_values_without_unnecessary_plan_branches() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(i, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    let result = ready(p.build(&outputs(&[a, b]), &Options::default()).unwrap());
    compare_worlds(&c, &k, &result, &[atom(a), atom(b)]);
    assert_eq!(result.to_json()["size"]["branches"], 0);
    assert_eq!(
        result,
        ready(p.build(&outputs(&[a, b]), &Options::default()).unwrap())
    );
    let opts = Options {
        max_oracle_calls: 0,
        ..Options::default()
    };
    assert!(matches!(
        p.build(&outputs(&[a, b]), &opts).unwrap(),
        Build::Inconclusive(_)
    ));
    let mut opts = Options::default();
    opts.oracle.max_queries = 0;
    let split = ready(p.build(&outputs(&[a, b]), &opts).unwrap());
    compare_worlds(&c, &k, &split, &[atom(a), atom(b)]);
    assert_eq!(split.to_json()["size"]["branches"], 1);
}
#[test]
fn no_meaning_and_ambiguity_never_become_executable_plans() {
    for ambiguous in [false, true] {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(
            &mut c,
            a,
            &[(i, false), (if ambiguous { b } else { a }, true)],
        );
        if ambiguous {
            rule(&mut c, b, &[(i, false), (a, true)]);
        }
        let v = verification(&mut c, &[]);
        let k = keys(&c);
        let Build::Problem(Problem::Meaning(m)) = planner(&c, &k, v)
            .build(&outputs(&[a]), &Options::default())
            .unwrap()
        else {
            panic!("must report meaning problem")
        };
        if ambiguous {
            assert!(matches!(m.uniqueness, Uniqueness::Multiple { .. }));
        } else {
            assert!(matches!(m.existence, Existence::NoMeaning(_)));
        }
    }
}
#[test]
fn assumption_selection_is_a_recorded_contract_not_an_available_true_value() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(i, false), (a, true)]);
    let assumption = c
        .assume_empty_in(Namespace::new(["test"]).unwrap(), "without_i", i)
        .unwrap();
    let v = verification(&mut c, &[assumption]);
    let k = keys(&c);
    let result = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a]), &Options::default())
            .unwrap(),
    );
    assert_eq!(result.assumptions.len(), 1);
    let values = BTreeMap::from([(AtomKey::from_atom(&k, &atom(i)).unwrap(), false)]);
    assert!(
        !result
            .execute_permitted(&values, Order::Semantic, 10_000)
            .unwrap()
            .outputs[&AtomKey::from_atom(&k, &atom(a)).unwrap()]
    );
}
#[test]
fn contradictory_context_is_not_a_vacuous_plan() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let assumption = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "required", a, [])
        .unwrap();
    let v = verification(&mut c, &[assumption]);
    let k = keys(&c);
    assert!(matches!(
        planner(&c, &k, v)
            .build(&outputs(&[a]), &Options::default())
            .unwrap(),
        Build::NoPermittedWorlds
    ));
}
#[test]
fn absent_and_positive_self_supported_outputs_are_false() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(a, false)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b]), &Options::default())
            .unwrap(),
    );
    let result = plan
        .execute_permitted(&BTreeMap::new(), Order::Semantic, 100)
        .unwrap();
    assert!(result.outputs.values().all(|v| !v));
}
#[test]
fn ordering_policy_changes_schedule_but_not_values() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(i, false)]);
    rule(&mut c, b, &[(i, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(
                &[
                    Output {
                        atom: atom(a),
                        priority: 10,
                    },
                    Output {
                        atom: atom(b),
                        priority: 0,
                    },
                ],
                &Options::default(),
            )
            .unwrap(),
    );
    let values = BTreeMap::from([(AtomKey::from_atom(&k, &atom(i)).unwrap(), true)]);
    let x = plan
        .execute_permitted(&values, Order::Semantic, 1000)
        .unwrap();
    let y = plan
        .execute_permitted(&values, Order::ReverseSemantic, 1000)
        .unwrap();
    let z = plan
        .execute_permitted(&values, Order::OutputPriority, 1000)
        .unwrap();
    assert_eq!(x.outputs, y.outputs);
    assert_eq!(x.outputs, z.outputs);
    assert_ne!(x.trace, y.trace);
    assert_eq!(z.trace, y.trace);
    assert!(matches!(
        plan.execute_permitted(&BTreeMap::new(), Order::Semantic, 1000),
        Err(ExecutionError::MissingInput(_))
    ));
    assert!(matches!(
        plan.execute_permitted(&values, Order::Semantic, 0),
        Err(ExecutionError::WorkLimit)
    ));
}
#[test]
fn unrelated_insertions_and_arena_ids_do_not_change_export() {
    let make = |extra: bool| {
        let mut c = Corpus::new();
        if extra {
            let z = rel(&mut c, "aaa_unrelated", false);
            rule(&mut c, z, &[]);
        }
        let i = rel(&mut c, "i", true);
        let a = rel(&mut c, "a", false);
        rule(&mut c, a, &[(i, false)]);
        let v = verification(&mut c, &[]);
        let k = keys(&c);
        ready(
            planner(&c, &k, v)
                .build(&outputs(&[a]), &Options::default())
                .unwrap(),
        )
        .to_json()
    };
    assert_eq!(make(false), make(true));
}
#[test]
fn bounds_invalid_requests_and_cancellation_cannot_publish_a_plan() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    assert!(matches!(
        p.build(
            &outputs(&[a]),
            &Options {
                max_nodes: 0,
                ..Options::default()
            }
        )
        .unwrap(),
        Build::Inconclusive(_)
    ));
    assert!(p.build(&[], &Options::default()).is_err());
    let mut options = Options::default();
    options.meaning.meaning = stable_query::MeaningMode::None;
    assert!(p.build(&outputs(&[a]), &options).is_err());
    let limits = Limits::default();
    let mut p =
        Planner::prepare(&c, &Domains::new(), &k, v, &limits, QueryLimits::default()).unwrap();
    limits.cancellation.cancel();
    assert!(matches!(
        p.build(&outputs(&[a]), &Options::default()),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn tiny_mixed_program_family_agrees_with_exhaustive_stable_oracle() {
    // All polarities of the cycle and its two independent input guards, plus
    // optional alternate producers. Inputs are never assumed true by planning.
    for shape in 0..32 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(&mut c, a, &[(i, shape & 1 != 0), (b, shape & 2 != 0)]);
        rule(&mut c, b, &[(j, shape & 4 != 0), (a, shape & 8 != 0)]);
        if shape & 16 != 0 {
            rule(&mut c, a, &[(i, false)]);
        }
        let v = verification(&mut c, &[]);
        let k = keys(&c);
        let g = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let atoms: Vec<_> = g.atoms().cloned().collect();
        let inputs: BTreeSet<_> = g.input_atoms().cloned().collect();
        let rules: Vec<_> = g.rules().cloned().collect();
        let unique = subsets(&inputs.iter().cloned().collect::<Vec<_>>())
            .iter()
            .all(|w| stable_models(&atoms, &inputs, &rules, w).len() == 1);
        for options in [Options::default(), split_options()] {
            let result = planner(&c, &k, v)
                .build(&outputs(&[a, b]), &options)
                .unwrap();
            match result {
                Build::Ready(plan) => {
                    assert!(unique, "shape {shape}");
                    compare_worlds(&c, &k, &plan, &[atom(a), atom(b)]);
                }
                Build::Problem(Problem::Meaning(_)) => assert!(!unique, "shape {shape}"),
                other => panic!("tiny shape {shape} should be conclusive: {other:?}"),
            }
        }
    }
}

#[test]
fn output_scope_omits_unrelated_work_but_requires_whole_program_meaning() {
    let mut c = Corpus::new();
    let input = rel(&mut c, "input", true);
    let out = rel(&mut c, "out", false);
    let bad = rel(&mut c, "unrelated", false);
    rule(&mut c, out, &[(input, false)]);
    rule(&mut c, bad, &[(bad, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    assert!(matches!(
        planner(&c, &k, v)
            .build(&outputs(&[out]), &Options::default())
            .unwrap(),
        Build::Problem(Problem::Meaning(_))
    ));
}

fn split_options() -> Options {
    let mut o = Options::default();
    o.oracle.max_queries = 0;
    o
}
#[test]
fn split_joins_different_values_before_one_shared_continuation() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, a, &[(i, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    rule(&mut c, out, &[(a, false), (j, false)]);
    rule(&mut c, out, &[(b, false), (j, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut p = planner(&c, &k, v);
    let options = split_options();
    let plan = ready(p.build(&outputs(&[out]), &options).unwrap());
    assert_eq!(plan.to_json()["size"]["branches"], 1);
    assert_eq!(plan.to_json()["size"]["joins"], 1);
    assert!(matches!(
        plan.nodes[&AtomKey::from_atom(&k, &atom(out)).unwrap()].operation,
        Operation::Compute { .. }
    ));
    compare_worlds(&c, &k, &plan, &[atom(out)]);
    assert_eq!(plan, ready(p.build(&outputs(&[out]), &options).unwrap()));
    assert_eq!(
        plan,
        ready(
            planner(&c, &k, v)
                .build(&outputs(&[out]), &options)
                .unwrap()
        )
    );
    for value in [false, true] {
        let values = BTreeMap::from([
            (AtomKey::from_atom(&k, &atom(i)).unwrap(), value),
            (AtomKey::from_atom(&k, &atom(j)).unwrap(), true),
        ]);
        let run = plan
            .execute_permitted(&values, Order::ReverseSemantic, 10000)
            .unwrap();
        assert_eq!(
            run.outputs[&AtomKey::from_atom(&k, &atom(out)).unwrap()],
            value
        );
        assert_eq!(
            run.branches,
            vec![(AtomKey::from_atom(&k, &atom(i)).unwrap(), value)]
        );
        assert_eq!(
            run.trace
                .iter()
                .filter(|a| **a == AtomKey::from_atom(&k, &atom(out)).unwrap())
                .count(),
            1
        );
    }
}
#[test]
fn extracted_support_excludes_an_unrelated_positive_kernel() {
    let mut c = Corpus::new();
    let selected = rel(&mut c, "selected", true);
    let seed = rel(&mut c, "seed", true);
    let reach = rel(&mut c, "aaa_reachable", false);
    let left = rel(&mut c, "left", false);
    let right = rel(&mut c, "right", false);
    rule(&mut c, reach, &[(seed, false)]);
    rule(&mut c, reach, &[(reach, false)]);
    rule(&mut c, left, &[(selected, false), (right, true)]);
    rule(&mut c, right, &[(selected, true), (left, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[left, reach]), &Options::default())
            .unwrap(),
    );
    let node = &plan.nodes[&AtomKey::from_atom(&k, &atom(left)).unwrap()];
    let selected = AtomKey::from_atom(&k, &atom(selected)).unwrap();
    assert_eq!(node.inputs, BTreeSet::from([selected.clone()]));
    let Operation::Compute { expression, .. } = &node.operation else {
        panic!()
    };
    assert_eq!(expression.nodes, vec![super::Term::Read(selected)]);
    compare_worlds(&c, &k, &plan, &[atom(left), atom(reach)]);
}
#[test]
fn infeasible_arm_is_omitted_only_after_a_conclusive_query() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(i, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    let yes = c
        .assume_at_least_one_in(Namespace::new(["test"]).unwrap(), "yes", i, [])
        .unwrap();
    let v = verification(&mut c, &[yes]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b]), &split_options())
            .unwrap(),
    );
    assert_eq!(plan.to_json()["size"]["branches"], 0);
    let values = BTreeMap::from([(AtomKey::from_atom(&k, &atom(i)).unwrap(), true)]);
    assert!(
        plan.execute_permitted(&values, Order::Semantic, 1000)
            .unwrap()
            .outputs[&AtomKey::from_atom(&k, &atom(a)).unwrap()]
    );
}
#[test]
fn split_bounds_never_publish_a_partial_plan() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(i, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    for which in 0..4 {
        let mut o = split_options();
        match which {
            0 => o.max_split_depth = 0,
            1 => o.max_splits = 0,
            2 => o.max_split_candidates = 0,
            _ => o.max_nodes = 1,
        };
        assert!(matches!(
            planner(&c, &k, v).build(&outputs(&[a, b]), &o).unwrap(),
            Build::Inconclusive(_)
        ));
    }
}
#[test]
fn split_on_a_derived_available_value_keeps_its_producer_before_the_branch() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let guard = rel(&mut c, "guard", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, guard, &[(i, false)]);
    rule(&mut c, a, &[(guard, false), (b, true)]);
    rule(&mut c, b, &[(guard, true), (a, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b]), &split_options())
            .unwrap(),
    );
    let split = plan
        .nodes
        .values()
        .find(|n| matches!(n.operation, Operation::Split { .. }))
        .unwrap();
    assert!(
        split
            .inputs
            .contains(&AtomKey::from_atom(&k, &atom(guard)).unwrap())
    );
    compare_worlds(&c, &k, &plan, &[atom(a), atom(b)]);
}

#[test]
fn subsumed_connectors_allow_sequential_splits_at_depth_one() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    rule(&mut c, a, &[(i, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    rule(&mut c, x, &[(j, false), (y, true)]);
    rule(&mut c, y, &[(j, true), (x, true)]);
    rule(&mut c, a, &[(i, false), (x, false), (b, true)]);
    rule(&mut c, x, &[(j, false), (a, false), (y, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let o = split_options();
    let mut p = planner(&c, &k, v);
    let plan = ready(p.build(&outputs(&[a, b, x, y]), &o).unwrap());
    compare_worlds(&c, &k, &plan, &[atom(a), atom(b), atom(x), atom(y)]);
    assert!(plan.to_json()["size"]["branches"].as_u64().unwrap() > 1);
    assert_eq!(plan, ready(p.build(&outputs(&[a, b, x, y]), &o).unwrap()));
    let shallow = Options {
        max_split_depth: 1,
        ..o
    };
    // Preparation removes the two syntactically subsumed connectors. The two
    // SCCs now split sequentially, so each needs only one level of nesting.
    let shallow_plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b, x, y]), &shallow)
            .unwrap(),
    );
    compare_worlds(&c, &k, &shallow_plan, &[atom(a), atom(b), atom(x), atom(y)]);
}

#[test]
fn nested_splits_recompute_residual_components_and_obey_depth_limits() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let gi = rel(&mut c, "guard_i", false);
    let gj = rel(&mut c, "guard_j", false);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let x = rel(&mut c, "x", false);
    let y = rel(&mut c, "y", false);
    rule(&mut c, gi, &[(i, false)]);
    rule(&mut c, gj, &[(j, false)]);
    // Equivalent upstream guards keep the connectors semantically redundant but
    // prevent a literal-subset proof. This fixture still needs nested splitting
    // when the expression oracle is disabled.
    rule(&mut c, a, &[(gi, false), (b, true)]);
    rule(&mut c, b, &[(i, true), (a, true)]);
    rule(&mut c, x, &[(gj, false), (y, true)]);
    rule(&mut c, y, &[(j, true), (x, true)]);
    rule(&mut c, a, &[(i, false), (x, false), (b, true)]);
    rule(&mut c, x, &[(j, false), (a, false), (y, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let o = split_options();
    let mut p = planner(&c, &k, v);
    let plan = ready(p.build(&outputs(&[a, b, x, y]), &o).unwrap());
    compare_worlds(&c, &k, &plan, &[atom(a), atom(b), atom(x), atom(y)]);
    assert_eq!(plan, ready(p.build(&outputs(&[a, b, x, y]), &o).unwrap()));
    let shallow = Options {
        max_split_depth: 1,
        ..o
    };
    assert!(matches!(
        planner(&c, &k, v)
            .build(&outputs(&[a, b, x, y]), &shallow)
            .unwrap(),
        Build::Inconclusive(_)
    ));
}

#[test]
fn support_reduction_uses_selected_assumptions_without_assuming_available_values_true() {
    let mut c = Corpus::new();
    let extra = rel(&mut c, "extra", true);
    let i = rel(&mut c, "i", true);
    let left = rel(&mut c, "left", false);
    let right = rel(&mut c, "right", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, left, &[(i, false), (extra, false), (right, true)]);
    rule(&mut c, right, &[(i, true), (left, true)]);
    rule(&mut c, right, &[(extra, true), (left, true)]);
    rule(&mut c, bad, &[(i, false), (extra, true)]);
    let a = c
        .assume_empty_in(Namespace::new(["test"]).unwrap(), "i_requires_extra", bad)
        .unwrap();
    let v = verification(&mut c, &[a]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[left]), &Options::default())
            .unwrap(),
    );
    let node = &plan.nodes[&AtomKey::from_atom(&k, &atom(left)).unwrap()];
    assert_eq!(
        node.inputs,
        BTreeSet::from([AtomKey::from_atom(&k, &atom(i)).unwrap()])
    );
    for (iv, ev) in [(false, false), (false, true), (true, true)] {
        let values = BTreeMap::from([
            (AtomKey::from_atom(&k, &atom(i)).unwrap(), iv),
            (AtomKey::from_atom(&k, &atom(extra)).unwrap(), ev),
        ]);
        assert_eq!(
            plan.execute_permitted(&values, Order::Semantic, 10000)
                .unwrap()
                .outputs[&AtomKey::from_atom(&k, &atom(left)).unwrap()],
            iv
        );
    }
}
#[test]
fn branch_keys_and_join_shape_survive_unrelated_insertions() {
    let make = |extra| {
        let mut c = Corpus::new();
        if extra {
            let z = rel(&mut c, "aaa_unrelated", false);
            rule(&mut c, z, &[]);
        }
        let i = rel(&mut c, "i", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(&mut c, a, &[(i, false), (b, true)]);
        rule(&mut c, b, &[(i, true), (a, true)]);
        let v = verification(&mut c, &[]);
        let k = keys(&c);
        ready(
            planner(&c, &k, v)
                .build(&outputs(&[a, b]), &split_options())
                .unwrap(),
        )
        .to_json()
    };
    assert_eq!(make(false), make(true));
}

#[test]
fn default_limits_split_a_wide_support_instead_of_building_a_global_expression() {
    let mut c = Corpus::new();
    let guard = rel(&mut c, "guard", true);
    let xs = (0..65)
        .map(|i| rel(&mut c, &format!("x{i}"), true))
        .collect::<Vec<_>>();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let mut body = vec![(guard, false), (b, true)];
    body.extend(xs.iter().map(|r| (*r, false)));
    rule(&mut c, a, &body);
    rule(&mut c, b, &[(guard, true), (a, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let plan = ready(
        planner(&c, &k, v)
            .build(&outputs(&[a, b]), &Options::default())
            .unwrap(),
    );
    assert!(plan.to_json()["size"]["branches"].as_u64().unwrap() > 0);
    for gv in [false, true] {
        for off in [None, Some(0), Some(32), Some(64)] {
            let mut values = xs
                .iter()
                .enumerate()
                .map(|(i, r)| (AtomKey::from_atom(&k, &atom(*r)).unwrap(), off != Some(i)))
                .collect::<BTreeMap<_, _>>();
            values.insert(AtomKey::from_atom(&k, &atom(guard)).unwrap(), gv);
            for order in [
                Order::Semantic,
                Order::ReverseSemantic,
                Order::OutputPriority,
            ] {
                let result = plan.execute_permitted(&values, order, 100_000).unwrap();
                assert_eq!(
                    result.outputs[&AtomKey::from_atom(&k, &atom(a)).unwrap()],
                    gv && off.is_none()
                );
                assert_eq!(
                    result.outputs[&AtomKey::from_atom(&k, &atom(b)).unwrap()],
                    !gv
                );
            }
        }
    }
}

#[test]
fn unresolved_cone_reports_dependencies_and_a_world_without_claiming_impossibility() {
    // A downstream contradiction selects between upstream meanings. Whole-program
    // meaning is unique, but p is outside a/b's producer cone. The cone-only
    // strategy must report its limitation rather than importing hidden support.
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let reject = rel(&mut c, "reject", false);
    rule(&mut c, a, &[(b, true)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, reject, &[(a, false), (p, true), (reject, true)]);
    rule(&mut c, reject, &[(b, false), (p, false), (reject, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let result = planner(&c, &k, v)
        .build(&outputs(&[a]), &Options::default())
        .unwrap();
    let Build::Problem(Problem::Unresolved {
        path,
        dependencies,
        world,
        ..
    }) = result
    else {
        panic!("expected bounded unresolved problem: {result:?}")
    };
    assert!(path.is_empty());
    assert!(!dependencies.is_empty());
    assert!(world.is_some());
    let g = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let atoms = g.atoms().cloned().collect::<Vec<_>>();
    let inputs = g.input_atoms().cloned().collect::<BTreeSet<_>>();
    let rules = g.rules().cloned().collect::<Vec<_>>();
    for w in subsets(&inputs.iter().cloned().collect::<Vec<_>>()) {
        assert_eq!(stable_models(&atoms, &inputs, &rules, &w).len(), 1);
    }
}

#[test]
fn preparation_settles_an_output_in_a_dead_cycle_before_planning() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(x, false), (q, true)]);
    rule(&mut c, p, &[]);
    rule(&mut c, q, &[(p, true)]);
    let v = verification(&mut c, &[]);
    let k = keys(&c);
    let mut options = Options::default();
    options.meaning.max_worlds = 0;
    options.max_oracle_calls = 0;
    let mut planner = planner(&c, &k, v);
    let plan = ready(planner.build(&outputs(&[p, q]), &options).unwrap());
    assert!(
        plan.nodes()
            .values()
            .all(|n| matches!(n.operation, Operation::Compute { .. }))
    );
    assert_eq!(plan.to_json()["size"]["branches"], 0);
    compare_worlds(&c, &k, &plan, &[atom(p), atom(q)]);
    assert_eq!(
        plan,
        ready(planner.build(&outputs(&[p, q]), &options).unwrap())
    );
}
