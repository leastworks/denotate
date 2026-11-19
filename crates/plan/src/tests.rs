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
    assert!(matches!(
        p.build(&outputs(&[a, b]), &opts).unwrap(),
        Build::OracleInconclusive(_)
    ));
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
        let result = planner(&c, &k, v)
            .build(&outputs(&[a, b]), &Options::default())
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
