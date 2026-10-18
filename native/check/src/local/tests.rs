use super::*;
use crate::test_support::rewrites::{atom, rel, rule, subsets};

#[test]
fn local_missing_premise_is_an_outer_error_including_blocked_components() {
    for blocked in [false, true] {
        let mut corpus = Corpus::new();
        let input = rel(&mut corpus, "input", true);
        let out = rel(&mut corpus, "out", false);
        let mut body = vec![(input, false)];
        if blocked {
            body.push((out, true));
        }
        rule(&mut corpus, out, &body);
        let limits = Limits::default();
        let program = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
        let mut cone = program.dependency_cone([atom(out)], &limits).unwrap();
        assert_eq!(!cone.blocked_by.is_empty(), blocked);
        program
            .symbolic_selected(&mut Budget::new(&limits), true, Some(&cone))
            .unwrap();
        assert!(cone.facts.remove(&atom(input)));
        for partial in [false, true] {
            assert!(matches!(
                program.symbolic_selected(&mut Budget::new(&limits), partial, Some(&cone)),
                Err(CheckError::Internal(
                    "local premise outside dependency cone"
                ))
            ));
        }
    }
}

#[test]
fn local_structurally_absent_premise_is_false_only_when_in_the_cone() {
    let mut corpus = Corpus::new();
    let absent = rel(&mut corpus, "absent", false);
    let out = rel(&mut corpus, "out", false);
    rule(&mut corpus, out, &[(absent, true)]);
    let limits = Limits::default();
    let program = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
    let mut cone = program.dependency_cone([atom(out)], &limits).unwrap();
    let meaning = program
        .symbolic_selected(&mut Budget::new(&limits), true, Some(&cone))
        .unwrap();
    assert!(!program.is_possible(&atom(absent)).unwrap());
    assert!(!meaning.conditions.contains_key(&atom(absent)));
    assert!(
        matches!(meaning.fact(&atom(absent)).unwrap(), SymbolicFact::Settled(c) if c.is_false())
    );
    assert!(matches!(meaning.fact(&atom(out)).unwrap(), SymbolicFact::Settled(c) if c.is_true()));
    assert!(cone.facts.remove(&atom(absent)));
    assert!(matches!(
        program.symbolic_selected(&mut Budget::new(&limits), true, Some(&cone)),
        Err(CheckError::Internal(
            "local premise outside dependency cone"
        ))
    ));
}

#[test]
fn projected_at_most_one_worlds_extend_and_minimum_witnesses_agree() {
    let mut corpus = Corpus::new();
    let sort = corpus.declare_sort("Value").unwrap();
    let values: Vec<_> = ["z", "a", "m"]
        .into_iter()
        .map(|n| corpus.declare_constant(n, sort).unwrap())
        .collect();
    let relation = corpus
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", sort)])
        .unwrap();
    let limits = Limits::default();
    let program = GroundProgram::prepare_with_input_groups(
        &corpus,
        &Domains::from([(sort, values)]),
        &[InputAtMostOne {
            relation,
            group_by: vec![],
        }],
        &limits,
    )
    .unwrap();
    let all = program.input_atoms().cloned().collect::<Vec<_>>();
    let global = program.condition_context(&limits).unwrap();
    // Includes empty, singleton and crossing-group projections, not only full groups.
    for selected in subsets(&all) {
        let local =
            ConditionContext::build_selected(&program, Some(&selected), &mut Budget::new(&limits))
                .unwrap();
        for world in subsets(&selected.iter().cloned().collect::<Vec<_>>()) {
            let local_ok = local
                .evaluate(&local.permitted_worlds(), world.iter().cloned(), &limits)
                .is_ok();
            let global_ok = global
                .evaluate(&global.permitted_worlds(), world.iter().cloned(), &limits)
                .is_ok();
            assert_eq!(local_ok, global_ok);
            let extension = subsets(&all).into_iter().any(|w| {
                w.intersection(&selected).cloned().collect::<BTreeSet<_>>() == world
                    && global
                        .evaluate(&global.permitted_worlds(), w, &limits)
                        .is_ok()
            });
            assert_eq!(local_ok, extension);
        }
        for positive in subsets(&selected.iter().cloned().collect::<Vec<_>>()) {
            let formula = |ctx: &ConditionContext| {
                let mut c = ctx.true_condition();
                for a in &positive {
                    c = ctx
                        .and(&c, &ctx.input(a, &limits).unwrap(), &limits)
                        .unwrap();
                }
                c
            };
            let local_w = local.witness(&formula(&local), &limits).unwrap();
            let global_w = global.witness(&formula(&global), &limits).unwrap();
            assert_eq!(
                local_w.as_ref().map(|w| &w.present),
                global_w.as_ref().map(|w| &w.present)
            );
        }
    }
    let a = ConditionContext::build_selected(
        &program,
        Some(&BTreeSet::from([all[0].clone()])),
        &mut Budget::new(&limits),
    )
    .unwrap();
    let b = ConditionContext::build_selected(
        &program,
        Some(&BTreeSet::from([all[1].clone()])),
        &mut Budget::new(&limits),
    )
    .unwrap();
    assert!(matches!(
        b.witness(&a.true_condition(), &limits),
        Err(CheckError::ForeignCondition)
    ));
}
