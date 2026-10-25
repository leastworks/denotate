use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

#[test]
fn witness_is_complete_prefers_absence_and_checks_universe_and_budget() {
    let mut corpus = Corpus::new();
    for name in ["x", "y", "unused"] {
        corpus
            .declare_relation(name, RelationRole::Input, [])
            .unwrap();
    }
    let limits = Limits::default();
    let p = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
    let ctx = p.condition_context(&limits).unwrap();
    let inputs: Vec<_> = p.input_atoms().cloned().collect();
    let x = ctx.input(&inputs[0], &limits).unwrap();
    let y = ctx.input(&inputs[1], &limits).unwrap();
    for condition in [
        &x,
        &ctx.not(&x, &limits).unwrap(),
        &ctx.or(&x, &y, &limits).unwrap(),
        &ctx.true_condition(),
    ] {
        let witness = ctx.witness(condition, &limits).unwrap().unwrap();
        assert!(
            ctx.evaluate(condition, witness.present.iter().cloned(), &limits)
                .unwrap()
        );
        assert_eq!(
            witness
                .present
                .union(&witness.absent)
                .cloned()
                .collect::<BTreeSet<_>>(),
            inputs.iter().cloned().collect()
        );
        assert!(witness.present.is_disjoint(&witness.absent));
        assert!(witness.absent.contains(&inputs[2]));
    }
    assert_eq!(ctx.witness(&ctx.false_condition(), &limits).unwrap(), None);
    let other = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
    let foreign = other.condition_context(&limits).unwrap().true_condition();
    assert_eq!(
        ctx.witness(&foreign, &limits),
        Err(CheckError::ForeignCondition)
    );
    assert!(matches!(
        ctx.witness(
            &x,
            &Limits {
                max_work: 0,
                ..limits
            }
        ),
        Err(CheckError::LimitExceeded { .. })
    ));
}

#[test]
fn a_symbolic_overlap_that_fails_concrete_replay_is_a_failure_not_a_finding() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("Value").unwrap();
    let a = c.declare_constant("a", sort).unwrap();
    let b = c.declare_constant("b", sort).unwrap();
    let x = c.declare_relation("x", RelationRole::Input, []).unwrap();
    let r = c
        .declare_relation("r", RelationRole::Derived, [Parameter::new("value", sort)])
        .unwrap();
    let head = c.atom(r, [a.into()]).unwrap();
    c.add_rule(head, []).unwrap();
    let head = c.atom(r, [b.into()]).unwrap();
    let yes = c.atom(x, []).unwrap();
    let no = c.atom(x, []).unwrap();
    c.add_rule(head, [Literal::Positive(yes), Literal::Negative(no)])
        .unwrap();
    c.at_most_one("unique", r, [], "test").unwrap();
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::from([(sort, vec![a, b])]), &limits).unwrap();
    let mut symbolic = p.symbolic(&limits).unwrap();
    assert!(
        symbolic
            .verify_at_most_one(&limits)
            .unwrap()
            .all_obligations_proved()
    );
    assert!(matches!(
        symbolic.verify_at_most_one(&Limits {
            max_work: 0,
            ..limits.clone()
        }),
        Err(CheckError::LimitExceeded { .. })
    ));
    // Deliberately corrupt the symbolic result, exercising the reporting gate.
    symbolic
        .conditions
        .insert(GroundAtom::new(r, [b]), symbolic.context.true_condition());
    assert!(matches!(
        symbolic.verify_at_most_one(&limits),
        Err(CheckError::Internal("symbolic overlap did not replay"))
    ));
}

#[test]
fn scoped_replay_cannot_claim_absence_outside_its_completed_components() {
    let mut c = Corpus::new();
    let a = c.declare_relation("a", RelationRole::Derived, []).unwrap();
    let b = c.declare_relation("b", RelationRole::Derived, []).unwrap();
    for r in [a, b] {
        let head = c.atom(r, []).unwrap();
        c.add_rule(head, []).unwrap();
    }
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let a = GroundAtom::new(a, []);
    let b = GroundAtom::new(b, []);
    let cone = p.dependency_cone([a.clone()], &limits).unwrap();
    let replay = p
        .evaluate_selected(
            [],
            Some(&cone.components),
            &mut crate::limits::Budget::new(&limits),
        )
        .unwrap();
    assert!(!replay.is_complete());
    assert_eq!(replay.fact(&a).unwrap(), FactState::Settled(true));
    assert_eq!(replay.fact(&b), Err(CheckError::OutsideReplay(b.clone())));
    assert_eq!(
        replay.absence_provider(&b),
        Err(CheckError::OutsideReplay(b))
    );
}
