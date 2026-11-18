use crate::{
    limits::Budget,
    test_support::symbolic::{nullary, relation, rule},
    *,
};
use denotate_ir::*;

fn compare(p: &GroundProgram) {
    let limits = Limits::default();
    let raw = p.symbolic(&limits).unwrap();
    let masked = p
        .symbolic_for_checking::<true>(&mut Budget::new(&limits))
        .unwrap();
    let inputs: Vec<_> = p.input_atoms().cloned().collect();
    for a in p.atoms() {
        match (raw.fact(a).unwrap(), masked.fact(a).unwrap()) {
            (SymbolicFact::Settled(c), SymbolicFact::Settled(m)) => {
                let expected = raw
                    .context()
                    .restrict(&c, &mut Budget::new(&limits))
                    .unwrap();
                // Raw XOR also checks that masked results are false outside W.
                assert!(
                    raw.context()
                        .apply(
                            &expected,
                            &m,
                            biodivine_lib_bdd::op_function::xor,
                            &mut Budget::new(&limits)
                        )
                        .unwrap()
                        .is_false(),
                    "{a:?}"
                );
            }
            (SymbolicFact::Blocked(a), SymbolicFact::Blocked(b)) => assert_eq!(a, b),
            states => panic!("{a:?}: {states:?}"),
        }
    }
    for bits in 0..(1usize << inputs.len()) {
        let world: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, a)| a.clone())
            .collect();
        if raw
            .context()
            .evaluate(&raw.context().permitted_worlds(), world.clone(), &limits)
            .is_err()
        {
            continue;
        }
        let replay = p.evaluate(world.clone(), &limits).unwrap();
        for a in p.atoms() {
            if let SymbolicFact::Settled(c) = masked.fact(a).unwrap() {
                assert_eq!(
                    replay.fact(a).unwrap(),
                    FactState::Settled(
                        masked
                            .context()
                            .evaluate(&c, world.clone(), &limits)
                            .unwrap()
                    )
                );
            }
        }
    }
}

#[test]
fn within_w_matches_all_worlds_of_tiny_recursive_stratified_programs() {
    for shape in 0..16 {
        let mut c = Corpus::new();
        let inputs: Vec<_> = (0..3)
            .map(|i| relation(&mut c, &format!("i{i}"), true))
            .collect();
        let cycle: Vec<_> = (0..3)
            .map(|i| relation(&mut c, &format!("p{i}"), false))
            .collect();
        for i in 0..3 {
            rule(&mut c, cycle[i], &[(cycle[(i + 1) % 3], false)]);
            if shape & (1 << i) != 0 {
                rule(&mut c, cycle[i], &[(inputs[i], false)]);
            }
        }
        let no = relation(&mut c, "no", false);
        rule(&mut c, no, &[(cycle[0], true)]);
        let fact = relation(&mut c, "fact", false);
        rule(&mut c, fact, &[]);
        let both = relation(&mut c, "both", false);
        rule(
            &mut c,
            both,
            &[(fact, false), (no, false), (inputs[2], true)],
        );
        if shape & 8 != 0 {
            let blocked = relation(&mut c, "blocked", false);
            rule(&mut c, blocked, &[(blocked, true)]);
        }
        let mut p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        compare(&p); // W = true.
        p.install_assumptions(
            &[Restriction::AtLeastOne {
                relation: inputs[0],
                group_by: vec![],
            }],
            None,
            &mut Budget::new(&Limits::default()),
        )
        .unwrap();
        compare(&p); // Nontrivial W, including a true-throughout-W input.
    }
}

#[test]
fn within_w_preserves_replacement_expressions_and_the_raw_proof_boundary() {
    let (c, _) = super::guarded_settlement::fixture(0);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let input = raw.input_atoms().next().unwrap().relation;
    let mut raw = raw.admit(&limits).unwrap();
    raw.install_assumptions(
        &[Restriction::Empty { relation: input }],
        None,
        &mut Budget::new(&limits),
    )
    .unwrap();
    let admitted = raw;
    assert!(admitted.is_admitted());
    assert!(admitted.rules().any(|r| !r.replacements.is_empty()));
    compare(&admitted);
    // Expressions cover every operator, including constants in nested negation.
    let m = admitted
        .symbolic_for_checking::<true>(&mut Budget::new(&limits))
        .unwrap();
    for expression in [
        SettledExpression::Constant(true),
        SettledExpression::Constant(false),
        SettledExpression::Not(std::sync::Arc::new(SettledExpression::Constant(true))),
        SettledExpression::All(vec![
            std::sync::Arc::new(SettledExpression::Constant(true)),
            std::sync::Arc::new(SettledExpression::Constant(false)),
        ]),
        SettledExpression::Any(vec![
            std::sync::Arc::new(SettledExpression::Constant(false)),
            std::sync::Arc::new(SettledExpression::Constant(true)),
        ]),
    ] {
        let old = admitted
            .symbolic(&limits)
            .unwrap()
            .settled_expression(&expression, &mut Budget::new(&limits))
            .unwrap();
        let crate::symbolic::PartialCondition::Known(new) = m
            .partial_expression(&expression, &mut Budget::new(&limits))
            .unwrap()
        else {
            panic!()
        };
        let expected = m
            .context()
            .restrict(&old, &mut Budget::new(&limits))
            .unwrap();
        assert!(
            m.context()
                .apply(
                    &expected,
                    &new,
                    biodivine_lib_bdd::op_function::xor,
                    &mut Budget::new(&limits)
                )
                .unwrap()
                .is_false()
        );
    }
}

#[test]
fn truth_within_w_and_false_guards_mask_exhausted_alternatives() {
    let mut c = Corpus::new();
    let flag = relation(&mut c, "flag", true);
    let wide = relation(&mut c, "wide", false);
    for i in 0..8 {
        let input = relation(&mut c, &format!("i{i}"), true);
        rule(&mut c, wide, &[(input, false)]);
    }
    let yes = relation(&mut c, "yes", false);
    rule(&mut c, yes, &[(wide, false)]);
    rule(&mut c, yes, &[(flag, false)]);
    let no = relation(&mut c, "no", false);
    rule(&mut c, no, &[(wide, true), (flag, true)]);
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    p.install_assumptions(
        &[Restriction::AtLeastOne {
            relation: flag,
            group_by: vec![],
        }],
        None,
        &mut Budget::new(&Limits::default()),
    )
    .unwrap();
    let low = Limits {
        max_bdd_nodes: 6,
        ..Limits::default()
    };
    let m = p
        .symbolic_for_checking::<true>(&mut Budget::new(&low))
        .unwrap();
    assert!(matches!(
        m.fact(&nullary(wide)).unwrap(),
        SymbolicFact::Inconclusive(_)
    ));
    let SymbolicFact::Settled(yes) = m.fact(&nullary(yes)).unwrap() else {
        panic!("true alternative lost")
    };
    assert!(
        m.context()
            .equivalent(&yes, &m.context().true_condition(), &Limits::default())
            .unwrap()
    );
    assert!(matches!(m.fact(&nullary(no)).unwrap(),SymbolicFact::Settled(c) if c.is_false()));
}
