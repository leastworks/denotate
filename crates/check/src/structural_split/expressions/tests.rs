use super::*;
use crate::test_support::rewrites::{atom, rel};

#[test]
fn choices_preserve_all_worlds_and_reuse_identical_branches() {
    let mut c = denotate_ir::Corpus::new();
    let atoms: Vec<_> = ["choice", "a", "b"]
        .map(|n| atom(rel(&mut c, n, true)))
        .into();
    let limits = Limits::default();
    let mut budget = Budget::new(&limits);
    let mut expressions = Expressions::default();
    let mut held = 0;
    let mut intern = |e| expressions.intern(e, &mut held, &mut budget).unwrap();
    let choice = intern(Arc::new(SettledExpression::Atom(atoms[0].clone())));
    let a = intern(Arc::new(SettledExpression::Atom(atoms[1].clone())));
    let b = intern(Arc::new(SettledExpression::Atom(atoms[2].clone())));
    let yes = intern(constant(true));
    let no = intern(constant(false));
    let same = expressions
        .choose(choice.clone(), a.clone(), a.clone(), &mut held, &mut budget)
        .unwrap();
    assert!(Arc::ptr_eq(&same, &a));
    for (left, right) in [
        (yes.clone(), yes.clone()),
        (no.clone(), no.clone()),
        (yes.clone(), no.clone()),
        (no.clone(), yes.clone()),
        (a.clone(), b.clone()),
    ] {
        let e = expressions
            .choose(
                choice.clone(),
                left.clone(),
                right.clone(),
                &mut held,
                &mut budget,
            )
            .unwrap();
        for bits in 0..8 {
            let eval = |e: &Expr| {
                e.evaluate(
                    &mut |a| Ok(bits & (1 << atoms.iter().position(|x| x == a).unwrap()) != 0),
                    &mut Budget::new(&limits),
                )
                .unwrap()
            };
            assert_eq!(
                eval(&e),
                if bits & 1 != 0 {
                    eval(&left)
                } else {
                    eval(&right)
                }
            );
        }
        if Arc::ptr_eq(&left, &yes) && Arc::ptr_eq(&right, &no) {
            assert!(
                Arc::ptr_eq(&e, &choice),
                "opposite leaf domains cannot justify collapsing to true"
            );
        }
        if Arc::ptr_eq(&left, &a) && Arc::ptr_eq(&right, &b) {
            assert!(
                matches!(e.as_ref(), SettledExpression::Any(_)),
                "different branches must remain conditional"
            );
        }
    }
}

#[test]
fn complements_fold_in_either_order_including_compound_children() {
    let mut c = denotate_ir::Corpus::new();
    let a = Arc::new(SettledExpression::Atom(atom(rel(&mut c, "a", true))));
    let b = Arc::new(SettledExpression::Atom(atom(rel(&mut c, "b", true))));
    let compound = join(vec![a.clone(), b.clone()], true);
    let limits = Limits::default();
    let mut expressions = Expressions::default();
    for e in [a, compound] {
        for all in [false, true] {
            for reverse in [false, true] {
                let mut children = vec![e.clone(), signed(e.clone(), true), b.clone()];
                if reverse {
                    children.reverse();
                }
                let result = expressions
                    .intern(join(children, all), &mut 0, &mut Budget::new(&limits))
                    .unwrap();
                assert!(matches!(result.as_ref(), SettledExpression::Constant(v) if *v == !all));
            }
        }
    }
    let result = expressions
        .intern(
            join(vec![b.clone(), constant(true)], true),
            &mut 0,
            &mut Budget::new(&limits),
        )
        .unwrap();
    assert_eq!(result.as_ref(), b.as_ref());
}
