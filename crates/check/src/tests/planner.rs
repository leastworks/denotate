use super::*;

fn atoms(n: usize, arity: usize, mode: usize) -> (Corpus, Vec<Atom>) {
    let mut c = Corpus::new();
    let sort = c.declare_sort("S").unwrap();
    let constant = c.declare_constant("c", sort).unwrap();
    let relation = c
        .declare_relation(
            "r",
            RelationRole::Input,
            (0..arity).map(|i| Parameter::new(format!("c{i}"), sort)),
        )
        .unwrap();
    let atoms = (0..n)
        .map(|i| {
            let terms = (0..arity).map(|column| {
                if mode == 0 || (mode == 4 && (i + column) % 3 == 0) {
                    Term::Constant(constant)
                } else {
                    let variable = match mode {
                        1 => 0,                  // Repeated columns and a dense shared-variable incidence list.
                        2 => i + column,         // Overlapping chain.
                        3 => i * arity + column, // Independent products.
                        _ => (i + column) % 3,
                    };
                    Term::variable(format!("v{variable}"), sort)
                }
            });
            c.atom(relation, terms).unwrap()
        })
        .collect();
    (c, atoms)
}

#[test]
fn every_pivot_preserves_maximum_bound_column_score() {
    let limits = Limits::default();
    for arity in [0, 1, 2, 4] {
        for mode in 0..5 {
            for n in [1, 2, 4, 7, 12] {
                let (_, atoms) = atoms(n, arity, mode);
                let positives: Vec<_> = atoms
                    .iter()
                    .map(|a| {
                        a.arguments()
                            .iter()
                            .map(|t| match t.value() {
                                Term::Constant(_) => None,
                                Term::Variable { name, .. } => {
                                    Some(std::sync::Arc::from(name.as_str()))
                                }
                            })
                            .collect()
                    })
                    .collect();
                let mut budget = Budget::new(&limits);
                let planner = JoinPlanner::new(&positives, &mut budget).unwrap();
                for pivot in 0..n {
                    let steps = planner.steps(pivot, &mut budget).unwrap();
                    assert_eq!(steps.len(), n - 1);
                    let mut used = BTreeSet::from([pivot]);
                    let mut bound = BTreeSet::new();
                    let mut selected = pivot;
                    for (index, columns) in steps {
                        for term in atoms[selected].arguments() {
                            if let Term::Variable { name, .. } = term.value() {
                                bound.insert(name.as_str());
                            }
                        }
                        let expected = |atom: &Atom| {
                            atom.arguments()
                                .iter()
                                .enumerate()
                                .filter_map(|(i, t)| match t.value() {
                                    Term::Constant(_) => Some(i),
                                    Term::Variable { name, .. }
                                        if bound.contains(name.as_str()) =>
                                    {
                                        Some(i)
                                    }
                                    _ => None,
                                })
                                .collect::<Vec<_>>()
                        };
                        let maximum = (0..n)
                            .filter(|i| !used.contains(i))
                            .map(|i| expected(&atoms[i]).len())
                            .max()
                            .unwrap();
                        assert_eq!(columns, expected(&atoms[index]));
                        assert_eq!(columns.len(), maximum);
                        assert!(used.insert(index));
                        selected = index;
                    }
                    assert_eq!(used.len(), n);
                }
            }
        }
    }
}

#[test]
fn all_pivots_have_quadratic_work_including_dense_incidence_updates() {
    let limits = Limits {
        max_work: 20_000_000,
        ..Limits::default()
    };
    for mode in 0..5 {
        let mut previous = None;
        for n in [16, 32, 64, 128, 256] {
            let (_, atoms) = atoms(n, 4, mode);
            let positives: Vec<_> = atoms
                .iter()
                .map(|a| {
                    a.arguments()
                        .iter()
                        .map(|t| match t.value() {
                            Term::Constant(_) => None,
                            Term::Variable { name, .. } => {
                                Some(std::sync::Arc::from(name.as_str()))
                            }
                        })
                        .collect()
                })
                .collect();
            let mut budget = Budget::new(&limits);
            let planner = JoinPlanner::new(&positives, &mut budget).unwrap();
            let count: usize = (0..n)
                .map(|pivot| planner.steps(pivot, &mut budget).unwrap().len())
                .sum();
            assert_eq!(count, n * (n - 1));
            assert!(
                budget.used() <= 32 * n * n,
                "mode {mode}, n {n}: {}",
                budget.used()
            );
            if let Some(old) = previous {
                assert!(budget.used() <= 4 * old);
            }
            previous = Some(budget.used());
        }
    }
}

#[test]
fn owned_plan_preflight_bounds_every_pivot_and_preserves_promotion_ties() {
    for arity in [0, 1, 2, 4] {
        for mode in 0..5 {
            for n in [0, 1, 2, 8, 32] {
                let (_, atoms) = atoms(n, arity, mode);
                let shape = JoinPlanSchema {
                    positions: (0..n).collect(),
                    positives: atoms
                        .iter()
                        .map(|a| {
                            a.arguments()
                                .iter()
                                .map(|t| match t.value() {
                                    Term::Constant(_) => None,
                                    Term::Variable { name, .. } => {
                                        Some(std::sync::Arc::from(name.as_str()))
                                    }
                                })
                                .collect()
                        })
                        .collect(),
                };
                let bound = shape.work_bound().unwrap();
                let owned = OwnedJoinPlan::compute(shape).unwrap();
                assert!(owned.work().unwrap() <= bound, "{n}/{arity}/{mode}");
            }
        }
    }
    let shape = JoinPlanSchema {
        positions: vec![0, 1, 2],
        positives: vec![
            vec![Some("x".into())],
            vec![Some("x".into()), Some("y".into())],
            vec![Some("x".into()), Some("z".into())],
        ],
    };
    let p = OwnedJoinPlan::compute(shape).unwrap();
    assert_eq!(
        p.pivots[0].steps[0].0, 2,
        "most recently promoted r precedes q"
    );
}
