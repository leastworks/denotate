use super::*;

fn models(p: &GroundProgram, universe: &[GroundAtom]) -> BTreeSet<Vec<bool>> {
    (0..1usize << universe.len())
        .filter_map(|bits| {
            let present: BTreeSet<_> = universe
                .iter()
                .enumerate()
                .filter_map(|(i, a)| (bits & (1 << i) != 0).then_some(a.clone()))
                .collect();
            let valid = universe.iter().all(|a| {
                p.inputs.contains(a)
                    || present.contains(a)
                        == p.rules.iter().filter(|r| &r.head.atom == a).any(|r| {
                            r.body.iter().all(|l| {
                                present.contains(&l.term.atom) == (l.polarity == Polarity::Positive)
                            })
                        })
            });
            valid.then(|| universe.iter().map(|a| present.contains(a)).collect())
        })
        .collect()
}

#[test]
fn sparse_completion_matches_full_enumeration_and_original_scopes() {
    for negative in [false, true] {
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let a = c.declare_constant("a", s).unwrap();
        let b = c.declare_constant("b", s).unwrap();
        let relation = |c: &mut Corpus, name, role| {
            c.declare_relation(name, role, [Parameter::new("x", s)])
                .unwrap()
        };
        let input = relation(&mut c, "input", RelationRole::Input);
        let p = relation(&mut c, "p", RelationRole::Derived);
        let q = relation(&mut c, "q", RelationRole::Derived);
        let absent = relation(&mut c, "absent", RelationRole::Derived);
        let pair = c
            .declare_relation(
                "pair",
                RelationRole::Derived,
                [Parameter::new("x", s), Parameter::new("y", s)],
            )
            .unwrap();

        let x = || Term::variable("X", s);
        let y = || Term::variable("Y", s);
        let z = || Term::variable("Z", s);
        let head = c.atom(p, [x()]).unwrap();
        let body = c.atom(p, [x()]).unwrap();
        c.add_rule(head, [Literal::Positive(body)]).unwrap();
        let head = c.atom(q, [x()]).unwrap();
        let body = c.atom(p, [x()]).unwrap();
        let guard = c.atom(input, [x()]).unwrap();
        c.add_rule(
            head,
            [
                Literal::Positive(guard),
                if negative {
                    Literal::Negative(body)
                } else {
                    Literal::Positive(body)
                },
            ],
        )
        .unwrap();
        let head = c.atom(pair, [x(), y()]).unwrap();
        let left = c.atom(input, [x()]).unwrap();
        let right = c.atom(q, [y()]).unwrap();
        c.add_rule(head, [Literal::Positive(left), Literal::Positive(right)])
            .unwrap();
        // Dead producer with a body-only variable. Its original dependencies
        // still reach every p and absent atom, without materializing X×Y×Z.
        let head = c.atom(q, [x()]).unwrap();
        let left = c.atom(p, [y()]).unwrap();
        let right = c.atom(absent, [z()]).unwrap();
        let guard = c.atom(input, [x()]).unwrap();
        c.add_rule(
            head,
            [
                Literal::Positive(guard),
                Literal::Positive(left),
                Literal::Positive(right),
            ],
        )
        .unwrap();
        for values in [vec![a, b], vec![b], vec![]] {
            let limits = Limits::default();
            let domains = Domains::from([(s, values)]);
            let full = GroundProgram::prepare_completion_enumerated(
                &c,
                &domains,
                &mut Budget::new(&limits),
            )
            .unwrap();
            let mut full = full;
            full.completion_inputs(&c, &mut Budget::new(&limits))
                .unwrap();
            let sparse =
                GroundProgram::prepare_completion(&c, &domains, &mut Budget::new(&limits)).unwrap();
            let universe: Vec<_> = full
                .atoms
                .iter()
                .chain(&sparse.atoms)
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            assert_eq!(models(&full, &universe), models(&sparse, &universe));
            let original =
                OriginalDependencies::new(&c, &domains, &mut Budget::new(&limits)).unwrap();
            for root in &universe {
                let old = full.dependency_cone([root.clone()], &limits).unwrap();
                let new = original
                    .cone([root.clone()], &mut Budget::new(&limits))
                    .unwrap();
                assert_eq!(new.facts, old.facts);
                let recursive = full.components().any(|component| {
                    component.atoms.iter().any(|a| old.facts.contains(a))
                        && (component.atoms.len() > 1
                            || full.rules.iter().any(|r| {
                                component.atoms.contains(&r.head.atom)
                                    && r.body.iter().any(|l| l.term.atom == r.head.atom)
                            }))
                });
                assert_eq!(new.cycle.is_some(), recursive);
            }
        }
    }
}

#[test]
fn joins_respect_repeated_variables_constants_and_eligibility() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let args = || [Parameter::new("x", s), Parameter::new("y", s)];
    let allowed = c
        .declare_relation("allowed", RelationRole::Derived, args())
        .unwrap();
    let input = c
        .declare_relation("input", RelationRole::Input, args())
        .unwrap();
    let p = c
        .declare_relation("p", RelationRole::Derived, args())
        .unwrap();
    c.restrict_input(input, allowed).unwrap();
    for values in [[a, a], [a, b]] {
        let fact = c.atom(allowed, values.map(Term::Constant)).unwrap();
        c.add_rule(fact, []).unwrap();
    }
    for relation in [input, p] {
        let head = c
            .atom(p, [Term::variable("X", s), Term::Constant(a)])
            .unwrap();
        let body = c
            .atom(relation, [Term::variable("X", s), Term::variable("X", s)])
            .unwrap();
        c.add_rule(head, [Literal::Positive(body)]).unwrap();
    }
    let limits = Limits::default();
    let d = Domains::from([(s, vec![a, b])]);
    let mut full =
        GroundProgram::prepare_completion_enumerated(&c, &d, &mut Budget::new(&limits)).unwrap();
    full.completion_inputs(&c, &mut Budget::new(&limits))
        .unwrap();
    let sparse = GroundProgram::prepare_completion(&c, &d, &mut Budget::new(&limits)).unwrap();
    let universe: Vec<_> = full
        .atoms
        .iter()
        .chain(&sparse.atoms)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(models(&full, &universe), models(&sparse, &universe));
    assert!(!sparse.inputs.contains(&GroundAtom::new(input, [b, b])));
}

#[test]
fn anchored_coordinate_updates_preserve_full_models_with_unanchored_alternatives() {
    for reverse in [false, true] {
        for seeded in [false, true] {
            for alternative in [false, true] {
                let mut c = Corpus::new();
                let s = c.declare_sort("S").unwrap();
                let a = c.declare_constant("a", s).unwrap();
                let z = c.declare_constant("z", s).unwrap();
                let mut names = vec!["p", "q", "free", "anchor"];
                if reverse {
                    names.reverse();
                }
                let mut ids = BTreeMap::new();
                for name in names {
                    ids.insert(
                        name,
                        c.declare_relation(name, RelationRole::Derived, [Parameter::new("x", s)])
                            .unwrap(),
                    );
                }
                let mut add = |head: &str, body: &[&str]| {
                    let h = c.atom(ids[head], [Term::variable("X", s)]).unwrap();
                    let bs = body
                        .iter()
                        .map(|name| {
                            Literal::Positive(c.atom(ids[name], [Term::variable("X", s)]).unwrap())
                        })
                        .collect::<Vec<_>>();
                    c.add_rule(h, bs).unwrap();
                };
                add("p", &["q"]);
                add("q", &["p", "anchor"]);
                add("free", &["free"]);
                if alternative {
                    add("p", &["free"]);
                }
                if seeded {
                    add("q", &["anchor"]);
                }
                let fact = c.atom(ids["anchor"], [Term::Constant(a)]).unwrap();
                c.add_rule(fact, []).unwrap();
                let domains = Domains::from([(s, vec![a, z])]);
                let limits = Limits::default();
                let full = GroundProgram::prepare_completion_enumerated(
                    &c,
                    &domains,
                    &mut Budget::new(&limits),
                )
                .unwrap();
                let sparse =
                    GroundProgram::prepare_completion(&c, &domains, &mut Budget::new(&limits))
                        .unwrap();
                let universe: Vec<_> = full
                    .atoms
                    .iter()
                    .chain(&sparse.atoms)
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                assert_eq!(
                    models(&full, &universe),
                    models(&sparse, &universe),
                    "reverse={reverse}, seeded={seeded}, alternative={alternative}"
                );
                // Scope depends on positive-support liveness, not just model
                // equality. Independently descend the fully enumerated atoms.
                let mut possible: BTreeSet<_> = full.atoms.iter().cloned().collect();
                loop {
                    let next: BTreeSet<_> = full
                        .rules
                        .iter()
                        .filter(|r| {
                            r.body.iter().all(|l| {
                                l.polarity == Polarity::Negative || possible.contains(&l.term.atom)
                            })
                        })
                        .map(|r| r.head.atom.clone())
                        .chain(full.inputs.iter().cloned())
                        .collect();
                    if next == possible {
                        break;
                    }
                    possible = next;
                }
                let identity = |r: &GroundRule| {
                    (
                        r.source,
                        r.head.atom.clone(),
                        r.body
                            .iter()
                            .map(|l| (l.polarity == Polarity::Positive, l.term.atom.clone()))
                            .collect::<Vec<_>>(),
                    )
                };
                let live: BTreeSet<_> = full
                    .rules
                    .iter()
                    .filter(|r| {
                        r.body.iter().all(|l| {
                            l.polarity == Polarity::Negative || possible.contains(&l.term.atom)
                        })
                    })
                    .map(identity)
                    .collect();
                assert_eq!(
                    sparse.rules.iter().map(identity).collect::<BTreeSet<_>>(),
                    live
                );
            }
        }
    }
}

// Compare live instances, not just answers: deleting one support must not delete
// a head that another producer still supports. This oracle grounds the full
// product first and then removes unsupported atoms in synchronous rounds.
fn assert_live_instances_match_dense(c: &Corpus, domains: &Domains) {
    let limits = Limits::default();
    let mut full =
        GroundProgram::prepare_completion_enumerated(c, domains, &mut Budget::new(&limits))
            .unwrap();
    full.completion_inputs(c, &mut Budget::new(&limits))
        .unwrap();
    let mut possible: BTreeSet<_> = full.atoms.iter().cloned().collect();
    loop {
        let next: BTreeSet<_> = full
            .inputs
            .iter()
            .cloned()
            .chain(
                full.rules
                    .iter()
                    .filter(|r| {
                        r.body
                            .iter()
                            .filter(|l| l.polarity == Polarity::Positive)
                            .all(|l| possible.contains(&l.term.atom))
                    })
                    .map(|r| r.head.atom.clone()),
            )
            .collect();
        if next == possible {
            break;
        }
        possible = next;
    }
    let key = |r: &GroundRule| {
        (
            r.source,
            r.head.atom.clone(),
            r.body
                .iter()
                .map(|l| (l.polarity == Polarity::Positive, l.term.atom.clone()))
                .collect::<Vec<_>>(),
        )
    };
    let expected: BTreeSet<_> = full
        .rules
        .iter()
        .filter(|r| {
            r.body
                .iter()
                .filter(|l| l.polarity == Polarity::Positive)
                .all(|l| possible.contains(&l.term.atom))
        })
        .map(key)
        .collect();
    let sparse = GroundProgram::prepare_completion(c, domains, &mut Budget::new(&limits)).unwrap();
    assert_eq!(
        sparse.rules.iter().map(key).collect::<BTreeSet<_>>(),
        expected
    );
}

#[test]
fn shrinking_deltas_preserve_multiple_support_repeated_premises_and_negative_literals() {
    // The edge chain loses its last endpoint, then its predecessors. The other
    // branch remains self-supported. Two occurrences of p can disappear in the
    // same update; projection gives multiple supports for a common head.
    for keep in [false, true] {
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let values: Vec<_> = (0..5)
            .map(|i| c.declare_constant(format!("v{i}"), s).unwrap())
            .collect();
        let p = c
            .declare_relation("p", RelationRole::Derived, [Parameter::new("x", s)])
            .unwrap();
        let q = c
            .declare_relation("q", RelationRole::Derived, [Parameter::new("x", s)])
            .unwrap();
        let edge = c
            .declare_relation(
                "edge",
                RelationRole::Derived,
                [Parameter::new("x", s), Parameter::new("y", s)],
            )
            .unwrap();
        let absent = c
            .declare_relation("absent", RelationRole::Derived, [])
            .unwrap();
        for (x, y) in [(0, 1), (1, 2), (2, 3), (4, 4)] {
            let h = c
                .atom(edge, [Term::Constant(values[x]), Term::Constant(values[y])])
                .unwrap();
            c.add_rule(h, []).unwrap();
        }
        if keep {
            let h = c.atom(p, [Term::Constant(values[3])]).unwrap();
            c.add_rule(h, []).unwrap();
        }
        let x = || Term::variable("X", s);
        let y = || Term::variable("Y", s);
        let h = c.atom(p, [x()]).unwrap();
        let e = c.atom(edge, [x(), y()]).unwrap();
        let pp = c.atom(p, [y()]).unwrap();
        c.add_rule(h, [Literal::Positive(e), Literal::Positive(pp)])
            .unwrap();
        let h = c.atom(q, [x()]).unwrap();
        let a = c.atom(p, [x()]).unwrap();
        let b = c.atom(p, [y()]).unwrap();
        let n = c.atom(absent, []).unwrap();
        c.add_rule(
            h,
            [
                Literal::Positive(a),
                Literal::Positive(b),
                Literal::Negative(n),
            ],
        )
        .unwrap();
        let h = c.atom(p, [x()]).unwrap();
        let b = c.atom(q, [x()]).unwrap();
        let e = c.atom(edge, [x(), x()]).unwrap();
        c.add_rule(h, [Literal::Positive(b), Literal::Positive(e)])
            .unwrap();
        assert_live_instances_match_dense(&c, &Domains::from([(s, values)]));
    }
}

#[test]
fn delta_gfp_agrees_with_dense_oracle_on_generated_small_programs() {
    for seed in 0..96u64 {
        let mut random = seed + 1;
        let mut next = || {
            random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
            random >> 32
        };
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let values: Vec<_> = (0..3)
            .map(|i| c.declare_constant(format!("v{i}"), s).unwrap())
            .collect();
        let rs: Vec<_> = (0..4)
            .map(|i| {
                c.declare_relation(
                    format!("r{i}"),
                    if i == 0 {
                        RelationRole::Input
                    } else {
                        RelationRole::Derived
                    },
                    [Parameter::new("x", s)],
                )
                .unwrap()
            })
            .collect();
        for _ in 0..12 {
            let r = rs[1 + (next() as usize % 3)];
            let head_arg = if next() % 2 == 0 {
                Term::variable("X", s)
            } else {
                Term::Constant(values[next() as usize % 3])
            };
            let head = c.atom(r, [head_arg]).unwrap();
            let mut body = Vec::new();
            for _ in 0..next() % 4 {
                let r = rs[next() as usize % 4];
                let arg = match next() % 3 {
                    0 => Term::variable("X", s),
                    1 => Term::variable("Y", s),
                    _ => Term::Constant(values[next() as usize % 3]),
                };
                let atom = c.atom(r, [arg]).unwrap();
                body.push(if next() % 4 == 0 {
                    Literal::Negative(atom)
                } else {
                    Literal::Positive(atom)
                });
            }
            // Bind both possible variable names through the eligible input.
            for name in ["X", "Y"] {
                body.push(Literal::Positive(
                    c.atom(rs[0], [Term::variable(name, s)]).unwrap(),
                ));
            }
            c.add_rule(head, body).unwrap();
        }
        assert_live_instances_match_dense(&c, &Domains::from([(s, values)]));
    }
}
