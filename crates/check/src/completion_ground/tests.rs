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
