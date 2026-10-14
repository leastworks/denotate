use crate::*;
use denotate_ir::*;
use std::collections::BTreeSet;

pub(super) fn assert_equivalent(corpus: &Corpus, domains: &Domains, sparse: &GroundProgram) {
    let limits = Limits::default();
    let full = GroundProgram::prepare_cartesian(corpus, domains, &limits).unwrap();
    assert_eq!(sparse.is_admitted(), full.is_admitted());
    let inputs: Vec<_> = full.input_atoms().cloned().collect();
    assert!(
        inputs.len() <= 10,
        "exhaustive oracle is for small input spaces"
    );
    for bits in 0..(1usize << inputs.len()) {
        let observation: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter(|(i, _)| bits & (1 << i) != 0)
            .map(|(_, a)| a.clone())
            .collect();
        let actual = sparse.evaluate(observation.clone(), &limits).unwrap();
        let expected = full.evaluate(observation, &limits).unwrap();
        for atom in full.atoms() {
            match (actual.fact(atom).unwrap(), expected.fact(atom).unwrap()) {
                (FactState::Settled(a), FactState::Settled(b)) => {
                    assert_eq!(a, b, "{atom:?}, observation {bits}")
                }
                (FactState::Blocked(a), FactState::Blocked(b)) => {
                    let actual_roots: BTreeSet<_> = a
                        .iter()
                        .map(|id| sparse.component(*id).unwrap().atoms.clone())
                        .collect();
                    let expected_roots: BTreeSet<_> = b
                        .iter()
                        .map(|id| full.component(*id).unwrap().atoms.clone())
                        .collect();
                    assert_eq!(actual_roots, expected_roots, "{atom:?}, observation {bits}");
                }
                states => panic!("{atom:?}, observation {bits}: {states:?}"),
            }
        }
    }
}

fn relation(c: &mut Corpus, name: &str, role: RelationRole, sorts: &[SortId]) -> RelationId {
    c.declare_relation(
        name,
        role,
        sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| Parameter::new(format!("c{i}"), *sort)),
    )
    .unwrap()
}

fn add_rule(
    c: &mut Corpus,
    head: (RelationId, Vec<Term>),
    body: Vec<(RelationId, Vec<Term>, bool)>,
) -> RuleId {
    let head = c.atom(head.0, head.1).unwrap();
    let body: Vec<_> = body
        .into_iter()
        .map(|(relation, terms, negative)| {
            let atom = c.atom(relation, terms).unwrap();
            if negative {
                Literal::Negative(atom)
            } else {
                Literal::Positive(atom)
            }
        })
        .collect();
    c.add_rule(head, body).unwrap()
}

#[test]
fn impossible_negation_has_evidence_without_a_node_and_invalid_atoms_remain_errors() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let t = c.declare_sort("T").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let outside = c.declare_constant("outside", s).unwrap();
    let wrong = c.declare_constant("wrong", t).unwrap();
    let dead = relation(&mut c, "dead", RelationRole::Derived, &[s]);
    let yes = relation(&mut c, "yes", RelationRole::Derived, &[]);
    // A syntactic producer exists, but has no seed in the positive closure.
    add_rule(
        &mut c,
        (dead, vec![a.into()]),
        vec![(dead, vec![a.into()], false)],
    );
    let source = add_rule(&mut c, (yes, vec![]), vec![(dead, vec![a.into()], true)]);
    let domains = Domains::from([(s, vec![a]), (t, vec![wrong])]);
    let p = GroundProgram::prepare(&c, &domains, &Limits::default()).unwrap();
    assert_equivalent(&c, &domains, &p);
    assert_eq!(p.atoms().count(), 1);
    assert_eq!(p.rules().count(), 1);
    assert_eq!(p.dependencies().count(), 0);
    let atom = GroundAtom::new(dead, [a]);
    assert!(!p.is_possible(&atom).unwrap());
    let replay = p.evaluate([], &Limits::default()).unwrap();
    assert_eq!(replay.fact(&atom).unwrap(), FactState::Settled(false));
    assert_eq!(
        replay.absence_provider(&atom).unwrap(),
        Some(CompletedProvider::NoPossibleProducer)
    );
    let Evidence::Derived { premises, .. } = &replay
        .derivation(&GroundAtom::new(yes, []))
        .unwrap()
        .evidence
    else {
        panic!()
    };
    assert_eq!(
        premises,
        &vec![PremiseEvidence::Absent {
            fact: atom,
            occurrence: c.rule(source).unwrap().body[0].atom().id(),
            provider: CompletedProvider::NoPossibleProducer,
        }]
    );
    let mut foreign = Corpus::new();
    let foreign_r = relation(&mut foreign, "dead", RelationRole::Derived, &[]);
    for invalid in [
        GroundAtom::new(dead, []),
        GroundAtom::new(dead, [a, a]),
        GroundAtom::new(dead, [outside]),
        GroundAtom::new(dead, [wrong]),
        GroundAtom::new(foreign_r, []),
    ] {
        assert!(matches!(
            replay.fact(&invalid),
            Err(CheckError::UnknownAtom(_))
        ));
        assert!(matches!(
            replay.absence_provider(&invalid),
            Err(CheckError::UnknownAtom(_))
        ));
    }
}

#[test]
fn dead_instances_can_remove_a_negative_cycle_and_its_downstream_blocking() {
    for seed in ["none", "fact", "input"] {
        let mut c = Corpus::new();
        let dead = relation(
            &mut c,
            "dead",
            if seed == "input" {
                RelationRole::Input
            } else {
                RelationRole::Derived
            },
            &[],
        );
        let cycle = relation(&mut c, "cycle", RelationRole::Derived, &[]);
        let downstream = relation(&mut c, "downstream", RelationRole::Derived, &[]);
        add_rule(
            &mut c,
            (cycle, vec![]),
            vec![(dead, vec![], false), (cycle, vec![], true)],
        );
        add_rule(&mut c, (downstream, vec![]), vec![(cycle, vec![], true)]);
        if seed == "fact" {
            add_rule(&mut c, (dead, vec![]), vec![]);
        }
        let limits = Limits::default();
        let sparse = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let full = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
        assert!(!full.is_admitted());
        assert_eq!(sparse.is_admitted(), seed == "none");
        if seed != "none" {
            assert_equivalent(&c, &Domains::new(), &sparse);
        } else {
            let a = sparse.evaluate([], &limits).unwrap();
            let b = full.evaluate([], &limits).unwrap();
            assert_eq!(
                a.fact(&GroundAtom::new(cycle, [])).unwrap(),
                FactState::Settled(false)
            );
            assert_eq!(
                a.fact(&GroundAtom::new(downstream, [])).unwrap(),
                FactState::Settled(true)
            );
            for r in [cycle, downstream] {
                assert!(matches!(
                    b.fact(&GroundAtom::new(r, [])).unwrap(),
                    FactState::Blocked(_)
                ));
            }
        }
    }
}

#[test]
fn repeated_arrivals_deduplicate_bindings_but_not_authored_rules() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let input = relation(&mut c, "input", RelationRole::Input, &[s]);
    let left = relation(&mut c, "left", RelationRole::Derived, &[s]);
    let right = relation(&mut c, "right", RelationRole::Derived, &[s]);
    let out = relation(&mut c, "out", RelationRole::Derived, &[]);
    let x = Term::variable("X", s);
    for rel in [left, right] {
        add_rule(
            &mut c,
            (rel, vec![x.clone()]),
            vec![(input, vec![x.clone()], false)],
        );
    }
    let mut sources = Vec::new();
    for _ in 0..2 {
        sources.push(add_rule(
            &mut c,
            (out, vec![]),
            vec![
                (left, vec![x.clone()], false),
                (right, vec![x.clone()], false),
                (left, vec![x.clone()], false),
            ],
        ));
    }
    let domains = Domains::from([(s, vec![b, a])]);
    let p = GroundProgram::prepare(&c, &domains, &Limits::default()).unwrap();
    assert_equivalent(&c, &domains, &p);
    for source in sources {
        assert_eq!(p.rules().filter(|r| r.source == source).count(), 2);
    }
    assert_eq!(p.rules().count(), 8);
    let again =
        GroundProgram::prepare_reversed(&c, &Domains::from([(s, vec![a, b])]), &Limits::default())
            .unwrap();
    assert_eq!(
        p.atoms().collect::<Vec<_>>(),
        again.atoms().collect::<Vec<_>>()
    );
    assert_eq!(
        p.rules()
            .map(|r| (r.source, &r.head, &r.body))
            .collect::<Vec<_>>(),
        again
            .rules()
            .map(|r| (r.source, &r.head, &r.body))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        p.components().map(|c| &c.atoms).collect::<Vec<_>>(),
        again.components().map(|c| &c.atoms).collect::<Vec<_>>()
    );
    let observation = [GroundAtom::new(input, [a]), GroundAtom::new(input, [b])];
    let first = p.evaluate(observation.clone(), &Limits::default()).unwrap();
    let second = again
        .evaluate(observation.into_iter().rev(), &Limits::default())
        .unwrap();
    for fact in first.established_facts() {
        let a = first.derivation(fact).unwrap();
        let b = second.derivation(fact).unwrap();
        assert_eq!(a.order, b.order);
        if let (Evidence::Derived { rule: ar, .. }, Evidence::Derived { rule: br, .. }) =
            (&a.evidence, &b.evidence)
        {
            assert_eq!(p.rule(*ar).unwrap().source, again.rule(*br).unwrap().source);
        }
    }
}

pub(super) fn mapping_corpus(size: usize, chained_guards: bool) -> (Corpus, Domains) {
    let mut c = Corpus::new();
    let i = c.declare_sort("Inputs").unwrap();
    let s = c.declare_sort("Slots").unwrap();
    let inputs: Vec<_> = (0..size)
        .map(|n| c.declare_constant(format!("i{n}"), i).unwrap())
        .collect();
    let slots: Vec<_> = (0..size)
        .map(|n| c.declare_constant(format!("s{n}"), s).unwrap())
        .collect();
    let present = relation(&mut c, "present", RelationRole::Input, &[i]);
    let mapped = relation(&mut c, "mapped_to", RelationRole::Derived, &[i, s]);
    let supplies = relation(&mut c, "supplies", RelationRole::Derived, &[i, s]);
    let available = relation(&mut c, "available", RelationRole::Derived, &[s]);
    let iv = Term::variable("I", i);
    let sv = Term::variable("S", s);
    add_rule(
        &mut c,
        (supplies, vec![iv.clone(), sv.clone()]),
        vec![
            (mapped, vec![iv.clone(), sv.clone()], false),
            (present, vec![iv.clone()], false),
        ],
    );
    add_rule(
        &mut c,
        (available, vec![sv.clone()]),
        vec![(supplies, vec![iv, sv], false)],
    );
    for n in 0..size {
        let body = if chained_guards && n > 0 {
            vec![(available, vec![slots[n - 1].into()], false)]
        } else {
            vec![]
        };
        add_rule(
            &mut c,
            (mapped, vec![inputs[n].into(), slots[n].into()]),
            body,
        );
    }
    c.at_most_one("one", supplies, [Column::Index(1)], "one per Slot")
        .unwrap();
    (c, Domains::from([(i, inputs), (s, slots)]))
}

#[test]
fn mapping_grounding_and_constant_guard_dispatch_have_linear_work_and_size() {
    for chained in [false, true] {
        for size in [20, 200, 2_000] {
            let (c, domains) = mapping_corpus(size, chained);
            let limits = Limits {
                max_atoms: 4 * size,
                max_rules: 3 * size,
                max_dependencies: 4 * size,
                // At 2,000 this is 1.2M: both 4M pair enumeration and 4M
                // tuple/consumer nested scans fail even at one tick per visit.
                max_work: 600 * size,
                ..Limits::default()
            };
            let p = GroundProgram::prepare(&c, &domains, &limits).unwrap();
            assert_eq!(p.atoms().count(), 4 * size);
            assert_eq!(p.rules().count(), 3 * size);
            assert_eq!(
                p.dependencies().count(),
                3 * size + if chained { size - 1 } else { 0 }
            );
            assert_eq!(p.at_most_one_groups().count(), 0);
            assert!(p.is_admitted());
        }
    }
}

#[test]
fn groups_use_possible_tuple_keys_and_retain_blocked_candidates() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let values: Vec<_> = (0..2_000)
        .map(|n| c.declare_constant(format!("v{n}"), s).unwrap())
        .collect();
    let r = relation(&mut c, "r", RelationRole::Derived, &[s, s, s]);
    let tuple = |a, b, d| {
        vec![
            Term::from(values[a]),
            Term::from(values[b]),
            Term::from(values[d]),
        ]
    };
    for _ in 0..2 {
        add_rule(&mut c, (r, tuple(0, 1, 2)), vec![]);
    }
    add_rule(&mut c, (r, tuple(3, 1, 2)), vec![(r, tuple(3, 1, 2), true)]);
    add_rule(&mut c, (r, tuple(4, 5, 6)), vec![]); // singleton
    let obligation = c
        .at_most_one("one", r, [Column::Index(2), Column::Index(1)], "one")
        .unwrap();
    let p = GroundProgram::prepare(
        &c,
        &Domains::from([(s, values.clone())]),
        &Limits {
            max_atoms: 3,
            max_rules: 4,
            max_work: 20_000,
            ..Limits::default()
        },
    )
    .unwrap();
    let groups: Vec<_> = p.at_most_one_groups().collect();
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].obligation, obligation);
    assert_eq!(groups[0].key, vec![values[2], values[1]]);
    assert_eq!(groups[0].tuples.len(), 2);
    assert!(!p.is_admitted());
    assert!(
        !p.component_for(&groups[0].tuples[1])
            .unwrap()
            .blocked_by
            .is_empty()
    );
}

#[test]
fn unseeded_signed_graphs_match_cartesian_over_every_observation() {
    for shape in 0..81 {
        let mut c = Corpus::new();
        let input = relation(&mut c, "input", RelationRole::Input, &[]);
        let rel = [
            relation(&mut c, "a", RelationRole::Derived, &[]),
            relation(&mut c, "b", RelationRole::Derived, &[]),
        ];
        let mut choices = shape;
        for from in rel {
            for to in rel {
                let sign = choices % 3;
                choices /= 3;
                if sign != 0 {
                    add_rule(&mut c, (from, vec![]), vec![(to, vec![], sign == 2)]);
                }
            }
        }
        // The unused input exercises both observations without seeding recursion.
        assert_eq!(c.relation(input).unwrap().role, RelationRole::Input);
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        assert_equivalent(&c, &Domains::new(), &p);
    }
}

#[test]
fn joins_handle_constants_repeated_variables_and_independent_products() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let pair = relation(&mut c, "pair", RelationRole::Input, &[s, s]);
    let unary = relation(&mut c, "unary", RelationRole::Input, &[s]);
    let out = relation(&mut c, "out", RelationRole::Derived, &[s, s]);
    let x = Term::variable("X", s);
    let y = Term::variable("Y", s);
    add_rule(
        &mut c,
        (out, vec![x.clone(), y.clone()]),
        vec![
            (pair, vec![x.clone(), x.clone()], false),
            (unary, vec![y], false), // a genuine independent product
            (pair, vec![a.into(), x], true),
        ],
    );
    let domains = Domains::from([(s, vec![a, b])]);
    let p = GroundProgram::prepare(&c, &domains, &Limits::default()).unwrap();
    assert_eq!(p.rules().count(), 4);
    assert_equivalent(&c, &domains, &p);
    assert_eq!(p.input_atoms().count(), 6); // binary inputs retain their full product
    let unique: BTreeSet<_> = p.rules().map(|r| &r.head.atom).collect();
    assert_eq!(unique.len(), 4);
}

#[test]
fn recursive_joins_match_warshall_over_all_three_node_graphs_and_input_worlds() {
    // Independent oracle over the fixture's adjacency matrix, not grounded IR.
    // Do not seed the diagonal: a node reaches itself only via a nonempty path.
    fn closure(mut edges: [[bool; 3]; 3]) -> [[bool; 3]; 3] {
        for via in 0..3 {
            for from in 0..3 {
                for to in 0..3 {
                    edges[from][to] |= edges[from][via] && edges[via][to];
                }
            }
        }
        edges
    }

    let limits = Limits::default();
    let mut worlds = 0;
    for graph in 0u32..512 {
        let mut c = Corpus::new();
        let node = c.declare_sort("Node").unwrap();
        let nodes: Vec<_> = (0..3)
            .map(|n| c.declare_constant(format!("n{n}"), node).unwrap())
            .collect();
        let active = relation(&mut c, "active", RelationRole::Input, &[node]);
        let edge = relation(&mut c, "edge", RelationRole::Derived, &[node, node]);
        let path = relation(&mut c, "path", RelationRole::Derived, &[node, node]);
        let x = Term::variable("X", node);
        let y = Term::variable("Y", node);
        let z = Term::variable("Z", node);
        // path(X, Y) :- edge(X, Y), active(X).
        let direct = add_rule(
            &mut c,
            (path, vec![x.clone(), y.clone()]),
            vec![
                (edge, vec![x.clone(), y.clone()], false),
                (active, vec![x.clone()], false),
            ],
        );
        // Both sides of this join grow recursively.
        // path(X, Z) :- path(X, Y), path(Y, Z).
        let transitive = add_rule(
            &mut c,
            (path, vec![x.clone(), z.clone()]),
            vec![(path, vec![x, y.clone()], false), (path, vec![y, z], false)],
        );
        let mut edges = [[false; 3]; 3];
        for from in 0..3 {
            for to in 0..3 {
                edges[from][to] = graph & (1 << (3 * from + to)) != 0;
                if edges[from][to] {
                    add_rule(
                        &mut c,
                        (edge, vec![nodes[from].into(), nodes[to].into()]),
                        vec![],
                    );
                }
            }
        }
        let p =
            GroundProgram::prepare(&c, &Domains::from([(node, nodes.clone())]), &limits).unwrap();
        let possible = closure(edges); // All three input nodes may be active.
        super::symbolic::assert_symbolic_agrees(&p);
        assert!(p.is_admitted(), "graph {graph}");
        assert_eq!(
            p.rules().filter(|r| r.source == direct).count(),
            graph.count_ones() as usize,
            "direct instances, graph {graph}"
        );
        let mut triples = 0;
        for from in 0..3 {
            for via in 0..3 {
                for to in 0..3 {
                    triples += usize::from(possible[from][via] && possible[via][to]);
                }
            }
        }
        assert_eq!(
            p.rules().filter(|r| r.source == transitive).count(),
            triples,
            "recursive instances, graph {graph}"
        );

        for bits in 0..8 {
            let mut observed_edges = edges;
            for (from, row) in observed_edges.iter_mut().enumerate() {
                if bits & (1 << from) == 0 {
                    row.fill(false);
                }
            }
            let expected = closure(observed_edges);
            let observation = (0..3)
                .filter(|n| bits & (1 << n) != 0)
                .map(|n| GroundAtom::new(active, [nodes[n]]));
            let replay = p.evaluate(observation, &limits).unwrap();
            for from in 0..3 {
                for to in 0..3 {
                    let atom = GroundAtom::new(path, [nodes[from], nodes[to]]);
                    assert_eq!(
                        p.is_possible(&atom).unwrap(),
                        possible[from][to],
                        "possible path {from}->{to}, graph {graph}"
                    );
                    assert_eq!(
                        replay.fact(&atom).unwrap(),
                        FactState::Settled(expected[from][to]),
                        "path {from}->{to}, graph {graph}, observation {bits}"
                    );
                }
            }
            worlds += 1;
        }
    }
    assert_eq!(worlds, 4_096);
}
