use crate::*;
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

fn relation(c: &mut Corpus, name: &str, input: bool) -> RelationId {
    c.declare_relation(
        name,
        if input {
            RelationRole::Input
        } else {
            RelationRole::Derived
        },
        [],
    )
    .unwrap()
}
fn atom(r: RelationId) -> GroundAtom {
    GroundAtom::new(r, [])
}
fn rule(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)]) -> RuleId {
    let head = c.atom(head, []).unwrap();
    let body: Vec<_> = body
        .iter()
        .map(|(r, negative)| {
            let a = c.atom(*r, []).unwrap();
            if *negative {
                Literal::Negative(a)
            } else {
                Literal::Positive(a)
            }
        })
        .collect();
    c.add_rule(head, body).unwrap()
}
fn prepare(c: &Corpus) -> GroundProgram {
    let p = GroundProgram::prepare(c, &Domains::new(), &Limits::default()).unwrap();
    super::sparse::assert_equivalent(c, &Domains::new(), &p);
    p
}

#[test]
fn grounding_is_typed_rule_local_and_preserves_every_occurrence() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let t = c.declare_sort("T").unwrap();
    let a = c.declare_constant("same", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let other = c.declare_constant("same", t).unwrap();
    let pair = c
        .declare_relation(
            "pair",
            RelationRole::Input,
            [Parameter::new("left", s), Parameter::new("right", s)],
        )
        .unwrap();
    let out = c
        .declare_relation("out", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let input_t = c
        .declare_relation("input_t", RelationRole::Input, [Parameter::new("x", t)])
        .unwrap();
    let out_t = c
        .declare_relation("out_t", RelationRole::Derived, [Parameter::new("x", t)])
        .unwrap();
    let head = c.atom(out, [Term::variable("X", s)]).unwrap();
    let body = c
        .atom(pair, [Term::variable("X", s), Term::variable("X", s)])
        .unwrap();
    let original = c.add_rule(head, [Literal::Positive(body)]).unwrap();
    let head = c.atom(out_t, [Term::variable("X", t)]).unwrap();
    let body = c.atom(input_t, [Term::variable("X", t)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    let domains = Domains::from([(s, vec![b, a]), (t, vec![other])]);
    let p = GroundProgram::prepare(&c, &domains, &Limits::default()).unwrap();
    super::sparse::assert_equivalent(&c, &domains, &p);
    assert_eq!(p.atoms().count(), 8);
    assert_eq!(p.rules().count(), 3);
    let instances: Vec<_> = p.rules().filter(|r| r.source == original).collect();
    assert_eq!(instances.len(), 2);
    let source = c.rule(original).unwrap();
    for (r, value) in instances.iter().zip([a, b]) {
        assert_eq!(r.head.atom, GroundAtom::new(out, [value]));
        assert_eq!(r.body[0].term.atom, GroundAtom::new(pair, [value, value]));
        assert_eq!(r.head.occurrence, source.head.id());
        assert_eq!(
            r.body[0].term.arguments,
            source.body[0]
                .atom()
                .arguments()
                .iter()
                .map(TermOccurrence::id)
                .collect::<Vec<_>>()
        );
        assert_ne!(r.body[0].term.arguments[0], r.body[0].term.arguments[1]);
    }
    assert_ne!(instances[0].id, instances[1].id);
    let replay = p
        .evaluate(
            [
                GroundAtom::new(pair, [a, b]),
                GroundAtom::new(pair, [b, b]),
                GroundAtom::new(input_t, [other]),
            ],
            &Limits::default(),
        )
        .unwrap();
    assert_eq!(
        replay.fact(&GroundAtom::new(out, [a])).unwrap(),
        FactState::Settled(false)
    );
    assert_eq!(
        replay.fact(&GroundAtom::new(out, [b])).unwrap(),
        FactState::Settled(true)
    );
    assert_eq!(
        replay.fact(&GroundAtom::new(out_t, [other])).unwrap(),
        FactState::Settled(true)
    );
    let again = GroundProgram::prepare(
        &c,
        &Domains::from([(s, vec![a, b]), (t, vec![other])]),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        p.atoms().collect::<Vec<_>>(),
        again.atoms().collect::<Vec<_>>()
    );
    assert_eq!(
        p.rules()
            .map(|r| (&r.head.atom, r.source))
            .collect::<Vec<_>>(),
        again
            .rules()
            .map(|r| (&r.head.atom, r.source))
            .collect::<Vec<_>>()
    );
    assert!(again.rule(instances[0].id).is_none());
    assert!(again.component(p.components().next().unwrap().id).is_none());
}

#[test]
fn body_only_variables_get_all_ground_instances_and_empty_domains_stay_empty() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let input = c
        .declare_relation("input", RelationRole::Input, [Parameter::new("x", s)])
        .unwrap();
    let exists = relation(&mut c, "exists", false);
    let fact = relation(&mut c, "fact", false);
    let head = c.atom(exists, []).unwrap();
    let body = c.atom(input, [Term::variable("X", s)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    rule(&mut c, fact, &[]);
    for (values, expected) in [(vec![], false), (vec![a], true)] {
        let p = GroundProgram::prepare(
            &c,
            &Domains::from([(s, values.clone())]),
            &Limits::default(),
        )
        .unwrap();
        super::sparse::assert_equivalent(&c, &Domains::from([(s, values.clone())]), &p);
        assert_eq!(p.rules().count(), 1 + values.len());
        let r = p
            .evaluate(
                values.iter().map(|a| GroundAtom::new(input, [*a])),
                &Limits::default(),
            )
            .unwrap();
        assert_eq!(r.fact(&atom(exists)).unwrap(), FactState::Settled(expected));
        assert_eq!(r.fact(&atom(fact)).unwrap(), FactState::Settled(true));
    }
}

#[test]
fn domains_reject_missing_foreign_duplicate_and_wrong_sort_values() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let t = c.declare_sort("T").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", t).unwrap();
    let r = c
        .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let head = c.atom(r, [a.into()]).unwrap();
    c.add_fact(head).unwrap();
    let limits = Limits::default();
    for domains in [
        Domains::new(),
        Domains::from([(s, vec![a])]),
        Domains::from([(s, vec![a, a]), (t, vec![])]),
        Domains::from([(s, vec![b]), (t, vec![b])]),
    ] {
        assert!(matches!(
            GroundProgram::prepare(&c, &domains, &limits),
            Err(CheckError::InvalidDomain { .. })
        ));
    }
    assert!(
        matches!(GroundProgram::prepare(&c, &Domains::from([(s, vec![]), (t, vec![])]), &limits), Err(CheckError::ConstantOutsideDomain(id)) if id == a)
    );
    let mut other = Corpus::new();
    let other_s = other.declare_sort("S").unwrap();
    let other_a = other.declare_constant("a", other_s).unwrap();
    for domains in [
        Domains::from([(other_s, vec![other_a])]),
        Domains::from([(s, vec![other_a]), (t, vec![])]),
    ] {
        assert!(matches!(
            GroundProgram::prepare(&c, &domains, &limits),
            Err(CheckError::InvalidDomain { .. })
        ));
    }
}

#[test]
fn observations_are_only_ground_input_facts_and_omission_means_absence() {
    let mut c = Corpus::new();
    let input = relation(&mut c, "input", true);
    let derived = relation(&mut c, "derived", false);
    rule(&mut c, derived, &[(input, false)]);
    let p = prepare(&c);
    let empty = p.evaluate([], &Limits::default()).unwrap();
    assert_eq!(empty.fact(&atom(input)).unwrap(), FactState::Settled(false));
    assert_eq!(
        empty.fact(&atom(derived)).unwrap(),
        FactState::Settled(false)
    );
    let full = p
        .evaluate([atom(input), atom(input)], &Limits::default())
        .unwrap();
    assert_eq!(full.present_inputs().count(), 1);
    assert_eq!(full.fact(&atom(derived)).unwrap(), FactState::Settled(true));
    assert!(matches!(
        p.evaluate([atom(derived)], &Limits::default()),
        Err(CheckError::InvalidObservation(_))
    ));
    let mut foreign = Corpus::new();
    let foreign_input = relation(&mut foreign, "input", true);
    assert!(matches!(
        p.evaluate([atom(foreign_input)], &Limits::default()),
        Err(CheckError::InvalidObservation(_))
    ));
    assert!(matches!(
        empty.fact(&atom(foreign_input)),
        Err(CheckError::UnknownAtom(_))
    ));
}

#[test]
fn positive_cycles_have_no_ghosts_and_keep_grounded_first_evidence_when_seeded() {
    let mut c = Corpus::new();
    let p = relation(&mut c, "p", false);
    let q = relation(&mut c, "q", false);
    let p_from_q = rule(&mut c, p, &[(q, false)]);
    let q_from_p = rule(&mut c, q, &[(p, false)]);
    let unseeded = prepare(&c);
    assert!(unseeded.is_admitted());
    let r = unseeded.evaluate([], &Limits::default()).unwrap();
    assert_eq!(r.fact(&atom(p)).unwrap(), FactState::Settled(false));
    assert_eq!(r.fact(&atom(q)).unwrap(), FactState::Settled(false));
    let seed = rule(&mut c, p, &[]);
    let duplicate = rule(&mut c, p, &[]);
    let seeded = prepare(&c);
    assert_eq!(seeded.rules().count(), 4);
    let r = seeded.evaluate([], &Limits::default()).unwrap();
    assert_eq!(r.established_facts().count(), 2);
    let evidence_p = r.derivation(&atom(p)).unwrap();
    let evidence_q = r.derivation(&atom(q)).unwrap();
    let Evidence::Derived { rule: id, premises } = &evidence_p.evidence else {
        panic!()
    };
    assert_eq!(seeded.rule(*id).unwrap().source, seed);
    assert!(premises.is_empty());
    assert_ne!(seeded.rule(*id).unwrap().source, p_from_q);
    assert_ne!(seeded.rule(*id).unwrap().source, duplicate);
    let Evidence::Derived { rule: id, premises } = &evidence_q.evidence else {
        panic!()
    };
    assert_eq!(seeded.rule(*id).unwrap().source, q_from_p);
    assert!(matches!(&premises[0], PremiseEvidence::Positive { fact, .. } if *fact == atom(p)));
    assert!(evidence_p.order < evidence_q.order);
}

#[test]
fn ground_stratification_accepts_a_negative_dependency_within_one_relation() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let b = c.declare_constant("b", s).unwrap();
    let r = c
        .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
        .unwrap();
    let head = c.atom(r, [a.into()]).unwrap();
    let body = c.atom(r, [b.into()]).unwrap();
    c.add_rule(head, [Literal::Negative(body)]).unwrap();
    let p =
        GroundProgram::prepare(&c, &Domains::from([(s, vec![a, b])]), &Limits::default()).unwrap();
    super::sparse::assert_equivalent(&c, &Domains::from([(s, vec![a, b])]), &p);
    assert!(p.is_admitted());
    let replay = p.evaluate([], &Limits::default()).unwrap();
    assert_eq!(
        replay.fact(&GroundAtom::new(r, [a])).unwrap(),
        FactState::Settled(true)
    );
    assert_eq!(
        replay.fact(&GroundAtom::new(r, [b])).unwrap(),
        FactState::Settled(false)
    );
}

#[test]
fn negated_premises_only_keep_completed_provider_references() {
    let mut c = Corpus::new();
    let t = relation(&mut c, "t", true);
    let a = relation(&mut c, "a", false);
    let b = relation(&mut c, "b", false);
    let d = relation(&mut c, "d", false);
    rule(&mut c, a, &[(t, false)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, d, &[(t, true)]);
    let p = prepare(&c);
    let replay = p.evaluate([], &Limits::default()).unwrap();
    for (consumer, provider, expected) in [
        (
            b,
            a,
            CompletedProvider::Component(p.component_for(&atom(a)).unwrap().id),
        ),
        (d, t, CompletedProvider::InputSnapshot),
    ] {
        assert_eq!(
            replay.fact(&atom(consumer)).unwrap(),
            FactState::Settled(true)
        );
        let Evidence::Derived { premises, .. } =
            &replay.derivation(&atom(consumer)).unwrap().evidence
        else {
            panic!()
        };
        assert!(
            matches!(&premises[..], [PremiseEvidence::Absent { fact, provider: got, .. }] if *fact == atom(provider) && *got == expected)
        );
        assert_eq!(
            replay.fact(&atom(provider)).unwrap(),
            FactState::Settled(false)
        );
    }
    let replay = p.evaluate([atom(t)], &Limits::default()).unwrap();
    assert_eq!(replay.fact(&atom(a)).unwrap(), FactState::Settled(true));
    assert_eq!(replay.fact(&atom(b)).unwrap(), FactState::Settled(false));
    assert_eq!(replay.fact(&atom(d)).unwrap(), FactState::Settled(false));
}

#[test]
fn cycle_evidence_names_each_ground_rule_and_its_premise_occurrence() {
    let mut c = Corpus::new();
    let p = relation(&mut c, "p", false);
    let q = relation(&mut c, "q", false);
    let r = relation(&mut c, "r", false);
    let rules = [
        rule(&mut c, p, &[(q, true)]),
        rule(&mut c, q, &[(r, false)]),
        rule(&mut c, r, &[(p, false)]),
    ];
    let program = prepare(&c);
    assert!(!program.is_admitted());
    let component = program.component_for(&atom(p)).unwrap();
    let edges = &component.cycle.as_ref().unwrap().edges;
    assert_eq!(edges.len(), 3);
    assert_eq!(edges[0].polarity, Polarity::Negative);
    assert_eq!(
        edges
            .iter()
            .map(|e| program.rule(e.rule).unwrap().source)
            .collect::<BTreeSet<_>>(),
        BTreeSet::from(rules)
    );
    for (edge, next) in edges.iter().zip(edges.iter().cycle().skip(1)) {
        assert_eq!(edge.provider, next.consumer);
        let original = c.rule(program.rule(edge.rule).unwrap().source).unwrap();
        assert_eq!(edge.premise, original.body[0].atom().id());
    }
    let replay = program.evaluate([], &Limits::default()).unwrap();
    assert_eq!(
        replay.fact(&atom(p)).unwrap(),
        FactState::Blocked(BTreeSet::from([component.id]))
    );
    assert!(replay.derivation(&atom(p)).is_none());
}

#[test]
fn blocked_status_propagates_with_both_polarities_without_erasing_independent_facts() {
    let mut c = Corpus::new();
    let p = relation(&mut c, "p", false);
    let q = relation(&mut c, "q", false);
    let r = relation(&mut c, "r", false);
    let t = relation(&mut c, "t", true);
    let ok = relation(&mut c, "ok", false);
    rule(&mut c, p, &[(p, true)]);
    rule(&mut c, q, &[(p, false)]);
    rule(&mut c, r, &[(p, true)]);
    rule(&mut c, ok, &[(t, false)]);
    let program = prepare(&c);
    let root = program.component_for(&atom(p)).unwrap();
    assert_eq!(root.cycle.as_ref().unwrap().edges.len(), 1);
    let replay = program.evaluate([atom(t)], &Limits::default()).unwrap();
    assert!(!replay.is_complete());
    for rel in [p, q, r] {
        assert_eq!(
            replay.fact(&atom(rel)).unwrap(),
            FactState::Blocked(BTreeSet::from([root.id]))
        );
        assert!(replay.derivation(&atom(rel)).is_none());
    }
    assert_eq!(replay.fact(&atom(ok)).unwrap(), FactState::Settled(true));
    assert_eq!(replay.fact(&atom(t)).unwrap(), FactState::Settled(true));
    assert_eq!(replay.established_facts().count(), 2);
}

#[test]
fn blocked_consumers_retain_all_unresolved_roots() {
    let mut c = Corpus::new();
    let a = relation(&mut c, "a", false);
    let b = relation(&mut c, "b", false);
    let out = relation(&mut c, "out", false);
    rule(&mut c, a, &[(a, true)]);
    rule(&mut c, b, &[(b, true)]);
    rule(&mut c, out, &[(a, false), (b, true)]);
    let p = prepare(&c);
    assert_eq!(
        p.component_for(&atom(out)).unwrap().blocked_by,
        BTreeSet::from([
            p.component_for(&atom(a)).unwrap().id,
            p.component_for(&atom(b)).unwrap().id
        ])
    );
}

#[test]
fn resource_limits_cover_grounding_dependencies_graph_and_evaluation() {
    let mut c = Corpus::new();
    let p = relation(&mut c, "p", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, p, &[]); // Keep the cycle possible so every resource is exercised.
    for (limits, resource) in [
        (
            Limits {
                max_atoms: 0,
                ..Limits::default()
            },
            "atoms",
        ),
        (
            Limits {
                max_rules: 0,
                ..Limits::default()
            },
            "rules",
        ),
        (
            Limits {
                max_dependencies: 0,
                ..Limits::default()
            },
            "dependencies",
        ),
        (
            Limits {
                max_work: 0,
                ..Limits::default()
            },
            "work",
        ),
        (
            Limits {
                timeout: Duration::ZERO,
                ..Limits::default()
            },
            "time",
        ),
    ] {
        assert!(
            matches!(GroundProgram::prepare(&c, &Domains::new(), &limits), Err(CheckError::LimitExceeded { resource: got, .. }) if got == resource)
        );
    }
    let prepared = prepare(&c);
    assert!(matches!(
        prepared.evaluate(
            [],
            &Limits {
                max_work: 0,
                ..Limits::default()
            }
        ),
        Err(CheckError::LimitExceeded {
            resource: "work",
            ..
        })
    ));
    let phases: BTreeSet<_> = (1..200)
        .filter_map(|work| {
            match GroundProgram::prepare(
                &c,
                &Domains::new(),
                &Limits {
                    max_work: work,
                    ..Limits::default()
                },
            ) {
                Err(CheckError::LimitExceeded { phase, .. }) => Some(phase),
                _ => None,
            }
        })
        .collect();
    assert!(phases.contains("dependencies"));
    assert!(phases.contains("components"));
}

#[test]
fn long_dependency_chain_uses_iterative_graph_walks_and_provider_order() {
    let mut c = Corpus::new();
    let mut head = relation(&mut c, "r0", false);
    rule(&mut c, head, &[]);
    for n in 1..1500 {
        let next = relation(&mut c, &format!("r{n}"), false);
        rule(&mut c, next, &[(head, false)]);
        head = next;
    }
    let p = prepare(&c);
    assert!(p.is_admitted());
    let order: BTreeMap<_, _> = p.components().enumerate().map(|(i, c)| (c.id, i)).collect();
    for component in p.components() {
        for dependency in &component.dependencies {
            assert!(order[dependency] < order[&component.id]);
        }
    }
    let r = p.evaluate([], &Limits::default()).unwrap();
    assert_eq!(r.fact(&atom(head)).unwrap(), FactState::Settled(true));
    assert_eq!(r.established_facts().count(), 1500);
}

#[test]
fn all_two_node_signed_graphs_agree_with_an_independent_reachability_oracle() {
    for shape in 0..81 {
        let mut c = Corpus::new();
        let rel = [relation(&mut c, "a", false), relation(&mut c, "b", false)];
        // Seed both nodes: this test independently checks SCCs, not possibility.
        for r in rel {
            rule(&mut c, r, &[]);
        }
        let mut choices = shape;
        let mut signs = [[0; 2]; 2];
        let mut reach = [[true, false], [false, true]];
        for from in 0..2 {
            for to in 0..2 {
                signs[from][to] = choices % 3;
                choices /= 3;
                if signs[from][to] != 0 {
                    rule(&mut c, rel[from], &[(rel[to], signs[from][to] == 2)]);
                    reach[from][to] = true;
                }
            }
        }
        // Warshall on the authored edges, not the checker's graph or SCCs.
        for via in 0..2 {
            for from in 0..2 {
                for to in 0..2 {
                    reach[from][to] |= reach[from][via] && reach[via][to];
                }
            }
        }
        let p = prepare(&c);
        for from in 0..2 {
            let blocked =
                (0..2).any(|u| (0..2).any(|v| reach[from][u] && signs[u][v] == 2 && reach[v][u]));
            assert_eq!(
                !p.component_for(&atom(rel[from]))
                    .unwrap()
                    .blocked_by
                    .is_empty(),
                blocked,
                "graph {shape}, node {from}"
            );
            for to in 0..2 {
                assert_eq!(
                    p.component_for(&atom(rel[from])).unwrap().id
                        == p.component_for(&atom(rel[to])).unwrap().id,
                    reach[from][to] && reach[to][from]
                );
            }
        }
    }
}
