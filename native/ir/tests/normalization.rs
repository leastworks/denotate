use denotate_ir::installation::*;
use denotate_ir::*;
use denotate_normalize as n;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
enum E {
    Leaf(u8),
    Not(Box<E>),
    And(Box<E>, Box<E>),
    Or(Box<E>, Box<E>),
}
fn expression(e: &E, next: &mut usize) -> n::Expression<u8, usize> {
    let key = *next;
    *next += 1;
    let kind = match e {
        E::Leaf(p) => n::ExpressionKind::Leaf {
            payload: *p,
            arguments: vec![],
        },
        E::Not(a) => n::ExpressionKind::Not(Box::new(expression(a, next))),
        E::And(a, b) => {
            n::ExpressionKind::And(Box::new(expression(a, next)), Box::new(expression(b, next)))
        }
        E::Or(a, b) => {
            n::ExpressionKind::Or(Box::new(expression(a, next)), Box::new(expression(b, next)))
        }
    };
    n::Expression { key, kind }
}
fn recipe(e: &E) -> n::Recipe<u8, u8, usize> {
    n::normalize(&n::Definition {
        head: n::Atom {
            key: usize::MAX,
            payload: 2,
            arguments: vec![],
        },
        body: Some(expression(e, &mut 0)),
    })
    .unwrap()
}
fn classical(e: &E, world: u8) -> bool {
    match e {
        E::Leaf(p) => world & (1 << p) != 0,
        E::Not(a) => !classical(a, world),
        E::And(a, b) => classical(a, world) && classical(b, world),
        E::Or(a, b) => classical(a, world) || classical(b, world),
    }
}
// Independent normal-program reduct oracle. No checker or normalization calls.
fn stable_models(c: &Corpus, present: &BTreeSet<RelationId>) -> Vec<BTreeSet<RelationId>> {
    let derived: Vec<_> = c
        .relations()
        .filter(|r| r.role == RelationRole::Derived)
        .map(|r| r.id)
        .collect();
    assert!(derived.len() < 12);
    (0..1usize << derived.len())
        .filter_map(|bits| {
            let mut candidate = present.clone();
            candidate.extend(
                derived
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, r)| *r),
            );
            let reduct: Vec<_> = c
                .rules()
                .filter(|r| {
                    r.body.iter().all(
                        |l| !matches!(l,Literal::Negative(a) if candidate.contains(&a.relation())),
                    )
                })
                .collect();
            let mut least = present.clone();
            loop {
                let old = least.len();
                for r in &reduct {
                    if r.body.iter().all(|l| match l {
                        Literal::Positive(a) => least.contains(&a.relation()),
                        Literal::Negative(_) => true,
                    }) {
                        least.insert(r.head.relation());
                    }
                }
                if least.len() == old {
                    break;
                }
            }
            (least == candidate).then_some(candidate)
        })
        .collect()
}
#[test]
fn all_small_ground_expressions_match_classical_truth_in_unique_stable_models() {
    // Exhaust every expression over two leaves with 1..=6 syntax nodes;
    // all four input worlds, including absent leaves, independently evaluated.
    let mut sizes = vec![vec![], vec![E::Leaf(0), E::Leaf(1)]];
    for size in 2..=6 {
        let mut es: Vec<_> = sizes[size - 1]
            .iter()
            .map(|a| E::Not(Box::new(a.clone())))
            .collect();
        for left in 1..size - 1 {
            for a in &sizes[left] {
                for b in &sizes[size - 1 - left] {
                    es.push(E::And(Box::new(a.clone()), Box::new(b.clone())));
                    es.push(E::Or(Box::new(a.clone()), Box::new(b.clone())));
                }
            }
        }
        sizes.push(es);
    }
    let count: usize = sizes.iter().map(Vec::len).sum();
    for e in sizes.iter().flatten() {
        let mut c = Corpus::new();
        let a = c
            .declare_relation("external_alpha", RelationRole::Input, [])
            .unwrap();
        let b = c
            .declare_relation("external_beta", RelationRole::Input, [])
            .unwrap();
        let result = c
            .declare_relation("answer", RelationRole::Derived, [])
            .unwrap();
        let bindings = |p: &u8| {
            Ok(BoundAtom {
                relation: [a, b, result][*p as usize],
                arguments: vec![],
            })
        };
        install(&mut c, &recipe(e), bindings, bindings).unwrap();
        for world in 0..4 {
            let present = [a, b]
                .into_iter()
                .enumerate()
                .filter(|(i, _)| world & (1 << i) != 0)
                .map(|(_, r)| r)
                .collect();
            let models = stable_models(&c, &present);
            assert_eq!(models.len(), 1, "{e:?}, world {world}");
            assert_eq!(
                models[0].contains(&result),
                classical(e, world),
                "{e:?}, world {world}"
            );
        }
    }
    assert_eq!(count, 556);
}
#[test]
fn generated_namespace_is_independent_of_frontend_declaration_order() {
    for frontend_first in [true, false] {
        let mut c = Corpus::new();
        let mut user = None;
        if frontend_first {
            user = Some(
                c.declare_relation("$condition_1", RelationRole::Input, [])
                    .unwrap(),
            );
        }
        let generated = c.declare_generated_relation();
        if !frontend_first {
            user = Some(
                c.declare_relation("$condition_1", RelationRole::Input, [])
                    .unwrap(),
            );
        }
        let user = user.unwrap();
        assert_ne!(user, generated);
        assert_eq!(
            c.relation(user).unwrap().name,
            c.relation(generated).unwrap().name
        );
        assert!(c.is_generated_relation(generated));
        assert!(!c.is_generated_relation(user));
        assert!(matches!(
            c.declare_relation("$condition_1", RelationRole::Input, []),
            Err(ConstructionError::DuplicateName { .. })
        ));
        let second = c.declare_generated_relation();
        assert_eq!(c.relation(second).unwrap().name, "$condition_2");
    }
}
#[test]
fn independent_attribution_policies_transfer_many_to_many_to_fresh_occurrences() {
    let r = recipe(&E::Not(Box::new(E::Not(Box::new(E::Leaf(0))))));
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///generic", 1, "other-dsl", "not not x")
        .unwrap();
    let mut outputs = vec![];
    for outer in [true, false] {
        let mut c = Corpus::new();
        let input = c.declare_relation("x", RelationRole::Input, []).unwrap();
        let result = c
            .declare_relation("answer", RelationRole::Derived, [])
            .unwrap();
        let binding = |p: &u8| {
            Ok(BoundAtom {
                relation: if *p == 2 { result } else { input },
                arguments: vec![],
            })
        };
        let installed = install(&mut c, &r, binding, binding).unwrap();
        let (local, records) = r
            .records()
            .iter()
            .find(|(_, rs)| rs[0].kind == n::OutputKind::Literal)
            .unwrap();
        assert_eq!(records[0].negations, [0, 1]);
        let origin = Origin::new(
            sources
                .span(snapshot, if outer { 0..9 } else { 8..9 })
                .unwrap(),
        );
        let mut assignments = BTreeMap::new();
        assignments.insert(
            *local,
            vec![
                origin.clone(),
                Origin::new(sources.span(snapshot, 4..9).unwrap()),
            ],
        );
        let mut provenance = Provenance::new();
        installed
            .transfer(&c, &sources, &mut provenance, &assignments)
            .unwrap();
        let id = installed.occurrences()[local];
        assert_eq!(provenance.origins(id).len(), 2);
        assert_eq!(provenance.origins(id)[0], origin);
        outputs.push(id);
    }
    assert_ne!(outputs[0], outputs[1]);
}
#[test]
fn binding_cannot_hide_a_variable_from_capture_checks_and_rule_safety_is_retained() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("Thing").unwrap();
    let input = c
        .declare_relation("q", RelationRole::Input, [Parameter::new("x", sort)])
        .unwrap();
    let result = c.declare_relation("p", RelationRole::Derived, []).unwrap();
    let build = |variable| {
        n::normalize(&n::Definition {
            head: n::Atom {
                key: 0,
                payload: (),
                arguments: vec![],
            },
            body: Some(n::Expression {
                key: 1,
                kind: n::ExpressionKind::Not(Box::new(n::Expression {
                    key: 2,
                    kind: n::ExpressionKind::Leaf {
                        payload: (),
                        arguments: vec![n::Argument { key: 3, variable }],
                    },
                })),
            }),
        })
        .unwrap()
    };
    for variable in [false, true] {
        let err = install(
            &mut c,
            &build(variable),
            |_| {
                Ok(BoundAtom {
                    relation: result,
                    arguments: vec![],
                })
            },
            |_| {
                Ok(BoundAtom {
                    relation: input,
                    arguments: vec![Term::variable("X", sort)],
                })
            },
        )
        .unwrap_err();
        if variable {
            assert!(matches!(
                err,
                InstallError::Construction(ConstructionError::UnsafeVariable { .. })
            ));
        } else {
            assert!(matches!(err, InstallError::InvalidBinding(_)));
        }
    }
}
