use denotate_ir::{installation::*, *};
use denotate_normalize as n;
use std::collections::BTreeMap;

#[test]
fn decoded_paths_distinguish_nested_names_from_a_single_segment() {
    let nested = Namespace::new(["billing", "invoices"]).unwrap();
    let quoted = Namespace::from("billing::invoices");
    assert_eq!(nested.segments(), &["billing", "invoices"]);
    assert_eq!(quoted.segments(), &["billing::invoices"]);
    assert_eq!(
        Namespace::new(["billing", ""]),
        Err(ConstructionError::EmptyName("namespace segment"))
    );
    assert_eq!(
        Namespace::from(""),
        Namespace::new([] as [&str; 0]).unwrap()
    );

    let mut c = Corpus::new();
    let sorts: Vec<_> = [&nested, &quoted]
        .into_iter()
        .map(|ns| c.declare_sort_in(ns, "Item").unwrap())
        .collect();
    assert_ne!(sorts[0], sorts[1]);
    // Identical spelling and the same sort still resolve to distinct constant
    // identities when their namespace paths differ.
    for ns in [&nested, &quoted] {
        let constant = c.declare_constant_in(ns, "item", sorts[0]).unwrap();
        let relation = c
            .declare_relation_in(
                ns,
                "r",
                RelationRole::Input,
                [Parameter::new("x", sorts[0])],
            )
            .unwrap();
        let obligation = c
            .at_most_one_in(ns, "unique", relation, [], "unique")
            .unwrap();
        for id in [
            OccurrenceId::from(constant),
            relation.into(),
            obligation.into(),
        ] {
            assert_eq!(c.namespace(id), Some(ns));
        }
        assert!(matches!(
            c.declare_sort_in(ns, "Item"),
            Err(ConstructionError::DuplicateName { .. })
        ));
        assert!(matches!(
            c.declare_constant_in(ns, "item", sorts[0]),
            Err(ConstructionError::DuplicateName { .. })
        ));
        assert!(matches!(
            c.declare_relation_in(ns, "r", RelationRole::Input, []),
            Err(ConstructionError::DuplicateName { .. })
        ));
        assert!(matches!(
            c.at_most_one_in(ns, "unique", relation, [], ""),
            Err(ConstructionError::DuplicateName { .. })
        ));
    }
    for (id, ns) in sorts.into_iter().zip([&nested, &quoted]) {
        assert_eq!(c.namespace(id), Some(ns));
    }
}

#[test]
fn rules_own_a_namespace_independently_of_their_references_and_sources() {
    let mut c = Corpus::new();
    let owner = Namespace::new(["billing", "invoices"]).unwrap();
    let output = c
        .declare_relation_in("reports", "r", RelationRole::Derived, [])
        .unwrap();
    let input = c
        .declare_relation_in("catalog", "p", RelationRole::Input, [])
        .unwrap();
    let head = c.atom(output, []).unwrap();
    let body = c.atom(input, []).unwrap();
    let body_occurrence = body.id();
    let rule = c
        .add_rule_in(&owner, head, [Literal::Positive(body)])
        .unwrap();
    assert_eq!(c.namespace(rule), Some(&owner));
    assert_eq!(c.namespace(output), Some(&Namespace::from("reports")));
    assert_eq!(c.namespace(input), Some(&Namespace::from("catalog")));
    assert_eq!(c.namespace(body_occurrence), None);

    let mut sources = Sources::new();
    let mut provenance = Provenance::new();
    for uri in ["file:///first.den", "file:///another.flow"] {
        let snapshot = sources.add(uri, 1, "origin", "r").unwrap();
        provenance
            .attach(
                &c,
                &sources,
                rule,
                [Origin::new(sources.span(snapshot, 0..1).unwrap())],
            )
            .unwrap();
    }
    assert_eq!(provenance.origins(rule).len(), 2);
    assert_eq!(c.namespace(rule), Some(&owner));

    let fact = c.atom(output, []).unwrap();
    let fact = c.add_fact_in("shared", fact).unwrap();
    assert!(c.rule(fact).unwrap().is_fact());
    assert_eq!(c.namespace(fact), Some(&Namespace::from("shared")));
    let head = c.atom(input, []).unwrap();
    assert_eq!(
        c.add_fact_in(&owner, head),
        Err(ConstructionError::InputDefinition(input))
    );
    assert_eq!(c.rules().count(), 2);

    let mut foreign = Corpus::new();
    let foreign_relation = foreign.declare_generated_relation_in(&owner);
    let head = foreign.atom(foreign_relation, []).unwrap();
    let foreign_rule = foreign.add_fact_in(&owner, head).unwrap();
    assert_eq!(c.namespace(foreign_relation), None);
    assert_eq!(c.namespace(foreign_rule), None);
    let head = foreign.atom(foreign_relation, []).unwrap();
    assert!(matches!(
        c.add_fact_in(&owner, head),
        Err(ConstructionError::ForeignAtom(_))
    ));
    assert_eq!(c.rules().count(), 2);
}

#[test]
fn helper_namespace_does_not_merge_equal_generated_or_frontend_labels() {
    for generated_first in [false, true] {
        let mut c = Corpus::new();
        let owner = Namespace::new(["billing", "invoices"]).unwrap();
        let mut generated = None;
        if generated_first {
            generated = Some(
                c.declare_generated_relation_named_in(&owner, "$condition_1")
                    .unwrap(),
            );
        }
        let frontend = c
            .declare_relation_in(&owner, "$condition_1", RelationRole::Derived, [])
            .unwrap();
        let generated = generated.unwrap_or_else(|| {
            c.declare_generated_relation_named_in(&owner, "$condition_1")
                .unwrap()
        });
        let duplicate = c
            .declare_generated_relation_named_in(&owner, "$condition_1")
            .unwrap();
        let other = c
            .declare_generated_relation_named_in("elsewhere", "$condition_1")
            .unwrap();
        let arbitrary = c
            .declare_generated_relation_named_in(&owner, "a label with spaces")
            .unwrap();
        assert_ne!(generated, duplicate);
        assert!(!c.is_generated_relation(frontend));
        for id in [generated, duplicate, arbitrary] {
            assert!(c.is_generated_relation(id));
            assert_eq!(c.namespace(id), Some(&owner));
        }
        assert_eq!(c.namespace(other), Some(&Namespace::from("elsewhere")));
        assert!(
            c.declare_relation_in(&owner, "$condition_1", RelationRole::Derived, [])
                .is_err()
        );
        assert!(matches!(
            c.declare_generated_relation_named_in(&owner, ""),
            Err(ConstructionError::EmptyName(_))
        ));
        let head = c.atom(frontend, []).unwrap();
        let one = c.atom(generated, []).unwrap();
        let two = c.atom(duplicate, []).unwrap();
        let rule = c
            .add_rule_in(
                &owner,
                head,
                [Literal::Positive(one), Literal::Negative(two)],
            )
            .unwrap();
        let rule = c.rule(rule).unwrap();
        assert_eq!(rule.head.relation(), frontend);
        assert_eq!(rule.body[0].atom().relation(), generated);
        assert_eq!(rule.body[1].atom().relation(), duplicate);
    }
}

fn helper_recipe() -> n::Recipe<u8, u8, usize> {
    let leaf = |key, payload| n::Expression {
        key,
        kind: n::ExpressionKind::Leaf {
            payload,
            arguments: vec![],
        },
    };
    n::normalize(&n::Definition {
        head: n::Atom {
            key: 0,
            payload: 2,
            arguments: vec![],
        },
        body: Some(n::Expression {
            key: 1,
            kind: n::ExpressionKind::Not(Box::new(n::Expression {
                key: 2,
                kind: n::ExpressionKind::And(Box::new(leaf(3, 0)), Box::new(leaf(4, 1))),
            })),
        }),
    })
    .unwrap()
}

#[test]
fn installation_binds_one_recipe_to_explicit_ir_owners_without_using_references_or_origins() {
    let mut c = Corpus::new();
    let owner = Namespace::new(["billing", "invoices"]).unwrap();
    let left = c
        .declare_relation_in("catalog", "p", RelationRole::Input, [])
        .unwrap();
    let right = c
        .declare_relation_in("shipping", "q", RelationRole::Input, [])
        .unwrap();
    let output = c
        .declare_relation_in("reports", "r", RelationRole::Derived, [])
        .unwrap();
    let bindings = |p: &u8| {
        Ok(BoundAtom {
            relation: [left, right, output][*p as usize],
            arguments: vec![],
        })
    };
    let head = c.atom(output, []).unwrap();
    let trigger = c.add_fact_in(&owner, head).unwrap();
    let inherited = c.namespace(trigger).unwrap().clone();
    let recipe = helper_recipe();
    let recipe_before = recipe.clone();
    let mut sources = Sources::new();
    let mut provenance = Provenance::new();
    let source = sources
        .add("file:///unrelated-name.den", 1, "denotate", "origin")
        .unwrap();
    let origin = Origin::new(sources.span(source, 0..6).unwrap());

    // Reuse the exact cached recipe with an inherited owner, then a caller-chosen
    // shared owner, then the legacy global default. Binding relations never move.
    for (index, ns) in [inherited, Namespace::from("shared"), Namespace::default()]
        .into_iter()
        .enumerate()
    {
        let installed = if ns.is_global() {
            install(&mut c, &recipe, bindings, bindings).unwrap()
        } else {
            install_in(&mut c, &ns, &recipe, bindings, bindings).unwrap()
        };
        assert_eq!(installed.rules().len(), 2);
        for rule in installed.rules().values() {
            assert_eq!(c.namespace(*rule), Some(&ns));
        }
        let helper = c
            .relations()
            .find(|r| {
                c.is_generated_relation(r.id)
                    && installed
                        .occurrences()
                        .values()
                        .any(|id| *id == r.id.into())
            })
            .unwrap()
            .id;
        assert_eq!(c.namespace(helper), Some(&ns));
        assert_eq!(
            c.relation(helper).unwrap().name,
            format!("$condition_{}", index + 1)
        );
        // Verify the installed helper's definition and negative use still refer
        // to this installation's identity, with the supplied external bindings.
        let definition = installed
            .rules()
            .values()
            .map(|id| c.rule(*id).unwrap())
            .find(|r| r.head.relation() == helper)
            .unwrap();
        assert_eq!(
            definition
                .body
                .iter()
                .map(|l| l.atom().relation())
                .collect::<Vec<_>>(),
            [left, right]
        );
        let use_rule = installed
            .rules()
            .values()
            .map(|id| c.rule(*id).unwrap())
            .find(|r| r.head.relation() == output)
            .unwrap();
        assert!(matches!(&use_rule.body[0], Literal::Negative(a) if a.relation() == helper));
        let assignments: BTreeMap<_, _> = installed
            .occurrences()
            .keys()
            .map(|id| (*id, vec![origin.clone()]))
            .collect();
        installed
            .transfer(&c, &sources, &mut provenance, &assignments)
            .unwrap();
        for id in installed.occurrences().values() {
            assert_eq!(provenance.origins(*id), [origin.clone()]);
        }
        assert_eq!(c.namespace(helper), Some(&ns));
        assert_eq!(recipe, recipe_before);
    }
    assert_eq!(c.namespace(left), Some(&Namespace::from("catalog")));
    assert_eq!(c.namespace(right), Some(&Namespace::from("shipping")));
    assert_eq!(c.namespace(output), Some(&Namespace::from("reports")));
}

#[test]
fn legacy_constructors_default_to_global_without_inferring_the_head_namespace() {
    let mut c = Corpus::new();
    let global = Namespace::default();
    let sort = c.declare_sort("S").unwrap();
    let constant = c.declare_constant("c", sort).unwrap();
    let relation = c.declare_relation("r", RelationRole::Derived, []).unwrap();
    let obligation = c.at_most_one("unique", relation, [], "").unwrap();
    let helper = c.declare_generated_relation();
    let named_helper = c.declare_generated_relation_named("arbitrary").unwrap();
    let external = c
        .declare_relation_in("other", "r", RelationRole::Derived, [])
        .unwrap();
    let atom = c.atom(external, []).unwrap();
    let fact = c.add_fact(atom).unwrap();
    let head = c.atom(external, []).unwrap();
    let body = c.atom(helper, []).unwrap();
    let rule = c.add_rule(head, [Literal::Negative(body)]).unwrap();
    for id in [
        OccurrenceId::from(sort),
        constant.into(),
        relation.into(),
        obligation.into(),
        helper.into(),
        named_helper.into(),
        fact.into(),
        rule.into(),
    ] {
        assert_eq!(c.namespace(id), Some(&global));
    }
    assert_eq!(c.namespace(external), Some(&Namespace::from("other")));
}
