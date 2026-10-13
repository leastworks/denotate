use denotate_ir::*;

fn unary(c: &mut Corpus, name: &str, sort: SortId, role: RelationRole) -> RelationId {
    c.declare_relation(name, role, [Parameter::new("value", sort)])
        .unwrap()
}

#[test]
fn same_name_in_different_sorts_has_distinct_identity() {
    let mut c = Corpus::new();
    let a = c.declare_sort("A").unwrap();
    let b = c.declare_sort("B").unwrap();
    let ca = c.declare_constant("same", a).unwrap();
    let cb = c.declare_constant("same", b).unwrap();
    assert_ne!(ca, cb);
    let r = unary(&mut c, "r", a, RelationRole::Derived);
    let atom = c.atom(r, [ca.into()]).unwrap();
    c.add_fact(atom).unwrap();
    assert!(matches!(
        c.atom(r, [cb.into()]),
        Err(ConstructionError::SortMismatch { argument: 0, .. })
    ));
    assert_eq!(c.rules().count(), 1);
}

#[test]
fn constructors_check_arity_and_variable_sorts() {
    let mut c = Corpus::new();
    let a = c.declare_sort("A").unwrap();
    let b = c.declare_sort("B").unwrap();
    let r = unary(&mut c, "r", a, RelationRole::Derived);
    assert!(matches!(
        c.atom(r, []),
        Err(ConstructionError::Arity {
            expected: 1,
            actual: 0,
            ..
        })
    ));
    assert!(matches!(
        c.atom(r, [Term::variable("X", a), Term::variable("Y", a)]),
        Err(ConstructionError::Arity {
            expected: 1,
            actual: 2,
            ..
        })
    ));
    assert!(matches!(
        c.atom(r, [Term::variable("X", b)]),
        Err(ConstructionError::SortMismatch { .. })
    ));
}

#[test]
fn variable_sort_consistency_is_rule_local() {
    let mut c = Corpus::new();
    let a = c.declare_sort("A").unwrap();
    let b = c.declare_sort("B").unwrap();
    let r = unary(&mut c, "r", a, RelationRole::Derived);
    let s = unary(&mut c, "s", b, RelationRole::Derived);
    let head = c.atom(r, [Term::variable("X", a)]).unwrap();
    let body = c.atom(s, [Term::variable("X", b)]).unwrap();
    assert!(matches!(
        c.add_rule(head, [Literal::Positive(body)]),
        Err(ConstructionError::VariableSortConflict { .. })
    ));
    assert_eq!(c.rules().count(), 0);
    for (relation, sort) in [(r, a), (s, b)] {
        let head = c.atom(relation, [Term::variable("X", sort)]).unwrap();
        let body = c.atom(relation, [Term::variable("X", sort)]).unwrap();
        c.add_rule(head, [Literal::Positive(body)]).unwrap();
    }
    assert_eq!(c.rules().count(), 2);
}

#[test]
fn head_and_negative_variables_need_positive_bindings() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("S").unwrap();
    let r = unary(&mut c, "r", sort, RelationRole::Derived);
    let p = unary(&mut c, "p", sort, RelationRole::Input);
    let x = Term::variable("X", sort);
    let head = c.atom(r, [x.clone()]).unwrap();
    assert!(matches!(
        c.add_fact(head),
        Err(ConstructionError::UnsafeVariable { .. })
    ));
    let head = c.atom(r, [x.clone()]).unwrap();
    let negative = c.atom(p, [x.clone()]).unwrap();
    assert!(matches!(
        c.add_rule(head, [Literal::Negative(negative)]),
        Err(ConstructionError::UnsafeVariable { .. })
    ));

    // A negative body-only variable is not bound by a different positive one.
    let head = c.atom(r, [x.clone()]).unwrap();
    let positive = c.atom(p, [x.clone()]).unwrap();
    let negative = c.atom(p, [Term::variable("Y", sort)]).unwrap();
    assert!(
        matches!(c.add_rule(head, [Literal::Positive(positive), Literal::Negative(negative)]),
        Err(ConstructionError::UnsafeVariable { name, .. }) if name == "Y")
    );

    // Body order is not execution order: the positive binder may occur last.
    let head = c.atom(r, [x.clone()]).unwrap();
    let negative = c.atom(p, [x.clone()]).unwrap();
    let positive = c.atom(p, [x]).unwrap();
    c.add_rule(
        head,
        [Literal::Negative(negative), Literal::Positive(positive)],
    )
    .unwrap();
}

#[test]
fn input_relations_cannot_have_facts_or_rule_definitions() {
    let mut c = Corpus::new();
    let p = c.declare_relation("p", RelationRole::Input, []).unwrap();
    let r = c.declare_relation("r", RelationRole::Derived, []).unwrap();
    let head = c.atom(p, []).unwrap();
    assert_eq!(c.add_fact(head), Err(ConstructionError::InputDefinition(p)));
    let head = c.atom(p, []).unwrap();
    let body = c.atom(r, []).unwrap();
    assert_eq!(
        c.add_rule(head, [Literal::Positive(body)]),
        Err(ConstructionError::InputDefinition(p))
    );
    let head = c.atom(r, []).unwrap();
    let fact = c.add_fact(head).unwrap();
    assert!(c.rule(fact).unwrap().is_fact());
}

#[test]
fn foreign_handles_are_rejected_instead_of_aliasing_equal_indices() {
    let mut c = Corpus::new();
    let mut other = Corpus::new();
    let a = c.declare_sort("A").unwrap();
    let foreign = other.declare_sort("A").unwrap();
    assert_eq!(
        c.declare_constant("x", foreign),
        Err(ConstructionError::UnknownSort(foreign))
    );
    assert!(matches!(
        c.declare_relation("bad", RelationRole::Derived, [Parameter::new("x", foreign)]),
        Err(ConstructionError::UnknownSort(_))
    ));
    let r = unary(&mut c, "r", a, RelationRole::Derived);
    let s = unary(&mut other, "r", foreign, RelationRole::Derived);
    let value = other.declare_constant("x", foreign).unwrap();
    assert!(matches!(
        c.atom(r, [value.into()]),
        Err(ConstructionError::UnknownConstant(_))
    ));
    assert!(matches!(
        c.atom(s, [value.into()]),
        Err(ConstructionError::UnknownRelation(_))
    ));
    let foreign_head = other.atom(s, [value.into()]).unwrap();
    assert!(matches!(
        c.add_fact(foreign_head),
        Err(ConstructionError::ForeignAtom(_))
    ));
    let local = c.declare_constant("x", a).unwrap();
    let head = c.atom(r, [local.into()]).unwrap();
    let body = other.atom(s, [value.into()]).unwrap();
    assert!(matches!(
        c.add_rule(head, [Literal::Positive(body)]),
        Err(ConstructionError::ForeignAtom(_))
    ));
    assert_eq!(c.rules().count(), 0);
}

#[test]
fn declarations_validate_names_without_imposing_a_source_language_lexicon() {
    let mut c = Corpus::new();
    assert!(matches!(
        c.declare_sort(""),
        Err(ConstructionError::EmptyName("sort"))
    ));
    let sort = c.declare_sort("S").unwrap();
    assert!(matches!(
        c.declare_sort("S"),
        Err(ConstructionError::DuplicateName { .. })
    ));
    c.declare_constant("same", sort).unwrap();
    assert!(matches!(
        c.declare_constant("same", sort),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(matches!(
        c.declare_relation(
            "r",
            RelationRole::Derived,
            [Parameter::new("x", sort), Parameter::new("x", sort)]
        ),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(matches!(
        c.declare_relation("r", RelationRole::Derived, [Parameter::new("", sort)]),
        Err(ConstructionError::EmptyName("parameter"))
    ));
    let r = unary(&mut c, "r", sort, RelationRole::Derived);
    assert!(matches!(
        c.declare_relation("r", RelationRole::Derived, []),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(matches!(
        c.atom(r, [Term::variable("", sort)]),
        Err(ConstructionError::EmptyName("variable"))
    ));
}

#[test]
fn cardinality_grouping_uses_roles_not_a_prefix_or_sort_name() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("S").unwrap();
    let r = c
        .declare_relation(
            "supplies",
            RelationRole::Derived,
            [
                Parameter::new("input", sort),
                Parameter::new("slot", sort),
                Parameter::new("region", sort),
            ],
        )
        .unwrap();
    let o = c
        .at_most_one(
            "unique",
            r,
            ["region".into(), "slot".into()],
            "Slot {slot}: {inputs}",
        )
        .unwrap();
    assert_eq!(
        c.obligation(o).unwrap().requirement,
        Requirement::AtMostOne {
            relation: r,
            group_by: vec![2, 1]
        }
    );
    assert_eq!(
        c.obligation(o).unwrap().message_template,
        "Slot {slot}: {inputs}"
    );
    assert!(matches!(
        c.at_most_one("bad", r, ["S".into()], ""),
        Err(ConstructionError::InvalidGroupColumn { .. })
    ));
    assert!(matches!(
        c.at_most_one("bad", r, [Column::Index(3)], ""),
        Err(ConstructionError::InvalidGroupColumn { .. })
    ));
    assert!(matches!(
        c.at_most_one("bad", r, ["slot".into(), Column::Index(1)], ""),
        Err(ConstructionError::DuplicateGroupColumn { index: 1, .. })
    ));
    assert!(matches!(
        c.at_most_one("unique", r, [], ""),
        Err(ConstructionError::DuplicateName { .. })
    ));
    c.at_most_one("global", r, [], "").unwrap();
    let boolean = c
        .declare_relation("boolean", RelationRole::Derived, [])
        .unwrap();
    c.at_most_one("boolean_bound", boolean, [], "").unwrap();
}

#[test]
fn equal_fact_values_keep_distinct_occurrences_for_attribution() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("S").unwrap();
    let x = c.declare_constant("x", sort).unwrap();
    let r = unary(&mut c, "r", sort, RelationRole::Derived);
    let first = c.atom(r, [x.into()]).unwrap();
    let second = c.atom(r, [x.into()]).unwrap();
    assert_eq!(first.arguments()[0].value(), second.arguments()[0].value());
    assert_ne!(first.arguments()[0].id(), second.arguments()[0].id());
    assert_ne!(first.id(), second.id());
    let one = c.add_fact(first).unwrap();
    let two = c.add_fact(second).unwrap();
    assert_ne!(one, two);
    // Two authored facts, not an assertion of two semantic tuples. Evaluation
    // will use set semantics; the construction layer must not lose either origin.
    assert_eq!(c.rules().count(), 2);
}
