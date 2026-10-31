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

#[test]
fn qualified_declarations_preserve_display_names_and_reject_same_namespace_duplicates() {
    let mut c = Corpus::new();
    let a = c
        .declare_sort_in(Namespace::new(["a"]).unwrap(), "S")
        .unwrap();
    let b = c
        .declare_sort_in(Namespace::new(["b"]).unwrap(), "S")
        .unwrap();
    assert_ne!(a, b);
    assert_eq!(c.sort(a).unwrap().name, c.sort(b).unwrap().name);
    assert!(
        c.declare_sort_in(Namespace::new(["a"]).unwrap(), "S")
            .is_err()
    );
    let plain = c.declare_sort("S").unwrap();
    assert_eq!(c.namespace(plain), Some(&Namespace::default()));
    assert!(c.declare_sort("S").is_err());
    let ca = c
        .declare_constant_in(Namespace::new(["a"]).unwrap(), "same", a)
        .unwrap();
    let cb = c
        .declare_constant_in(Namespace::new(["b"]).unwrap(), "same", a)
        .unwrap();
    assert_ne!(ca, cb);
    assert!(
        c.declare_constant_in(Namespace::new(["a"]).unwrap(), "same", a)
            .is_err()
    );
    let ra = c
        .declare_relation_in(Namespace::new(["a"]).unwrap(), "r", RelationRole::Input, [])
        .unwrap();
    let rb = c
        .declare_relation_in(Namespace::new(["b"]).unwrap(), "r", RelationRole::Input, [])
        .unwrap();
    assert_ne!(ra, rb);
    assert!(
        c.declare_relation_in(Namespace::new(["a"]).unwrap(), "r", RelationRole::Input, [])
            .is_err()
    );
    c.at_most_one_in(Namespace::new(["a"]).unwrap(), "unique", ra, [], "")
        .unwrap();
    c.at_most_one_in(Namespace::new(["b"]).unwrap(), "unique", rb, [], "")
        .unwrap();
    assert!(
        c.at_most_one_in(Namespace::new(["a"]).unwrap(), "unique", ra, [], "")
            .is_err()
    );
    let generated = c.declare_generated_relation_named("$condition_42").unwrap();
    let frontend = c
        .declare_relation("$condition_42", RelationRole::Derived, [])
        .unwrap();
    assert!(c.is_generated_relation(generated));
    assert!(!c.is_generated_relation(frontend));
    assert_eq!(c.relation(generated).unwrap().name, "$condition_42");
}

#[test]
fn assumptions_restrict_inputs_and_verifications_select_declarations() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let input = unary(&mut c, "value", s, RelationRole::Input);
    let derived = unary(&mut c, "present", s, RelationRole::Derived);
    let ns = Namespace::new(["demo"]).unwrap();
    let a = c
        .assume_at_most_one_in(ns.clone(), "one_value", input, [])
        .unwrap();
    c.assume_at_most_one_in(ns.clone(), "over_derived", derived, [])
        .unwrap();
    c.validate_assumptions().unwrap();
    assert!(matches!(
        c.assume_at_most_one_in(ns.clone(), "bad_column", input, ["missing".into()]),
        Err(ConstructionError::InvalidGroupColumn { .. })
    ));
    assert!(matches!(
        c.assume_at_most_one_in(ns.clone(), "one_value", input, []),
        Err(ConstructionError::DuplicateName {
            kind: "assumption",
            ..
        })
    ));
    c.assume_at_most_one_in(Namespace::default(), "one_value", input, [])
        .unwrap();
    let o = c
        .at_most_one_in(ns.clone(), "unique", derived, [], "")
        .unwrap();

    let v = c.verification_in(ns.clone(), "normal", [a], [o]).unwrap();
    let declared = c.verification(v).unwrap();
    assert_eq!(
        (
            declared.assumptions.as_slice(),
            declared.obligations.as_slice()
        ),
        (&[a][..], &[o][..])
    );
    // Empty selections are allowed: no restrictions, or a consistency-only context.
    c.verification_in(ns.clone(), "unrestricted", [], [o])
        .unwrap();
    c.verification_in(ns.clone(), "inputs_only", [a], [])
        .unwrap();
    assert!(matches!(
        c.verification_in(ns.clone(), "twice", [a, a], [o]),
        Err(ConstructionError::DuplicateReference { .. })
    ));
    assert!(matches!(
        c.verification_in(ns.clone(), "normal", [a], [o]),
        Err(ConstructionError::DuplicateName {
            kind: "verification",
            ..
        })
    ));
    let mut other = Corpus::new();
    let t = other.declare_sort("S").unwrap();
    let foreign_input = unary(&mut other, "value", t, RelationRole::Input);
    let foreign = other
        .assume_at_most_one_in(Namespace::default(), "one_value", foreign_input, [])
        .unwrap();
    assert_eq!(
        c.verification_in(ns, "foreign", [foreign], []),
        Err(ConstructionError::UnknownAssumption(foreign))
    );
    let top = top_level(&c);
    assert!(top.contains(&a.into()) && top.contains(&v.into()));
}

#[test]
fn coverage_uses_the_same_namespaces_and_grouping_validation_as_uniqueness() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let r = unary(&mut c, "r", s, RelationRole::Derived);
    let namespace = Namespace::new(["library"]).unwrap();
    let id = c
        .at_least_one_in(
            namespace.clone(),
            "covered",
            r,
            ["value".into()],
            "coverage",
        )
        .unwrap();
    assert_eq!(c.namespace(id), Some(&namespace));
    assert_eq!(
        c.obligation(id).unwrap().requirement,
        Requirement::AtLeastOne {
            relation: r,
            group_by: vec![0]
        }
    );
    assert!(matches!(
        c.at_most_one_in(namespace, "covered", r, [], ""),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(matches!(
        c.at_least_one("bad", r, ["missing".into()], ""),
        Err(ConstructionError::InvalidGroupColumn { .. })
    ));
    assert!(matches!(
        c.at_least_one("bad", r, ["value".into(), Column::Index(0)], ""),
        Err(ConstructionError::DuplicateGroupColumn { .. })
    ));
    assert!(c.at_least_one("global", r, [], "").is_ok());
}

#[test]
fn exactly_one_is_one_authored_declaration_with_shared_validation() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let r = unary(&mut c, "r", s, RelationRole::Derived);
    let ns = Namespace::new(["lib"]).unwrap();
    let id = c
        .exactly_one_in(ns.clone(), "one", r, ["value".into()], "one tuple")
        .unwrap();
    assert_eq!(c.namespace(id), Some(&ns));
    assert_eq!(
        c.obligation(id).unwrap().requirement,
        Requirement::ExactlyOne {
            relation: r,
            group_by: vec![0]
        }
    );
    assert_eq!(c.obligations().count(), 1);
    assert!(matches!(
        c.at_least_one_in(ns, "one", r, [], ""),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(matches!(
        c.exactly_one("bad", r, ["missing".into()], ""),
        Err(ConstructionError::InvalidGroupColumn { .. })
    ));
    assert!(matches!(
        c.exactly_one("bad", r, ["value".into(), Column::Index(0)], ""),
        Err(ConstructionError::DuplicateGroupColumn { .. })
    ));
    assert!(c.exactly_one("global", r, [], "").is_ok());
}

#[test]
fn empty_is_ungrouped_with_shared_declaration_validation() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let r = unary(&mut c, "r", s, RelationRole::Derived);
    let ns = Namespace::new(["lib"]).unwrap();
    let id = c.empty_in(ns.clone(), "none", r, "no tuples").unwrap();
    assert_eq!(c.namespace(id), Some(&ns));
    assert_eq!(
        c.obligation(id).unwrap().requirement,
        Requirement::Empty { relation: r }
    );
    assert!(!Cardinality::Empty.has_coverage() && !Cardinality::Empty.has_uniqueness());
    assert!(matches!(
        c.at_most_one_in(ns, "none", r, [], ""),
        Err(ConstructionError::DuplicateName { .. })
    ));
    assert!(c.empty("", r, "").is_err());
    let mut foreign = Corpus::new();
    let unknown = foreign
        .declare_relation("r", RelationRole::Derived, [])
        .unwrap();
    assert!(c.empty("foreign", unknown, "").is_err());
}

#[test]
fn condition_notices_validate_arity_ownership_selection_and_semantic_bindings() {
    let mut c = Corpus::new();
    let ns = Namespace::new(["lib"]).unwrap();
    let r = c.declare_relation("r", RelationRole::Derived, []).unwrap();
    let n = c
        .notice_varies_in(ns.clone(), "n", r, Some(r), "use")
        .unwrap();
    assert_eq!(c.namespace(n), Some(&ns));
    assert!(top_level(&c).contains(&n.into()));
    assert!(c.notice_varies_in(ns.clone(), "n", r, None, "").is_err());
    let s = c.declare_sort("S").unwrap();
    let unary = unary(&mut c, "unary", s, RelationRole::Derived);
    assert!(matches!(
        c.notice_varies_in(ns.clone(), "bad", unary, None, ""),
        Err(ConstructionError::InvalidNoticeRelation(_))
    ));
    assert!(matches!(
        c.notice_varies_in(ns.clone(), "bad", r, Some(unary), ""),
        Err(ConstructionError::InvalidNoticeRelation(_))
    ));
    assert!(
        c.verification_with_notices_in(ns.clone(), "bad", [], [], [n, n])
            .is_err()
    );
    let v = c
        .verification_with_notices_in(ns.clone(), "v", [], [], [n])
        .unwrap();
    assert_eq!(c.verification(v).unwrap().notices, [n]);
    let mut foreign = Corpus::new();
    let other = foreign
        .declare_relation("r", RelationRole::Derived, [])
        .unwrap();
    assert!(
        c.notice_varies_in(ns.clone(), "bad", other, None, "")
            .is_err()
    );
    let other = foreign
        .notice_varies_in(ns.clone(), "n", other, None, "")
        .unwrap();
    assert!(matches!(
        c.verification_with_notices_in(ns, "foreign", [], [], [other]),
        Err(ConstructionError::UnknownNotice(_))
    ));
    let mut keys = SemanticKeys::default();
    keys.bind_sort(&c, s, SortKey(QualifiedKey::new("", "S")))
        .unwrap();
    for (id, name) in [(r, "r"), (unary, "unary")] {
        keys.bind_relation(&c, id, RelationKey::Named(QualifiedKey::new("", name)))
            .unwrap();
    }
    keys.bind_verification(&c, v, VerificationKey(QualifiedKey::new("lib", "v")))
        .unwrap();
    assert_eq!(keys.validate(&c), Err(KeyError::MissingBinding(n.into())));
    keys.bind_notice(&c, n, NoticeKey(QualifiedKey::new("lib", "n")))
        .unwrap();
    keys.validate(&c).unwrap();
}
