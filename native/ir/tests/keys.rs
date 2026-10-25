use denotate_ir::*;

#[test]
fn current_bindings_reject_missing_ambiguous_and_foreign_occurrences_transactionally() {
    let mut corpus = Corpus::new();
    let a = corpus.declare_sort("a").unwrap();
    let b = corpus.declare_sort("b").unwrap();
    let key = OccurrenceKey::Sort(SortKey(QualifiedKey::new("test", "a")));
    let other = OccurrenceKey::Sort(SortKey(QualifiedKey::new("test", "b")));
    let mut bindings = CurrentBindings::default();
    assert!(matches!(bindings.key(a), Err(KeyError::MissingBinding(_))));
    assert!(matches!(
        bindings.resolve(&key),
        Err(KeyError::MissingKey(_))
    ));
    bindings.bind(&corpus, key.clone(), a).unwrap();
    assert!(matches!(
        bindings.bind(&corpus, key.clone(), b),
        Err(KeyError::DuplicateKey(_))
    ));
    assert!(matches!(
        bindings.bind(&corpus, other.clone(), a),
        Err(KeyError::DuplicateOccurrence(_))
    ));
    assert_eq!(bindings.resolve(&key).unwrap(), a.into());
    assert_eq!(bindings.entries().count(), 1);
    let mut foreign = Corpus::new();
    let id = foreign.declare_sort("b").unwrap();
    assert!(matches!(
        bindings.bind(&corpus, other, id),
        Err(KeyError::UnknownOccurrence(_))
    ));
    let mut keys = SemanticKeys::default();
    keys.bind_sort(&corpus, a, SortKey(QualifiedKey::new("test", "a")))
        .unwrap();
    assert_eq!(
        keys.validate(&corpus),
        Err(KeyError::MissingBinding(b.into()))
    );
    assert!(matches!(
        keys.validate(&foreign),
        Err(KeyError::UnknownOccurrence(_))
    ));
}

fn library(negative: bool) -> (Corpus, SemanticKeys, RuleId) {
    let mut c = Corpus::new();
    let relation = c.declare_relation("r", RelationRole::Derived, []).unwrap();
    let head = c.atom(relation, []).unwrap();
    let body = c.atom(relation, []).unwrap();
    let atom_ids = [head.id(), body.id()];
    let r = c
        .add_rule(
            head,
            [if negative {
                Literal::Negative(body)
            } else {
                Literal::Positive(body)
            }],
        )
        .unwrap();
    let mut keys = SemanticKeys::default();
    keys.bind_relation(
        &c,
        relation,
        RelationKey::Named(QualifiedKey::new("library", "r")),
    )
    .unwrap();
    let key = RuleKey::Library(QualifiedKey::new("library", "definition"));
    keys.bind_rule(&c, r, key.clone()).unwrap();
    for (atom, id) in atom_ids.into_iter().enumerate() {
        keys.bind_occurrence(
            &c,
            id,
            OccurrenceKey::Library {
                rule: key.clone(),
                atom,
                argument: None,
            },
        )
        .unwrap();
    }
    keys.validate(&c).unwrap();
    (c, keys, r)
}
#[test]
fn library_rule_identity_survives_content_change_and_owned_keys_are_structural() {
    let (a, ak, ar) = library(false);
    let (b, bk, br) = library(true);
    assert_eq!(ak.rule(ar).unwrap(), bk.rule(br).unwrap());
    assert_ne!(
        ak.rule_schema(a.rule(ar).unwrap()).unwrap(),
        bk.rule_schema(b.rule(br).unwrap()).unwrap()
    );
    let make = || OwnerKey::new(String::from("frontend"), vec![0, 1, 255]);
    let a = make();
    let b = make();
    assert_eq!(a, b);
    assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
    assert_eq!(std::collections::HashSet::from([a, b]).len(), 1);
    assert_ne!(OwnerKey::new("other", vec![0, 1, 255]), make());
}

#[test]
fn assumptions_and_verifications_need_typed_keys() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let input = c
        .declare_relation("value", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    let a = c
        .assume_at_most_one_in(Namespace::default(), "one", input, [])
        .unwrap();
    let v = c
        .verification_in(Namespace::default(), "normal", [a], [])
        .unwrap();
    let mut keys = SemanticKeys::default();
    keys.bind_sort(&c, s, SortKey(QualifiedKey::new("", "S")))
        .unwrap();
    keys.bind_relation(
        &c,
        input,
        RelationKey::Named(QualifiedKey::new("", "value")),
    )
    .unwrap();
    assert_eq!(keys.validate(&c), Err(KeyError::MissingBinding(a.into())));
    let assumption = AssumptionKey(QualifiedKey::new("", "one"));
    keys.bind_assumption(&c, a, assumption.clone()).unwrap();
    assert_eq!(keys.validate(&c), Err(KeyError::MissingBinding(v.into())));
    let verification = VerificationKey(QualifiedKey::new("", "normal"));
    keys.bind_verification(&c, v, verification.clone()).unwrap();
    keys.validate(&c).unwrap();
    assert_eq!(keys.assumption(a), Ok(&assumption));
    assert_eq!(keys.verification(v), Ok(&verification));
    // Typed keys cannot be bound through the untyped occurrence path.
    let mut untyped = SemanticKeys::default();
    assert_eq!(
        untyped.bind_occurrence(&c, a.into(), OccurrenceKey::Assumption(assumption)),
        Err(KeyError::InvalidKind(a.into()))
    );
}
