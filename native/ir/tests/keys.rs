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
