use super::*;

#[test]
fn constant_duplicates_use_namespace_sort_and_name_without_reordering_ids() {
    let mut c = Corpus::new();
    // Same sort spelling is not the same sort identity.
    let sorts = [
        c.declare_sort_in(Namespace::new(["left"]).unwrap(), "S")
            .unwrap(),
        c.declare_sort_in(Namespace::new(["right"]).unwrap(), "S")
            .unwrap(),
    ];
    let namespaces = [
        Namespace::default(),
        Namespace::new(["owner", "inner"]).unwrap(),
        Namespace::new(["owner::inner"]).unwrap(),
    ];
    let mut declared = Vec::new();
    // Deliberately differ from name, namespace and sort order in the index.
    for name in ["z", "shared", "a"] {
        for namespace in namespaces.iter().rev() {
            for sort in sorts.iter().rev() {
                let next = c.next;
                let id = c.declare_constant_in(namespace, name, *sort).unwrap();
                assert_eq!(id.0.index, next);
                assert!(c.contains_occurrence(id.into()));
                assert_eq!(c.constant(id).unwrap().sort, *sort);
                assert_eq!(c.constant(id).unwrap().name, name);
                assert_eq!(c.namespace(id), Some(namespace));
                declared.push(id);

                assert_eq!(
                    c.declare_constant_in(namespace, name, *sort),
                    Err(ConstructionError::DuplicateName {
                        kind: "constant in sort",
                        name: name.into(),
                    })
                );
                assert_eq!(c.next, next + 1, "duplicate must not consume an ID");
            }
        }
    }
    assert_eq!(c.constants().map(|v| v.id).collect::<Vec<_>>(), declared);
}

#[test]
fn invalid_constant_declarations_preserve_error_precedence_and_allocation() {
    let mut c = Corpus::new();
    let sort = c.declare_sort("S").unwrap();
    let foreign = Corpus::new().declare_sort("S").unwrap();
    let before = c.next;
    assert_eq!(
        c.declare_constant("", foreign),
        Err(ConstructionError::UnknownSort(foreign))
    );
    assert_eq!(
        c.declare_constant("valid", foreign),
        Err(ConstructionError::UnknownSort(foreign))
    );
    assert_eq!(
        c.declare_constant("", sort),
        Err(ConstructionError::EmptyName("constant"))
    );
    assert!(c.constants().next().is_none());
    assert_eq!(c.next, before);
    let id = c.declare_constant("valid", sort).unwrap();
    assert_eq!(id.0.index, before);
    assert_eq!(c.constants().map(|v| v.id).collect::<Vec<_>>(), [id]);
}
