use denotate_ir::*;

fn facts() -> (Corpus, [RuleId; 3]) {
    let mut c = Corpus::new();
    let r = c.declare_relation("p", RelationRole::Derived, []).unwrap();
    let mut fact = || {
        let atom = c.atom(r, []).unwrap();
        c.add_fact(atom).unwrap()
    };
    let ids = [fact(), fact(), fact()];
    (c, ids)
}

#[test]
fn source_ranges_are_checked_utf8_bytes_and_snapshot_specific() {
    let mut sources = Sources::new();
    let one = sources
        .add("file:///example.flow", 1, "dsl", "// 😀\r\nb")
        .unwrap();
    assert_eq!(
        sources
            .add("file:///example.flow", 1, "dsl", "// 😀\r\nb")
            .unwrap(),
        one
    );
    assert!(matches!(
        sources.add("file:///example.flow", 1, "dsl", "changed"),
        Err(ProvenanceError::SnapshotConflict { .. })
    ));
    assert!(matches!(
        sources.add("file:///example.flow", 1, "another-view", "// 😀\r\nb"),
        Err(ProvenanceError::SnapshotConflict { .. })
    ));
    let b = sources.span(one, 9..10).unwrap();
    assert_eq!(b.byte_range(), 9..10);
    assert_eq!(sources.text(b).unwrap(), "b");
    assert_eq!(
        sources.text(sources.span(one, 3..7).unwrap()).unwrap(),
        "😀"
    );
    let reversed_start = 5;
    for range in [4..7, 3..6, 10..11, reversed_start..2] {
        assert!(matches!(
            sources.span(one, range),
            Err(ProvenanceError::InvalidUtf8Range { .. })
        ));
    }
    assert_eq!(
        sources.text(sources.span(one, 10..10).unwrap()).unwrap(),
        ""
    );
    let two = sources
        .add("file:///example.flow", 2, "dsl", "// moved\n// 😀\r\nb")
        .unwrap();
    assert_ne!(one, two);
    assert_eq!(sources.text(b).unwrap(), "b");
    let another_store = Sources::new();
    assert!(matches!(
        another_store.text(b),
        Err(ProvenanceError::UnknownSnapshot(_))
    ));
}

#[test]
fn many_to_many_origins_survive_splits_merges_and_additional_source_views() {
    let (corpus, [one, two, merged]) = facts();
    let mut sources = Sources::new();
    let dsl = sources
        .add("file:///example.flow", 1, "dsl", "a b")
        .unwrap();
    let den = sources
        .add("file:///example.den", 1, "denotate", "p();")
        .unwrap();
    let a = Origin::new(sources.span(dsl, 0..1).unwrap());
    let b = Origin::new(sources.span(dsl, 2..3).unwrap());
    let generated = Origin::new(sources.span(den, 0..4).unwrap());
    let mut provenance = Provenance::new();
    provenance
        .attach(&corpus, &sources, one, [a.clone()])
        .unwrap();
    provenance
        .inherit(&corpus, &sources, two, &[one.into()])
        .unwrap();
    provenance
        .attach(&corpus, &sources, two, [b.clone()])
        .unwrap();
    provenance
        .inherit(&corpus, &sources, merged, &[one.into(), two.into()])
        .unwrap();
    provenance
        .attach(&corpus, &sources, merged, [generated.clone(), a.clone()])
        .unwrap();
    assert_eq!(
        provenance.origins(merged),
        &[a.clone(), b.clone(), generated.clone()]
    );
    assert_eq!(
        provenance.in_view(merged, &sources, "dsl").unwrap(),
        vec![&a, &b]
    );
    assert_eq!(
        provenance.in_view(merged, &sources, "denotate").unwrap(),
        vec![&generated]
    );
    assert_eq!(
        provenance.occurrences_at(a.span),
        vec![one.into(), two.into(), merged.into()]
    );
    assert_eq!(provenance.origins(one), &[a]);
    assert_eq!(corpus.rules().count(), 3);
}

#[test]
fn failed_attachments_are_atomic_and_do_not_accept_foreign_or_uncommitted_nodes() {
    let (corpus, [one, _, _]) = facts();
    let mut sources = Sources::new();
    let doc = sources.add("file:///one", 1, "dsl", "x").unwrap();
    let good = Origin::new(sources.span(doc, 0..1).unwrap());
    let mut other_sources = Sources::new();
    let other_doc = other_sources.add("file:///one", 1, "dsl", "x").unwrap();
    let bad = Origin::new(other_sources.span(other_doc, 0..1).unwrap());
    let mut provenance = Provenance::new();
    assert!(
        provenance
            .attach(&corpus, &sources, one, [good.clone(), bad])
            .is_err()
    );
    assert!(provenance.origins(one).is_empty());
    let (mut other, [foreign, _, _]) = facts();
    assert!(matches!(
        provenance.attach(&corpus, &sources, foreign, [good.clone()]),
        Err(ProvenanceError::UnknownOccurrence(_))
    ));
    let r = other
        .declare_relation("uncommitted", RelationRole::Derived, [])
        .unwrap();
    let atom = other.atom(r, []).unwrap();
    assert!(matches!(
        provenance.attach(&other, &sources, atom.id(), [good]),
        Err(ProvenanceError::UnknownOccurrence(_))
    ));
    assert!(matches!(
        provenance.inherit(&corpus, &sources, one, &[foreign.into()]),
        Err(ProvenanceError::UnknownOccurrence(_))
    ));
}

#[test]
fn hand_authored_denotate_needs_no_dsl_origin() {
    let (corpus, [one, _, _]) = facts();
    let mut sources = Sources::new();
    let doc = sources
        .add("file:///library.den", 1, "denotate", "p();")
        .unwrap();
    let origin = Origin::new(sources.span(doc, 0..4).unwrap());
    let mut provenance = Provenance::new();
    provenance
        .attach(&corpus, &sources, one, [origin.clone()])
        .unwrap();
    assert_eq!(
        provenance.in_view(one, &sources, "denotate").unwrap(),
        vec![&origin]
    );
    assert!(provenance.in_view(one, &sources, "dsl").unwrap().is_empty());
}
