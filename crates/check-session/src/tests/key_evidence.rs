//! Semantic keys, snapshot rebinding, and canonical input-order behavior.
use super::*;

// The checker unit-test crate is distinct from the dependency linked through
// test-dsl; use the same generic production stages with local checker types.
fn prepare_keyed(p: &LoweredProgram) -> std::result::Result<KeyedPreparation, CheckError> {
    let program = prepare(p, &Limits::default())?;
    let keys = GroundKeyIndex::build(&p.corpus, &p.keys, &program).map_err(CheckError::Keys)?;
    Ok(KeyedPreparation { program, keys })
}

fn input_order(p: &LoweredProgram, g: &GroundProgram) -> Vec<GroundAtom> {
    let mut order: Vec<_> = g.input_atoms().cloned().collect();
    order.sort_by_cached_key(|a| AtomKey::from_atom(&p.keys, a).unwrap());
    order
}

#[test]
fn keys_rebind_all_current_occurrences_and_preserve_duplicate_sources() {
    let text = "input i, j; slot a; a <- i when (present(i) or present(j)) and present(i); a <- i when (present(i) or present(j)) and present(i);";
    let (_, sources, p) = lower(text);
    let (_, newer, q) = lower(&format!("// new source\n{text}"));
    p.keys.validate(&p.corpus).unwrap();
    q.keys.validate(&q.corpus).unwrap();
    assert!(p.keys.validate(&q.corpus).is_err());
    let old: BTreeSet<_> = p.keys.bindings().entries().map(|(k, _)| k).collect();
    let new: BTreeSet<_> = q.keys.bindings().entries().map(|(k, _)| k).collect();
    assert_eq!(old, new);
    let mut attributed = 0;
    let mut generated = 0;
    let mut library = 0;
    let mut duplicate_owners = BTreeSet::new();
    for (key, id) in p.keys.bindings().entries() {
        let current = q.keys.bindings().resolve(key).unwrap();
        assert_ne!(id, current);
        let a = p.attribution.provenance.origins(id);
        let b = q.attribution.provenance.origins(current);
        assert_eq!(a.len(), b.len());
        for (a, b) in a.iter().zip(b) {
            assert_ne!(a.span.snapshot(), b.span.snapshot());
            assert_eq!(sources.text(a.span).unwrap(), newer.text(b.span).unwrap());
            assert_eq!(a.span.byte_range().start + 14, b.span.byte_range().start);
            attributed += 1;
        }
        match key {
            OccurrenceKey::Relation(RelationKey::Generated { owner, .. }) => {
                generated += 1;
                duplicate_owners.insert(owner.clone());
            }
            OccurrenceKey::Library { .. } => library += 1,
            _ => {}
        }
    }
    assert!(attributed > 10 && generated >= 2 && library > 10);
    assert_eq!(duplicate_owners.len(), 2);
}

#[test]
fn ground_keys_keep_body_only_variables_empty_groups_and_negative_absence() {
    let (_, _, p) = lower("input i; slot empty, a; a <- i when not available(empty);");
    let prepared = prepare_keyed(&p).unwrap();
    let g = &prepared.program;
    let index = &prepared.keys;
    assert_eq!(index.instances.len(), g.rules().count());
    assert!(
        index.atoms.len() > g.atoms().count(),
        "impossible negative premises retained"
    );
    let (obligation, groups) = index.groups.first_key_value().unwrap();
    let empty = groups.domains[0]
        .iter()
        .find(|k| k.name.as_ref() == "empty")
        .unwrap()
        .clone();
    let key = groups.key(obligation, vec![empty]).unwrap();
    assert!(!groups.members.contains_key(&key.tuple));
    assert!(groups.key(obligation, vec![]).is_err());
    let present = index
        .content
        .iter()
        .find(|(key, _)| matches!(&key.rule, RuleKey::Library(k) if k.name.as_ref()=="present"))
        .unwrap();
    assert_eq!(
        present.0.substitution.len(),
        2,
        "V is body-only in present(I) <- value(I,V)"
    );
    assert!(
        present
            .0
            .substitution
            .iter()
            .any(|(v, _)| v.name.as_ref() == "V")
    );
    let (_, _, q) = lower("input i; slot empty, a; a <- i when not available(empty);");
    assert!(GroundKeyIndex::build(&q.corpus, &q.keys, g).is_err());
}

#[test]
fn input_order_override_preserves_outcomes_and_restores_execution() {
    // Three competing inputs make the choice observable; two inputs force the
    // same conflict even when variable order differs.
    let (_, _, p) = lower("input z, a, m; slot s; s <- z; s <- a; s <- m;");
    let g = prepare(&p, &Limits::default()).unwrap();
    let current = budget_result_lowered(&p, 20_000_000);
    let proposed = denotate_check::test_support::with_test_input_order(input_order(&p, &g), || {
        budget_result_lowered(&p, 20_000_000)
    });
    assert_eq!(
        semantic_outcomes(current.clone()),
        semantic_outcomes(proposed.clone())
    );
    assert_eq!(
        current,
        budget_result_lowered(&p, 20_000_000),
        "test override must restore current order"
    );
    for result in [&current, &proposed] {
        assert_eq!(result["groups"][0]["status"], "counterexample");
    }
}
