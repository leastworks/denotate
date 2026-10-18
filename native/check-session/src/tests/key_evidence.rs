//! 6a.1 acceptance and diagnostic probes. Uses the unchanged 6.0 corpus.
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
fn reordered_declarations_change_proposed_witness_but_keep_current_execution() {
    // Three competing inputs make the choice observable; two inputs force the
    // same conflict even when variable order differs.
    let (_, _, p) = lower("input z, a, m; slot s; s <- z; s <- a; s <- m;");
    let g = prepare(&p, &Limits::default()).unwrap();
    let current = budget_result_lowered(&p, 20_000_000);
    let proposed = denotate_check::test_support::with_test_input_order(input_order(&p, &g), || {
        budget_result_lowered(&p, 20_000_000)
    });
    assert_ne!(current, proposed);
    assert_eq!(
        current,
        budget_result_lowered(&p, 20_000_000),
        "test override must restore current order"
    );
    for result in [&current, &proposed] {
        assert_eq!(result["groups"][0]["status"], "counterexample");
    }
}

fn witness_row(name: String, source: &str, max_work: usize) -> Value {
    let (ast, sources) = parse(source);
    let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
        return json!({"fixture":name,"source":source,"max_work":max_work,"invalid_source":true});
    };
    let g = prepare(&p, &Limits::default()).unwrap();
    let order = input_order(&p, &g);
    let current_order: Vec<_> = g.input_atoms().cloned().collect();
    let current_atoms: Vec<_> = g
        .atoms()
        .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
        .collect();
    let mut sorted = current_atoms.clone();
    sorted.sort();
    let current = budget_result_lowered(&p, max_work);
    let proposed = denotate_check::test_support::with_test_input_order(order.clone(), || {
        budget_result_lowered(&p, max_work)
    });
    let witness = |result: &Value| {
        result["groups"]
            .as_array()
            .map(|groups| {
                groups
                    .iter()
                    .filter(|g| g["status"] == "counterexample")
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    };
    json!({"fixture":name,"source":source,"max_work":max_work,
        "atom_order_differs":current_atoms!=sorted,"input_order_differs":current_order!=order,
        "current_input_order":current_order.iter().map(|a| Names::atom_key(&AtomKey::from_atom(&p.keys,a).unwrap())).collect::<Vec<_>>(),
        "proposed_input_order":order.iter().map(|a| Names::atom_key(&AtomKey::from_atom(&p.keys,a).unwrap())).collect::<Vec<_>>(),
        "result_differs":current!=proposed,"witness_differs":witness(&current)!=witness(&proposed),"current":current,"proposed":proposed})
}

#[test]
#[ignore = "manual release 6a.1 witness delta and key phase evidence"]
fn measure_key_boundary() {
    assert!(!cfg!(debug_assertions));
    let baseline: Value = serde_json::from_str(include_str!(
        "../../../check/fixtures/SLICE-6.0-BASELINE.json"
    ))
    .unwrap();
    let mut witnesses = Vec::new();
    for edit in baseline["edits"].as_array().unwrap() {
        for side in ["before", "after"] {
            witnesses.push(witness_row(
                format!("{}/{}", edit["edit"].as_str().unwrap(), side),
                edit[format!("{side}_source")].as_str().unwrap(),
                20_000_000,
            ));
        }
    }
    for (i, observation) in baseline["budgets"].as_array().unwrap().iter().enumerate() {
        let row = witness_row(
            format!("budget/{i}"),
            observation["source"].as_str().unwrap(),
            observation["max_work"].as_u64().unwrap() as usize,
        );
        assert_eq!(row["current"], observation["result"]);
        witnesses.push(row);
    }
    let mut timing = Vec::new();
    for family in ["duplicates", "distinct_literals", "helper_chain"] {
        for size in [1, 4, 16, 64] {
            let text = workload(family, size);
            let mut samples = Vec::new();
            for iteration in 0..6 {
                let (_, _, p) = lower(&text);
                let g = prepare_keyed(&p).unwrap();
                if iteration > 0 {
                    samples.push(json!({"installation_keys_ns":p.key_computation.as_nanos(),"ground_keys_ns":g.keys.elapsed.as_nanos(),"key_total_ns":(p.key_computation+g.keys.elapsed).as_nanos(),"preparation_ns":(g.program.metrics().grounding+g.program.metrics().admissibility).as_nanos(),"occurrences":p.keys.bindings().entries().count(),"instances":g.keys.instances.len(),"components":g.keys.components.len()}));
                }
            }
            timing.push(json!({"family":family,"parameter":size,"samples":samples}));
        }
    }
    println!(
        "SLICE_6A1_EVIDENCE={}",
        json!({"witnesses":witnesses,"key_timings":timing})
    );
}
