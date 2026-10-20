//! Component graph semantics, receipt propagation and actual Salsa cutoff.
use super::*;
use crate::Session;
use denotate_test_dsl::{attribution::SourceView, presentation};

fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}
fn inputs(source: &str) -> Vec<LocalInput> {
    let (_, _, p) = lower(source);
    let l = limits();
    let prepared = request_evidence::checked(&p, &l);
    let LocalCheckOutcome::Complete(r) = prepared.verify_local(&(&l).into()).unwrap() else {
        panic!()
    };
    r.queries.into_values().map(|a| a.input).collect()
}
fn check(session: &mut Session, source: &str) -> Accounted<ScopedResults> {
    let (_, sources, p) = lower(source);
    let l = limits();
    let prepared = request_evidence::checked(&p, &l);
    let CheckOutcome::Complete(global) = prepared.verify(&(&l).into()).unwrap() else {
        panic!()
    };
    let LocalCheckOutcome::Complete(fresh) = prepared
        .verify_local_with(&(&l).into(), &mut NoComponentMemo)
        .unwrap()
    else {
        panic!()
    };
    let LocalCheckOutcome::Complete(cached) = session.verify(&prepared, &(&l).into()).unwrap()
    else {
        panic!()
    };
    assert_eq!(
        fresh.checked.results, cached.checked.results,
        "fresh/cached: {source}"
    );
    assert_eq!(
        global.results.value, fresh.checked.results.value,
        "global: {source}"
    );
    let render = |r: &Verification<'_>| {
        format!(
            "{:?}",
            presentation::present(&p, r, &sources, SourceView::TestDsl.as_str()).unwrap()
        )
    };
    assert_eq!(
        render(&global.verification),
        render(&cached.checked.verification),
        "diagnostics: {source}"
    );
    cached.checked.results.receipts.total().unwrap();
    assert!(
        session.stats().retained_bytes
            + session.component_stats().retained_bytes
            + session.plan_stats().retained_bytes
            <= 64 * 1024 * 1024
    );
    cached.checked.results
}
#[test]
fn components_frozen_and_edit_sources_match_global_and_fresh_graph() {
    let data: Value =
        serde_json::from_str(include_str!("../../fixtures/OWNED-6b.2a-REFERENCE.json")).unwrap();
    let sources: BTreeSet<_> = data["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["source"].as_str().unwrap())
        .collect();
    assert!(sources.len() >= 20);
    for source in sources {
        let mut session = Session::with_components();
        check(&mut session, source);
        check(&mut session, &format!("// shifted\n{source}"));
        assert_eq!(session.component_stats().evaluations, 0, "{source}");
        assert_eq!(
            session.stats().verdict_misses + session.stats().completion_misses,
            0
        );
    }
}
#[test]
fn components_share_providers_across_cones_and_count_receipts_once() {
    let mut session = Session::with_components();
    let r = check(
        &mut session,
        "input i,j; slot a,b; a <- i; a <- j; b <- i; b <- j;",
    );
    let count = r
        .receipts
        .entries()
        .filter(|(k, _)| matches!(k, QueryKey::ComponentEvaluation(_)))
        .count();
    assert!(
        session.component_stats().hits > 0,
        "{:?}, count {count}",
        session.component_stats()
    );
    assert_eq!(session.component_stats().evaluations, count);
    let roots = r
        .receipts
        .entries()
        .filter_map(|(k, _)| matches!(k, QueryKey::ConeEvaluation(_)).then_some(k.clone()))
        .collect::<Vec<_>>();
    let aggregate = r.receipts.aggregate(roots).unwrap();
    assert_eq!(
        aggregate
            .queries
            .iter()
            .filter(|k| matches!(k, QueryKey::ComponentEvaluation(_)))
            .count(),
        count
    );
}
#[test]
fn components_backdate_semantics_but_propagate_changed_provider_receipts() {
    let mut input =
        inputs("input i,j,k; slot a; a <- i when present(j) or present(k); a <- j;").remove(0);
    let mut session = Session::with_components();
    let ops = (&limits()).into();
    let first = session
        .execute(&input, &ops, &mut LocalMetrics::default())
        .unwrap();
    let graph = ComponentGraph::project(&input).unwrap();
    let provider = graph
        .inputs
        .values()
        .find(|c| {
            !c.local.rules.is_empty()
                && graph
                    .inputs
                    .values()
                    .any(|other| other.providers.contains(&c.key))
        })
        .unwrap();
    let rule_key = provider
        .local
        .rules
        .iter()
        .find(|(_, r)| !r.body.is_empty())
        .unwrap()
        .0
        .clone();
    let rule = input.rules.get_mut(&rule_key).unwrap();
    rule.body.push(rule.body[0].clone());
    let before = session.component_stats();
    let answers_before = session.stats().verdict_misses;
    let assemblies_before = session.stats().evaluation_misses;
    let next = session
        .execute(&input, &ops, &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(first.evaluation, next.evaluation);
    assert_eq!(first.answer, next.answer);
    assert_ne!(first.dependencies, next.dependencies);
    assert_eq!(
        session.component_stats().evaluations - before.evaluations,
        1,
        "only changed provider should execute"
    );
    assert_eq!(session.stats().verdict_misses, answers_before);
    assert_eq!(session.stats().evaluation_misses, assemblies_before);
    assert_eq!(
        next,
        NoComponentMemo
            .execute(&input, &ops, &mut LocalMetrics::default())
            .unwrap()
    );
}
#[test]
fn components_limits_scheduling_eviction_and_recovery_are_deterministic() {
    let queries = inputs("input i,j,k; slot a,b; a <- i; a <- j; b <- k when not available(b);");
    let mut session = Session::with_components();
    let ops = (&limits()).into();
    for work in [0, 1, 32, 128, 512, 2000, 20_000_000] {
        let mut expected = BTreeMap::new();
        for query in &queries {
            let mut q = query.clone();
            q.limits.max_work = work;
            expected.insert(
                q.scope.clone(),
                NoComponentMemo
                    .execute(&q, &ops, &mut LocalMetrics::default())
                    .unwrap(),
            );
        }
        for reverse in [false, true, false] {
            if reverse {
                session.evict_values();
            }
            let mut order = queries.clone();
            if reverse {
                order.reverse();
            }
            for mut q in order {
                q.limits.max_work = work;
                assert_eq!(
                    session
                        .execute(&q, &ops, &mut LocalMetrics::default())
                        .unwrap(),
                    expected[&q.scope]
                );
            }
        }
    }
    let cancelled = OperationalLimits::from(&limits());
    cancelled.cancellation.cancel();
    assert!(matches!(
        session.execute(&queries[0], &cancelled, &mut LocalMetrics::default()),
        Err(CheckError::Cancelled)
    ));
    assert_eq!(
        session
            .execute(&queries[0], &ops, &mut LocalMetrics::default())
            .unwrap(),
        NoComponentMemo
            .execute(&queries[0], &ops, &mut LocalMetrics::default())
            .unwrap()
    );
}
#[test]
fn components_projection_rejects_missing_premises_and_provider_edges() {
    let mut q = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let graph = ComponentGraph::project(&q).unwrap();
    let consumer = graph
        .inputs
        .values()
        .find(|c| !c.providers.is_empty())
        .unwrap();
    assert!(matches!(
        evaluate_owned_component(
            consumer,
            &BTreeMap::new(),
            &(&limits()).into(),
            &mut LocalMetrics::default()
        ),
        Err(CheckError::Internal("missing component provider"))
    ));
    let atom = q
        .rules
        .values()
        .find_map(|r| r.body.first())
        .unwrap()
        .1
        .atom
        .clone();
    q.facts.remove(&atom);
    assert!(ComponentGraph::project(&q).is_err());
}

fn singleton(n: usize) -> LocalInput {
    let atom = AtomKey {
        relation: RelationKey::Named(QualifiedKey::new("components-test", format!("i{n}"))),
        arguments: vec![],
    };
    let key = ComponentKey(vec![atom.clone()].into());
    LocalInput {
        completion_context: None,
        scope: LocalScope::Group(GroupKey {
            obligation: ObligationKey(QualifiedKey::new("components-test", format!("q{n}"))),
            tuple: vec![],
        }),
        roots: BTreeSet::from([atom.clone()]),
        obligation: None,
        facts: BTreeSet::from([atom.clone()]),
        possible: BTreeSet::from([atom.clone()]),
        inputs: BTreeSet::from([atom]),
        components: BTreeMap::from([(
            key,
            LocalComponent {
                recursive: false,
                blocked_by: BTreeSet::new(),
            },
        )]),
        rules: BTreeMap::new(),
        original_dependencies: BTreeMap::new(),
        rewrites: BTreeSet::new(),
        domains: BTreeMap::new(),
        constraints: vec![],
        input_groups: BTreeSet::new(),
        request_scope: RequestScope::WholeProgram,
        backend: BackendIdentity::bdd(),
        limits: (&limits()).into(),
        admission_limit: None,
    }
}
#[test]
fn components_recycle_slots_and_retain_stable_payload_under_churn() {
    let mut session = Session::with_components();
    let ops = (&limits()).into();
    let mut plateau = 0;
    for n in 0..1100 {
        let q = singleton(n);
        let expected = NoComponentMemo
            .execute(&q, &ops, &mut LocalMetrics::default())
            .unwrap();
        assert_eq!(
            session
                .execute(&q, &ops, &mut LocalMetrics::default())
                .unwrap(),
            expected
        );
        let stats = session.component_stats();
        assert!(stats.allocated_slots <= 512 && stats.retained_components <= 512);
        assert!(session.stats().retained_bytes + stats.retained_bytes <= 64 * 1024 * 1024);
        assert_eq!(session.stats().resets, 0);
        if n == 999 {
            plateau = stats.retained_bytes;
        }
    }
    assert!(session.component_stats().evicted > 0);
    assert!(session.component_stats().retained_bytes.abs_diff(plateau) < 64 * 1024);
    let before = session.component_stats().evaluations;
    session
        .execute(&singleton(1099), &ops, &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(session.component_stats().evaluations, before);
}
#[test]
fn components_byte_pressure_oversize_and_interruption_do_not_change_receipts() {
    let q = inputs("input i,j; slot a; a <- i; a <- j;").remove(0);
    let ops = (&limits()).into();
    let expected = NoComponentMemo
        .execute(&q, &ops, &mut LocalMetrics::default())
        .unwrap();
    for bytes in [0, 1024, 32 * 1024, 256 * 1024] {
        let mut session = Session::new_components(crate::Retention {
            max_entries: 4,
            max_bytes: bytes,
            max_condition_nodes: 32,
        });
        for _ in 0..3 {
            assert_eq!(
                session
                    .execute(&q, &ops, &mut LocalMetrics::default())
                    .unwrap(),
                expected
            );
            assert!(
                session.stats().retained_bytes + session.component_stats().retained_bytes <= bytes
            );
        }
    }
    let mut session = Session::with_components();
    session.interrupt_after_evaluation();
    assert!(matches!(
        session.execute(&q, &(&limits()).into(), &mut LocalMetrics::default()),
        Err(CheckError::Cancelled)
    ));
    assert_eq!(session.component_stats().retained_components, 0);
    let before = session.component_stats().evaluations;
    assert_eq!(
        session
            .execute(&q, &ops, &mut LocalMetrics::default())
            .unwrap(),
        expected
    );
    assert!(session.component_stats().evaluations > before);
}
#[test]
fn components_entry_oversize_uses_the_same_fresh_graph_contract() {
    let mut q = singleton(0);
    for n in 1..513 {
        let extra = singleton(n);
        q.facts.extend(extra.facts);
        q.possible.extend(extra.possible);
        q.inputs.extend(extra.inputs);
        q.components.extend(extra.components);
    }
    let ops = (&limits()).into();
    let mut session = Session::with_components();
    let expected = NoComponentMemo
        .execute(&q, &ops, &mut LocalMetrics::default())
        .unwrap();
    for _ in 0..2 {
        assert_eq!(
            session
                .execute(&q, &ops, &mut LocalMetrics::default())
                .unwrap(),
            expected
        );
    }
    assert_eq!(session.component_stats().bypassed_graphs, 2);
    assert_eq!(session.component_stats().allocated_slots, 0);
}
#[test]
fn components_edits_cycles_blocking_and_w_dependent_discharge_match_oracle() {
    let mut session = Session::with_components();
    for source in [
        "input i,j; slot a,b; a <- i when available(b); b <- j when available(a); a <- j;",
        "input i,j; slot a,b; a <- i when not available(b); b <- j when not available(a);",
        "input i,j; slot a; a <- i when not available(a); a <- j;",
        "input i,j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
    ] {
        check(&mut session, source);
        check(&mut session, &format!("{source} input unrelated;"));
        check(&mut session, source);
        check(&mut session, &source.replace("is 1", "is 3"));
    }
    for (_, before, after) in edit_cases() {
        // Name/syntax-error edits have no checker request; existing frontend
        // gates cover them, while this graph test covers every valid pair.
        let valid = |s: &str| {
            let (ast, sources) = parse(s);
            matches!(
                lowering::lower(&ast, &sources).unwrap(),
                LoweringOutcome::Lowered(_)
            )
        };
        if valid(&before) {
            check(&mut session, &before);
        }
        if valid(&after) {
            check(&mut session, &after);
        }
    }
}

#[test]
fn components_small_worlds_agree_with_concrete_evaluation() {
    for source in [
        "input i,j; slot a,b; a <- i; b <- j when available(a); b <- i;",
        "input i,j; slot a,b; a <- i when available(b); b <- j when available(a); a <- j;",
        "input i,j; slot a; a <- i when not available(a); a <- j;",
        "input i,j; slot a; a <- i when input_value(i) is 1; a <- j when not input_value(i) is 2;",
    ] {
        let (_, _, p) = lower(source);
        let l = limits();
        let ops = (&l).into();
        let prepared = request_evidence::checked(&p, &l);
        let program = prepared.program();
        let atoms = program.input_atoms().cloned().collect::<Vec<_>>();
        assert!(atoms.len() <= 10);
        let LocalCheckOutcome::Complete(r) = prepared
            .verify_local_with(&ops, &mut NoComponentMemo)
            .unwrap()
        else {
            panic!()
        };
        for bits in 0..(1 << atoms.len()) {
            let world = atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| bits & (1 << i) != 0)
                .map(|(_, a)| a.clone())
                .collect::<BTreeSet<_>>();
            // Independent implementation of this DSL's selected constraint:
            // at most one value per input (grouping column zero).
            let mut chosen = BTreeSet::new();
            if world
                .iter()
                .any(|a| !chosen.insert((a.relation, a.arguments[0])))
            {
                continue;
            }
            let concrete = program.evaluate(world.iter().cloned(), &l).unwrap();
            let keys = world
                .iter()
                .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
                .collect();
            for artifact in r.queries.values() {
                let evaluated = artifact.evaluation.as_ref().unwrap();
                for atom in program.atoms() {
                    let key = AtomKey::from_atom(&p.keys, atom).unwrap();
                    if !artifact.input.facts.contains(&key) {
                        continue;
                    }
                    if let FactState::Settled(expected) = concrete.fact(atom).unwrap() {
                        let actual = evaluated.conditions.get(&key).is_some_and(|c| {
                            denotate_check::test_support::owned_condition_value(c, &keys)
                        });
                        assert_eq!(actual, expected, "{source}, world {bits}, {key:?}");
                    }
                }
            }
        }
    }
}
#[test]
fn components_resource_limits_and_reverse_dependency_requests_keep_sound_answers() {
    let queries = inputs(
        "input i,j,k; slot a,b; a <- i when present(j) or present(k); a <- j; b <- k when not available(b);",
    );
    let ops = (&limits()).into();
    for query in queries {
        let ample = NoComponentMemo
            .execute(&query, &ops, &mut LocalMetrics::default())
            .unwrap();
        let mut variants = Vec::new();
        for cap in [0, 1, 2, 3, 8, 32] {
            for resource in 0..4 {
                let mut q = query.clone();
                match resource {
                    0 => q.limits.max_bdd_nodes = cap,
                    1 => q.limits.max_bdd_tasks = cap,
                    2 => q.limits.max_condition_nodes = cap,
                    _ => q.limits.max_bdd_variables = cap,
                }
                variants.push(q);
            }
        }
        let mut session = Session::with_components();
        session.reverse_components_for_test(true);
        for q in variants {
            let fresh = NoComponentMemo
                .execute(&q, &ops, &mut LocalMetrics::default())
                .unwrap();
            if fresh.answer.is_some() {
                assert_eq!(fresh.answer, ample.answer);
            }
            for _ in 0..2 {
                assert_eq!(
                    session
                        .execute(&q, &ops, &mut LocalMetrics::default())
                        .unwrap(),
                    fresh
                );
            }
        }
        let mut expired = OperationalLimits::from(&limits());
        expired.timeout = Duration::from_nanos(1);
        assert!(matches!(
            session.execute(&query, &expired, &mut LocalMetrics::default()),
            Err(CheckError::Deadline { .. })
        ));
        assert_eq!(session.component_stats().retained_components, 0);
        assert_eq!(
            session
                .execute(&query, &ops, &mut LocalMetrics::default())
                .unwrap(),
            ample
        );
    }
}
#[test]
fn components_wide_edit_reuses_fifteen_of_sixteen_scope_answers() {
    let (_, before, after) = edit_cases()
        .into_iter()
        .find(|(name, _, _)| name == "wide_local_guard")
        .unwrap();
    let mut session = Session::with_components();
    check(&mut session, &before);
    check(&mut session, &after);
    assert_eq!(session.stats().evaluation_hits, 15);
    assert_eq!(session.stats().evaluation_misses, 1);
    assert!(session.component_stats().hits > 0);
}

fn component_reference() -> Value {
    let old: Value =
        serde_json::from_str(include_str!("../../fixtures/OWNED-6b.2a-REFERENCE.json")).unwrap();
    let mut rows = Vec::new();
    for row in old["cases"].as_array().unwrap() {
        let source = row["source"].as_str().unwrap();
        let (_, _, p) = lower(source);
        let l = Limits {
            max_work: row["max_work"].as_u64().unwrap() as usize,
            ..limits()
        };
        let req = request_evidence::request(&p, &l);
        let exhausted = |reason: Inconclusive, receipts| {
            (
                json!({"status":"inconclusive","phase":reason.phase,"resource":reason.resource}),
                Accounted {
                    value: req.exhausted(reason),
                    receipts,
                },
            )
        };
        let mut session = Session::with_components();
        let mut runs = Vec::new();
        for cached in [false, true, true] {
            let preparation = if cached {
                session.prepare(&req, &p.corpus, &p.keys, &(&l).into())
            } else {
                req.prepare(&p.corpus, &p.keys, &(&l).into())
            }
            .unwrap();
            let result = match preparation {
                RequestPreparation::Inconclusive { reason, receipts } => {
                    exhausted(reason, receipts)
                }
                RequestPreparation::Complete(g) => {
                    let g = g.admit(&(&l).into()).unwrap();
                    let result = if cached {
                        session.verify(&g, &(&l).into())
                    } else {
                        g.verify_local_with(&(&l).into(), &mut NoComponentMemo)
                    }
                    .unwrap();
                    match result {
                        LocalCheckOutcome::Inconclusive { reason, receipts } => {
                            exhausted(reason, receipts)
                        }
                        LocalCheckOutcome::Complete(r) => (
                            captured_report(&r.checked.verification, &Names { keys: &p.keys }),
                            r.checked.results,
                        ),
                    }
                }
            };
            runs.push(result);
        }
        assert_eq!(runs[0], runs[1]);
        assert_eq!(runs[1], runs[2]);
        let (capture, result) = runs.remove(0);
        rows.push(json!({"source":source,"max_work":l.max_work,"fixtures":row["fixtures"],"captured_result":capture,"neutral_result":format!("{:?}",result.value),"receipts":budget_evidence::receipt_capture(&result.receipts)}));
    }
    json!({"schema":1,"note":"Fresh 6b.2b component graph contract. Independent per-component allowances and canonical once-only aggregation. Not a historical receipt overlay.","cases":rows})
}
#[test]
#[ignore = "capture the initial component graph reference; never overwrite earlier references"]
fn capture_component_reference() {
    println!("COMPONENT_6B2B_REFERENCE={}", component_reference());
}

#[test]
#[ignore = "paired release experiment; run alone, one warm-up/five samples"]
fn measure_component_query_paths() {
    assert!(!cfg!(debug_assertions));
    fn run(session: &mut Session, source: &str) -> (Value, Accounted<ScopedResults>) {
        let start = Instant::now();
        let (_, _, p) = lower(source);
        let lowering = start.elapsed();
        let l = limits();
        let req = request_evidence::request(&p, &l);
        let start = Instant::now();
        let RequestPreparation::Complete(g) = session
            .prepare(&req, &p.corpus, &p.keys, &(&l).into())
            .unwrap()
        else {
            panic!()
        };
        let preparation = start.elapsed();
        let start = Instant::now();
        let g = g.admit(&(&l).into()).unwrap();
        let admission = start.elapsed();
        let start = Instant::now();
        let LocalCheckOutcome::Complete(r) = session.verify(&g, &(&l).into()).unwrap() else {
            panic!()
        };
        let checking = start.elapsed();
        let start = Instant::now();
        let CheckOutcome::Complete(global) = g.verify(&(&l).into()).unwrap() else {
            panic!()
        };
        let global_ns = start.elapsed().as_nanos();
        assert_eq!(r.checked.results.value, global.results.value);
        let c = session.component_stats();
        let s = session.stats();
        let m = r.metrics;
        let row = json!({"lowering_ns":lowering.as_nanos(),"preparation_ns":preparation.as_nanos(),"admission_ns":admission.as_nanos(),"checking_ns":checking.as_nanos(),"global_checking_ns":global_ns,
            "local_projection_ns":m.keys.as_nanos(),"component_projection_ns":c.projection_ns,"component_install_ns":c.input_install_ns,"component_equality_ns":c.input_equality_ns,"component_query_ns":c.query_ns,"component_assembly_ns":c.assembly_ns,"component_receipts_ns":c.receipts_ns,"component_retention_ns":c.retention_ns,
            "evaluation_ns":m.evaluation.as_nanos(),"export_ns":m.export.as_nanos(),"component_executions":c.evaluations,"provider_projections":c.provider_projections,"component_hits":c.hits,"scope_hits":s.evaluation_hits,"scope_misses":s.evaluation_misses,"answer_misses":s.verdict_misses+s.completion_misses,
            "component_evicted":c.evicted,"component_bypassed_graphs":c.bypassed_graphs,"component_bytes":c.retained_bytes,"scope_bytes":s.retained_bytes,"plan_bytes":session.plan_stats().retained_bytes,"logical_work":r.checked.results.receipts.total().unwrap().work});
        (row, r.checked.results)
    }
    let old: Value = serde_json::from_str(include_str!("../../LOCAL-6b.1a.json")).unwrap();
    let mut rows = Vec::new();
    for row in old["measurement"]["rows"].as_array().unwrap() {
        let source = row["source"].as_str().unwrap();
        let edited = if row["family"] == "wide_overlap" {
            edit_cases()
                .into_iter()
                .find(|(n, _, _)| n == "wide_local_guard")
                .unwrap()
                .2
        } else {
            format!("{source}\ninput new6b; slot new6b_slot; new6b_slot <- new6b;")
        };
        let mut samples = Vec::new();
        for iteration in 0..6 {
            let mut modes = serde_json::Map::new();
            // Alternate paired order to reduce systematic ordering bias.
            for components in if iteration % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            } {
                let mut session = if components {
                    Session::with_components()
                } else {
                    Session::default()
                };
                let (cold, a) = run(&mut session, source);
                let (warm, b) = run(&mut session, &format!("// moved\n{source}"));
                assert_eq!(a, b);
                let (edit, _) = run(&mut session, &edited);
                modes.insert(
                    if components { "components" } else { "coarse" }.into(),
                    json!({"cold":cold,"warm":warm,"edit":edit}),
                );
            }
            if iteration > 0 {
                samples.push(Value::Object(modes));
            }
        }
        rows.push(json!({"family":row["family"],"size":row["size"],"source":source,"edited_source":edited,"samples":samples}));
    }
    assert_eq!(rows.len(), 26);
    println!(
        "COMPONENT_6B2B_MEASUREMENTS={}",
        json!({"warmups":1,"samples_per_point":5,"rows":rows})
    );
}

#[test]
fn components_reference_is_frozen_and_cold_warm_exact() {
    let expected: Value = serde_json::from_str(include_str!(
        "../../fixtures/COMPONENTS-6b.2b-REFERENCE.json"
    ))
    .unwrap();
    assert_eq!(component_reference(), expected);
}
#[test]
fn components_reject_provider_meaning_from_a_stronger_constraint_context() {
    let q = inputs("input i,j; slot a; a <- i when input_value(i) is 1; a <- j when present(i);")
        .remove(0);
    let graph = ComponentGraph::project(&q).unwrap();
    let ops = (&limits()).into();
    let mut values: BTreeMap<ComponentKey, std::sync::Arc<ProviderValue>> = BTreeMap::new();
    let mut exercised = false;
    for key in &graph.order {
        let input = &graph.inputs[key];
        let providers = input
            .providers
            .iter()
            .map(|k| (k.clone(), values[k].clone()))
            .collect::<BTreeMap<_, _>>();
        let value = evaluate_owned_component(input, &providers, &ops, &mut LocalMetrics::default())
            .unwrap();
        if input.providers.iter().any(|k| {
            graph.inputs[k]
                .local
                .input_groups
                .iter()
                .any(|g| g.len() > 1)
        }) {
            let mut weakened = input.as_ref().clone();
            weakened.local.input_groups.clear();
            assert!(matches!(
                evaluate_owned_component(&weakened, &providers, &ops, &mut LocalMetrics::default()),
                Err(CheckError::Internal(
                    "provider constraint context does not cover consumer"
                ))
            ));
            exercised = true;
        }
        values.insert(
            key.clone(),
            std::sync::Arc::new((value.value, value.failure)),
        );
    }
    assert!(exercised);
}

#[test]
fn components_plans_and_scopes_share_one_document_byte_ceiling() {
    let source = format!(
        "{} s0 <- i1; s1 <- i2; s2 <- i3; s3 <- i0;",
        workload("distinct_literals", 8)
    );
    let (_, _, p) = lower(&source);
    let l = limits();
    let ops = (&l).into();
    let request = request_evidence::request(&p, &l);
    let bytes = 2 * 1024 * 1024;
    let mut session = Session::new_components(crate::Retention {
        max_entries: 32,
        max_bytes: bytes,
        max_condition_nodes: 1_000_000,
    });
    for _ in 0..3 {
        let RequestPreparation::Complete(g) =
            session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let g = g.admit(&ops).unwrap();
        let LocalCheckOutcome::Complete(fresh) =
            g.verify_local_with(&ops, &mut NoComponentMemo).unwrap()
        else {
            panic!()
        };
        let LocalCheckOutcome::Complete(cached) = session.verify(&g, &ops).unwrap() else {
            panic!()
        };
        assert_eq!(cached.checked.results, fresh.checked.results);
        assert!(session.plan_stats().retained_bytes > 0);
        assert!(session.component_stats().allocated_slots > 0);
        assert!(
            session.stats().retained_bytes
                + session.component_stats().retained_bytes
                + session.plan_stats().retained_bytes
                <= bytes
        );
    }
}

#[test]
fn components_preserve_all_frontend_frozen_cases() {
    for (text, count) in [
        (include_str!("../../../test-dsl/fixtures/pre-mask.json"), 22),
        (
            include_str!("../../../test-dsl/fixtures/pre-normalize.json"),
            38,
        ),
        (
            include_str!("../../../test-dsl/fixtures/pre-integration-fingerprints.json"),
            84,
        ),
    ] {
        let data: Value = serde_json::from_str(text).unwrap();
        let cases = data["cases"].as_array().unwrap();
        assert_eq!(cases.len(), count);
        for row in cases {
            let source = row["text"].as_str().unwrap();
            let document = std::sync::Arc::new(Document::new(
                &mut syntax::parser().unwrap(),
                source.into(),
                1,
                true,
            ));
            let frontend = denotate_test_dsl::analysis::prepare(
                &"file:///components-frozen.inputmapping".parse().unwrap(),
                1,
                document,
                &mut lowering::incremental::Session::default(),
            )
            .unwrap();
            if frontend.program.is_some() {
                check(&mut Session::with_components(), source);
            }
        }
    }
}
