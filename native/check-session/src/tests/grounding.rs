//! Fresh relation-SCC grounding contract, then cache equivalence and edits.
use super::*;
fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}
#[test]
fn grounding_fresh_matches_global_preparation_and_diagnostics() {
    use denotate_test_dsl::{attribution::SourceView, presentation};
    let mut sources = regression_cases()
        .into_iter()
        .map(|r| r["source"].as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    for (_, a, b) in edit_cases() {
        sources.insert(a);
        sources.insert(b);
    }
    for source in sources {
        let (ast, sources) = parse(&source);
        let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
            continue;
        };
        let l = limits();
        let ops = (&l).into();
        let request = request_evidence::request(&p, &l);
        let RequestPreparation::Complete(old) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("old {source}")
        };
        let RequestPreparation::Complete(fresh) = request
            .prepare_with_grounding(
                &p.corpus,
                &p.keys,
                &ops,
                &mut FreshPlans,
                &mut FreshGrounding,
            )
            .unwrap()
        else {
            panic!("new {source}")
        };
        assert_eq!(
            old.keys().content,
            fresh.keys().content,
            "instances {source}"
        );
        assert_eq!(
            old.program().atoms().collect::<Vec<_>>(),
            fresh.program().atoms().collect::<Vec<_>>(),
            "tuples {source}"
        );
        fresh.receipts().total().unwrap();
        let old = old.admit(&ops).unwrap();
        let fresh = fresh.admit(&ops).unwrap();
        let CheckOutcome::Complete(a) = old.verify(&ops).unwrap() else {
            panic!()
        };
        let LocalCheckOutcome::Complete(b) = fresh.verify_local(&ops).unwrap() else {
            panic!()
        };
        assert_eq!(
            a.results.value, b.checked.results.value,
            "outcomes {source}"
        );
        let present = |v: &Verification<'_>| {
            format!(
                "{:?}",
                presentation::present(&p, v, &sources, SourceView::TestDsl.as_str()).unwrap()
            )
        };
        assert_eq!(
            present(&a.verification),
            present(&b.checked.verification),
            "diagnostics {source}"
        );
    }
}

fn independent_grounding(p: &LoweredProgram, actual: &PreparedCheck<'_>) {
    let full = GroundProgram::prepare_cartesian(&p.corpus, &p.domains(), &limits()).unwrap();
    let mut possible = full.input_atoms().cloned().collect::<BTreeSet<_>>();
    loop {
        let before = possible.len();
        for r in full.rules() {
            if r.body
                .iter()
                .filter(|l| l.polarity == Polarity::Positive)
                .all(|l| possible.contains(&l.term.atom))
            {
                possible.insert(r.head.atom.clone());
            }
        }
        if possible.len() == before {
            break;
        }
    }
    let index = GroundKeyIndex::build(&p.corpus, &p.keys, &full).unwrap();
    let expected = full
        .rules()
        .filter(|r| {
            r.body
                .iter()
                .filter(|l| l.polarity == Polarity::Positive)
                .all(|l| possible.contains(&l.term.atom))
        })
        .map(|r| {
            let key = &index.instances[&r.id];
            (key.clone(), index.content[key].clone())
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        actual.program().atoms().cloned().collect::<BTreeSet<_>>(),
        possible
    );
    assert_eq!(actual.keys().content, expected);
}
#[test]
fn grounding_matches_independent_cartesian_positive_closure() {
    for source in [
        "input i,j; slot a,b; a <- i; b <- j when available(a); a <- j when available(b);",
        "input i,j; slot a,b; a <- i when available(b); b <- j when available(a);",
        "input i,j; slot a,b; a <- i when not available(b); b <- j when available(a);",
        "input i,j; slot a,b; a <- i when input_value(i) is 1; a <- j; b <- i when available(a);",
        "input i,j; slot a,b; a <- i; a <- j; b <- i when available(a) and present(j);",
    ] {
        let (_, _, p) = lower(source);
        let l = limits();
        let r = request_evidence::request(&p, &l);
        let RequestPreparation::Complete(g) = r
            .prepare_with_grounding(
                &p.corpus,
                &p.keys,
                &(&l).into(),
                &mut FreshPlans,
                &mut FreshGrounding,
            )
            .unwrap()
        else {
            panic!()
        };
        independent_grounding(&p, &g);
    }
}
fn fresh_result(p: &LoweredProgram, l: &Limits) -> (Value, Accounted<ScopedResults>) {
    run_result(p, l, None)
}
fn run_result(
    p: &LoweredProgram,
    l: &Limits,
    mut session: Option<&mut crate::Session>,
) -> (Value, Accounted<ScopedResults>) {
    let req = request_evidence::request(p, l);
    let ops = l.into();
    let exhausted = |reason: Inconclusive, receipts| {
        (
            json!({"status":"inconclusive","phase":reason.phase,"resource":reason.resource}),
            Accounted {
                value: req.exhausted(reason),
                receipts,
            },
        )
    };
    let prep = if let Some(s) = session.as_deref_mut() {
        s.prepare(&req, &p.corpus, &p.keys, &ops)
    } else {
        req.prepare_with_grounding(
            &p.corpus,
            &p.keys,
            &ops,
            &mut FreshPlans,
            &mut FreshGrounding,
        )
    }
    .unwrap();
    match prep {
        RequestPreparation::Inconclusive { reason, receipts } => exhausted(reason, receipts),
        RequestPreparation::Complete(g) => {
            let g = g.admit(&ops).unwrap();
            match if let Some(s) = session {
                s.verify(&g, &ops)
            } else {
                g.verify_local(&ops)
            }
            .unwrap()
            {
                LocalCheckOutcome::Inconclusive { reason, receipts } => exhausted(reason, receipts),
                LocalCheckOutcome::Complete(r) => (
                    captured_report(&r.checked.verification, &Names { keys: &p.keys }),
                    r.checked.results,
                ),
            }
        }
    }
}

#[test]
fn grounding_resource_cases_match_fresh_cold_warm_and_evicted() {
    for (source, work) in resource_cases() {
        let (_, _, p) = lower(&source);
        let l = Limits {
            max_work: work,
            ..limits()
        };
        let expected = fresh_result(&p, &l);
        let mut session = crate::Session::with_grounding();
        assert_eq!(expected, run_result(&p, &l, Some(&mut session)));
        assert_eq!(expected, run_result(&p, &l, Some(&mut session)));
        session.evict_values();
        assert_eq!(expected, run_result(&p, &l, Some(&mut session)));
    }
}
#[test]
fn grounding_cached_edits_undo_and_current_diagnostics() {
    use denotate_test_dsl::{attribution::SourceView, presentation};
    for (_, before, after) in edit_cases() {
        let mut session = crate::Session::with_grounding();
        for source in [&before, &after, &before] {
            let (ast, sources) = parse(source);
            let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
                continue;
            };
            let l = limits();
            let ops = (&l).into();
            let req = request_evidence::request(&p, &l);
            assert_eq!(
                fresh_result(&p, &l),
                run_result(&p, &l, Some(&mut session)),
                "{source}"
            );
            let RequestPreparation::Complete(g) =
                session.prepare(&req, &p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let g = g.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(r) = session.verify(&g, &ops).unwrap() else {
                panic!()
            };
            let old = request_evidence::checked(&p, &l);
            let CheckOutcome::Complete(global) = old.verify(&ops).unwrap() else {
                panic!()
            };
            assert_eq!(global.results.value, r.checked.results.value);
            let present = |v: &Verification<'_>| {
                format!(
                    "{:?}",
                    presentation::present(&p, v, &sources, SourceView::TestDsl.as_str()).unwrap()
                )
            };
            assert_eq!(
                present(&global.verification),
                present(&r.checked.verification)
            );
            assert_eq!(session.grounding_stats().executed, 0);
            assert!(session.grounding_stats().reused > 0);
            assert!(
                session.stats().retained_bytes
                    + session.plan_stats().retained_bytes
                    + session.grounding_stats().retained_bytes
                    <= crate::Retention::default().max_bytes
            );
        }
    }
}
#[derive(Default)]
struct Capture {
    graph: Option<GroundingGraph>,
}
impl GroundingStore for Capture {
    fn ground(
        &mut self,
        g: &GroundingGraph,
        ops: &OperationalLimits,
    ) -> Result<BTreeMap<GroundingKey, std::sync::Arc<GroundingResult>>, CheckError> {
        self.graph = Some(g.clone());
        FreshGrounding.ground(g, ops)
    }
}
fn capture(source: &str) -> GroundingGraph {
    let (_, _, p) = lower(source);
    let l = limits();
    let req = request_evidence::request(&p, &l);
    let mut capture = Capture::default();
    assert!(matches!(
        req.prepare_with_grounding(
            &p.corpus,
            &p.keys,
            &(&l).into(),
            &mut FreshPlans,
            &mut capture
        )
        .unwrap(),
        RequestPreparation::Complete(_)
    ));
    capture.graph.unwrap()
}
#[test]
fn grounding_snapshot_drop_early_cutoff_updates_instances_and_receipts() {
    let before = capture("input i,j; slot a,b; a <- i; b <- j when available(a);");
    let after =
        capture("input i,j; slot a,b; a <- i; a <- i when present(i); b <- j when available(a);");
    let mut cache = crate::grounding::GroundingCache::default();
    let ops = (&limits()).into();
    cache.begin(16 * 1024 * 1024);
    let a = cache.ground(&before, &ops).unwrap();
    cache.begin(16 * 1024 * 1024);
    let b = cache.ground(&after, &ops).unwrap();
    assert_eq!(b, FreshGrounding.ground(&after, &ops).unwrap());
    assert!(
        cache.stats.executed > 0 && cache.stats.reused > 0,
        "{:?}",
        cache.stats
    );
    let mut changed = false;
    for (key, b) in &b {
        if let Some(a) = a.get(key) {
            if a.provider() == b.provider()
                && a.value.as_ref().unwrap().instances != b.value.as_ref().unwrap().instances
            {
                assert_ne!(a.receipt, b.receipt);
                changed = true;
                assert!(after.inputs.values().any(|v| v.providers.contains(key)));
            }
        }
    }
    assert!(changed);
}
#[test]
fn grounding_provider_guards_and_reverse_requests() {
    let g = capture("input i,j; slot a,b; a <- i; b <- j when available(a);");
    let ops = (&limits()).into();
    let unit = g.inputs.values().find(|u| !u.providers.is_empty()).unwrap();
    assert!(matches!(
        ground_owned_unit(
            unit,
            &BTreeMap::new(),
            &ops,
            &mut GroundingMetrics::default()
        ),
        Err(CheckError::Internal("missing grounding provider"))
    ));
    let mut incomplete = unit.as_ref().clone();
    incomplete.providers.clear();
    assert!(matches!(
        ground_owned_unit(
            &incomplete,
            &BTreeMap::new(),
            &ops,
            &mut GroundingMetrics::default()
        ),
        Err(CheckError::Internal("incomplete grounding provider edges"))
    ));
    let mut cache = crate::grounding::GroundingCache::default();
    cache.reverse_requests = true;
    cache.begin(16 * 1024 * 1024);
    assert_eq!(
        cache.ground(&g, &ops).unwrap(),
        FreshGrounding.ground(&g, &ops).unwrap()
    );
}

type RuleSpec<'a> = (&'a str, &'a str, Vec<(&'a str, bool)>);
fn generic(spec: &[RuleSpec<'_>]) -> (Corpus, SemanticKeys) {
    let mut c = Corpus::new();
    let mut keys = SemanticKeys::default();
    let mut relations = BTreeMap::new();
    for name in ["p", "a", "b", "c", "unused"] {
        let r = c
            .declare_relation(
                name,
                if name == "p" {
                    RelationRole::Input
                } else {
                    RelationRole::Derived
                },
                [],
            )
            .unwrap();
        keys.bind_relation(
            &c,
            r,
            RelationKey::Named(QualifiedKey::new("grounding-tests", name)),
        )
        .unwrap();
        relations.insert(name, r);
    }
    for (name, head, body) in spec {
        let key = RuleKey::Library(QualifiedKey::new("grounding-tests", *name));
        let h = c.atom(relations[head], []).unwrap();
        let mut occurrences = vec![h.id()];
        let body = body
            .iter()
            .map(|(r, neg)| {
                let a = c.atom(relations[r], []).unwrap();
                occurrences.push(a.id());
                if *neg {
                    Literal::Negative(a)
                } else {
                    Literal::Positive(a)
                }
            })
            .collect::<Vec<_>>();
        let r = c.add_rule(h, body).unwrap();
        keys.bind_rule(&c, r, key.clone()).unwrap();
        for (atom, id) in occurrences.into_iter().enumerate() {
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
    }
    (c, keys)
}
#[test]
fn grounding_retractions_alternative_supports_scc_merge_split_and_negative_edits() {
    let open = vec![
        ("seed", "a", vec![("p", false)]),
        ("ab", "b", vec![("a", false)]),
        ("bc", "c", vec![("b", false)]),
    ];
    let mut cycle = open.clone();
    cycle.push(("ca", "a", vec![("c", false)]));
    let mut alternative = cycle.clone();
    alternative.push(("seed2", "a", vec![("p", false)]));
    let mut one_support = alternative.clone();
    one_support.remove(0);
    let no_support = cycle[1..].to_vec();
    let mut negative = open.clone();
    negative[2].2.push(("unused", true));
    let history = [
        open.clone(),
        cycle.clone(),
        alternative,
        one_support,
        no_support.clone(),
        open.clone(),
        negative,
        open,
        cycle,
        no_support,
    ];
    let mut session = crate::Session::with_grounding();
    for spec in history {
        let (c, keys) = generic(&spec);
        let l = limits();
        let ops = (&l).into();
        let req = CheckRequest::all_obligations(&c, &keys, &Domains::new(), &[], &l).unwrap();
        let RequestPreparation::Complete(fresh) = req
            .prepare_with_grounding(&c, &keys, &ops, &mut FreshPlans, &mut FreshGrounding)
            .unwrap()
        else {
            panic!()
        };
        let RequestPreparation::Complete(cached) = session.prepare(&req, &c, &keys, &ops).unwrap()
        else {
            panic!()
        };
        assert_eq!(fresh.keys().content, cached.keys().content);
        assert_eq!(fresh.receipts(), cached.receipts());
        let full = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        let mut possible = full.input_atoms().cloned().collect::<BTreeSet<_>>();
        loop {
            let n = possible.len();
            for r in full.rules() {
                if r.body
                    .iter()
                    .filter(|a| a.polarity == Polarity::Positive)
                    .all(|a| possible.contains(&a.term.atom))
                {
                    possible.insert(r.head.atom.clone());
                }
            }
            if possible.len() == n {
                break;
            }
        }
        assert_eq!(possible, cached.program().atoms().cloned().collect());
        let full_keys = GroundKeyIndex::build(&c, &keys, &full).unwrap();
        let expected = full
            .rules()
            .filter(|r| {
                r.body
                    .iter()
                    .filter(|a| a.polarity == Polarity::Positive)
                    .all(|a| possible.contains(&a.term.atom))
            })
            .map(|r| {
                let k = &full_keys.instances[&r.id];
                (k.clone(), full_keys.content[k].clone())
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(expected, cached.keys().content);
        if !spec.iter().any(|(n, _, _)| n.starts_with("seed")) {
            assert_eq!(
                cached.program().atoms().count(),
                1,
                "recursive support survived deletion"
            );
        }
    }
}
fn singleton(n: usize) -> GroundingInput {
    let relation = RelationKey::Named(QualifiedKey::new("grounding-retention", format!("i{n}")));
    GroundingInput {
        key: GroundingKey(BTreeSet::from([relation.clone()])),
        providers: BTreeSet::new(),
        relations: BTreeMap::from([(
            relation,
            RelationSchema {
                input: true,
                parameters: vec![],
            },
        )]),
        domains: BTreeMap::new(),
        rules: BTreeMap::new(),
        plans: BTreeMap::new(),
        limits: (&limits()).into(),
    }
}
fn singleton_graph(start: usize, n: usize) -> GroundingGraph {
    let inputs = (start..start + n)
        .map(singleton)
        .map(|i| (i.key.clone(), std::sync::Arc::new(i)))
        .collect::<BTreeMap<_, _>>();
    GroundingGraph {
        order: inputs.keys().cloned().collect(),
        inputs,
    }
}
#[test]
fn grounding_recycles_slots_and_bounds_payload_and_oversize() {
    let mut cache = crate::grounding::GroundingCache::default();
    let ops = (&limits()).into();
    let mut retained = 0;
    let capacity = crate::grounding::MAX_UNITS;
    for start in [0, capacity, capacity * 2, capacity * 3] {
        let g = singleton_graph(start, capacity);
        cache.begin(16 * 1024 * 1024);
        assert_eq!(
            cache.ground(&g, &ops).unwrap(),
            FreshGrounding.ground(&g, &ops).unwrap()
        );
        assert_eq!(cache.stats.allocated_slots, capacity);
        assert!(cache.stats.retained_bytes <= 16 * 1024 * 1024);
        if retained != 0 {
            assert!(cache.stats.retained_bytes < retained * 2);
        }
        retained = cache.stats.retained_bytes;
    }
    let g = singleton_graph(0, capacity + 1);
    cache.begin(16 * 1024 * 1024);
    assert_eq!(
        cache.ground(&g, &ops).unwrap(),
        FreshGrounding.ground(&g, &ops).unwrap()
    );
    assert_eq!(cache.stats.bypassed_graphs, 1);
    let mut small = crate::grounding::GroundingCache::default();
    let g = singleton_graph(0, 1);
    small.begin(2048);
    assert_eq!(
        small.ground(&g, &ops).unwrap(),
        FreshGrounding.ground(&g, &ops).unwrap()
    );
    assert_eq!(small.stats.retained_units, 0);
    assert!(small.stats.retained_bytes <= 2048);
}
#[test]
fn grounding_limits_cancellation_and_all_pools_share_bytes() {
    let source = format!("{} s0 <- i1;", workload("distinct_literals", 8));
    let (_, _, p) = lower(&source);
    let ample = fresh_result(&p, &limits()).1.value;
    let caps = [0, 1, 20, 100, 1000, 100000];
    for cap in caps {
        for dimension in 0..4 {
            let mut l = limits();
            match dimension {
                0 => l.max_work = cap,
                1 => l.max_atoms = cap,
                2 => l.max_rules = cap,
                _ => l.max_dependencies = cap,
            };
            let mut s = crate::Session::with_grounding();
            let expected = fresh_result(&p, &l);
            for (k, v) in &expected.1.value.groups {
                if !matches!(v, ScopedResult::Inconclusive(_)) {
                    assert_eq!(Some(v.clone()), ample.group(k));
                }
            }
            assert_eq!(expected, run_result(&p, &l, Some(&mut s)));
            assert_eq!(expected, run_result(&p, &l, Some(&mut s)));
        }
    }
    let bytes = 4 * 1024 * 1024;
    let mut s = crate::Session::new_grounding(crate::Retention {
        max_bytes: bytes,
        max_entries: 1024,
        max_condition_nodes: 1_000_000,
    });
    let l = limits();
    let req = request_evidence::request(&p, &l);
    let ops = (&l).into();
    for _ in 0..3 {
        let RequestPreparation::Complete(g) = s.prepare(&req, &p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let g = g.admit(&ops).unwrap();
        s.verify(&g, &ops).unwrap();
        assert!(s.grounding_stats().allocated_slots > 0 && s.plan_stats().retained_bytes > 0);
        assert!(
            s.stats().retained_bytes
                + s.plan_stats().retained_bytes
                + s.grounding_stats().retained_bytes
                <= bytes
        );
    }
    let cancelled = OperationalLimits::from(&limits());
    cancelled.cancellation.cancel();
    assert!(matches!(
        s.prepare(&req, &p.corpus, &p.keys, &cancelled),
        Err(CheckError::Cancelled)
    ));
    let deadline = OperationalLimits {
        timeout: Duration::ZERO,
        ..ops.clone()
    };
    assert!(matches!(
        s.prepare(&req, &p.corpus, &p.keys, &deadline),
        Err(CheckError::Deadline { .. })
    ));
    assert!(matches!(
        s.prepare(&req, &p.corpus, &p.keys, &ops).unwrap(),
        RequestPreparation::Complete(_)
    ));
}
#[test]
fn grounding_interrupted_query_does_not_poison_recovery() {
    let g = capture("input i,j; slot a,b; a <- i; b <- j when available(a);");
    let mut cache = crate::grounding::GroundingCache::default();
    cache.begin(16 * 1024 * 1024);
    cache.interrupt_after_unit();
    assert!(matches!(
        cache.ground(&g, &(&limits()).into()),
        Err(CheckError::Cancelled)
    ));
    assert_eq!(cache.stats.retained_units, 0);
    let ops = (&limits()).into();
    cache.begin(16 * 1024 * 1024);
    assert_eq!(
        cache.ground(&g, &ops).unwrap(),
        FreshGrounding.ground(&g, &ops).unwrap()
    );
    assert_eq!(cache.stats.executed, g.inputs.len());
}

#[test]
fn grounding_equal_possible_provider_skips_all_downstream_units() {
    let graph = |extra: bool| {
        let mut rules = vec![
            ("seed", "a", vec![("p", false)]),
            ("ab", "b", vec![("a", false)]),
            ("bc", "c", vec![("b", false)]),
        ];
        if extra {
            rules.push(("alternative", "a", vec![("p", false)]));
        }
        let (c, keys) = generic(&rules);
        let l = limits();
        let r = CheckRequest::all_obligations(&c, &keys, &Domains::new(), &[], &l).unwrap();
        let mut capture = Capture::default();
        r.prepare_with_grounding(&c, &keys, &(&l).into(), &mut FreshPlans, &mut capture)
            .unwrap();
        capture.graph.unwrap()
    };
    let before = graph(false);
    let after = graph(true);
    let mut cache = crate::grounding::GroundingCache::default();
    let ops = (&limits()).into();
    cache.begin(16 * 1024 * 1024);
    let old = cache.ground(&before, &ops).unwrap();
    cache.begin(16 * 1024 * 1024);
    let new = cache.ground(&after, &ops).unwrap();
    assert_eq!(cache.stats.executed, 1);
    assert_eq!(cache.stats.reused, after.inputs.len() - 1);
    assert_eq!(new, FreshGrounding.ground(&after, &ops).unwrap());
    let changed = new
        .iter()
        .filter(|(k, v)| old[*k].receipt != v.receipt)
        .count();
    assert_eq!(changed, 1);
    assert!(
        new.iter()
            .any(|(k, v)| old[k].value.as_ref().unwrap().instances
                != v.value.as_ref().unwrap().instances)
    );
    let mut receipts = WorkReceipts::default();
    for (k, r) in new {
        receipts
            .record(QueryKey::Grounding(k), r.receipt.clone())
            .unwrap();
    }
    assert_eq!(receipts.total().unwrap().queries.len(), after.inputs.len());
}
