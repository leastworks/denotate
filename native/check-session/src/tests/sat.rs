//! SAT portability: independent finite stable-model oracle, fresh/cached equality,
//! backend switching and current-snapshot diagnostics.
use super::*;

fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}

fn run(
    p: &LoweredProgram,
    backend: BackendIdentity,
    session: Option<&mut crate::Session>,
) -> Accounted<ScopedResults> {
    let l = limits();
    let mut req = request_evidence::request(p, &l);
    req.backend = backend;
    let RequestPreparation::Complete(g) = req.prepare(&p.corpus, &p.keys, &(&l).into()).unwrap()
    else {
        panic!()
    };
    let g = g.admit(&(&l).into()).unwrap();
    let LocalCheckOutcome::Complete(r) = match session {
        Some(session) => session.verify(&g, &(&l).into()),
        None => g.verify_local(&(&l).into()),
    }
    .unwrap() else {
        panic!()
    };
    for a in r.queries.values().filter(|a| a.input.uses_sat()) {
        assert!(a.evaluation.is_none());
    }
    r.checked.results.receipts.total().unwrap();
    r.checked.results
}

#[test]
fn sat_frozen_edits_fresh_cold_warm_evicted_and_backend_switch() {
    let data: Value =
        serde_json::from_str(include_str!("../../fixtures/OWNED-6b.2a-REFERENCE.json")).unwrap();
    let mut sources = data["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["source"].as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    for (_, a, b) in edit_cases() {
        sources.insert(a);
        sources.insert(b);
    }
    let mut session = crate::Session::default();
    let mut groups = 0;
    let mut recursive = 0;
    let mut rejected = 0;
    for source in sources {
        let (ast, src) = parse(&source);
        let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &src).unwrap() else {
            continue;
        };
        let fresh = run(&p, BackendIdentity::sat(), None);
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
        assert_eq!(
            session.stats().verdict_misses + session.stats().completion_misses,
            0,
            "{source}: {:?}",
            session.stats()
        );
        session.evict_values();
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
        let bdd = run(&p, BackendIdentity::bdd(), Some(&mut session));
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
        let l = limits();
        let prepared = request_evidence::checked(&p, &l);
        recursive += prepared
            .program()
            .components()
            .filter(|c| c.recursive && c.blocked_by.is_empty())
            .count();
        for (k, result) in &fresh.value.groups {
            groups += 1;
            match result {
                ScopedResult::Unsupported(UnsupportedReason::UnfoundedSupport(_)) => rejected += 1,
                ScopedResult::Counterexample(c, _) => {
                    let ScopedResult::Counterexample(b, _) = &bdd.value.groups[k] else {
                        panic!("SAT unsound: {source}")
                    };
                    if c.scope == CertificationScope::WholeProgram {
                        assert_eq!(c, b, "{source}");
                    }
                }
                _ => assert_eq!(result, &bdd.value.groups[k], "{source}"),
            }
        }
    }
    println!(
        "SAT_FROZEN_INVENTORY groups={groups} admitted_recursive_sccs={recursive} spurious_candidates={rejected}"
    );
    assert!(groups > 0);
}

type RuleSpec = (usize, Vec<(usize, bool)>);
fn generic(
    spec: &[RuleSpec],
    exclusive: bool,
) -> (Corpus, SemanticKeys, Domains, Vec<InputAtMostOne>) {
    let mut c = Corpus::new();
    let s = c.declare_sort("V").unwrap();
    let values = [
        c.declare_constant("a", s).unwrap(),
        c.declare_constant("b", s).unwrap(),
    ];
    let i = c
        .declare_relation("i", RelationRole::Input, [Parameter::new("v", s)])
        .unwrap();
    let d = c
        .declare_relation("d", RelationRole::Derived, [Parameter::new("v", s)])
        .unwrap();
    let u = c
        .declare_relation("u", RelationRole::Derived, [Parameter::new("v", s)])
        .unwrap();
    let relations = [i, d, u];
    for (h, body) in spec {
        let head = c.atom(relations[h / 2], [values[h % 2].into()]).unwrap();
        let body = body
            .iter()
            .map(|(a, neg)| {
                let atom = c.atom(relations[a / 2], [values[a % 2].into()]).unwrap();
                if *neg {
                    Literal::Negative(atom)
                } else {
                    Literal::Positive(atom)
                }
            })
            .collect::<Vec<_>>();
        c.add_rule(head, body).unwrap();
    }
    c.at_most_one("unique", d, [], "test").unwrap();
    let mut keys = SemanticKeys::default();
    let q = |n: &str| QualifiedKey::new("sat-tests", n);
    keys.bind_sort(&c, s, SortKey(q("V"))).unwrap();
    for constant in c.constants() {
        keys.bind_constant(
            &c,
            constant.id,
            ConstantKey {
                sort: SortKey(q("V")),
                name: constant.name.clone().into(),
            },
        )
        .unwrap();
    }
    for relation in c.relations() {
        keys.bind_relation(&c, relation.id, RelationKey::Named(q(&relation.name)))
            .unwrap();
    }
    for (index, rule) in c.rules().enumerate() {
        let key = RuleKey::Library(q(&format!("r{index}")));
        keys.bind_rule(&c, rule.id, key.clone()).unwrap();
        for (n, atom) in std::iter::once(&rule.head)
            .chain(rule.body.iter().map(Literal::atom))
            .enumerate()
        {
            keys.bind_occurrence(
                &c,
                atom.id(),
                OccurrenceKey::Library {
                    rule: key.clone(),
                    atom: n,
                    argument: None,
                },
            )
            .unwrap();
            for (a, argument) in atom.arguments().iter().enumerate() {
                keys.bind_occurrence(
                    &c,
                    argument.id(),
                    OccurrenceKey::Library {
                        rule: key.clone(),
                        atom: n,
                        argument: Some(a),
                    },
                )
                .unwrap();
            }
        }
    }
    for o in c.obligations() {
        keys.bind_obligation(&c, o.id, ObligationKey(q(&o.name)))
            .unwrap();
    }
    (
        c,
        keys,
        Domains::from([(s, values.to_vec())]),
        if exclusive {
            vec![InputAtMostOne {
                relation: i,
                group_by: vec![],
            }]
        } else {
            vec![]
        },
    )
}

// Independent GL-reduct enumeration; neither the SAT encoding nor checker replay
// defines this oracle. Enumerate all interpretations, then check least closure.
fn stable(spec: &[RuleSpec], world: usize) -> Vec<usize> {
    (0..4)
        .filter_map(|derived| {
            let candidate = world | (derived << 2);
            let mut closure = world;
            loop {
                let old = closure;
                for (head, body) in spec {
                    if body
                        .iter()
                        .any(|(a, negative)| *negative && candidate & (1 << a) != 0)
                    {
                        continue;
                    }
                    if body
                        .iter()
                        .filter(|(_, negative)| !negative)
                        .all(|(a, _)| closure & (1 << a) != 0)
                    {
                        closure |= 1 << head;
                    }
                }
                if old == closure {
                    break;
                }
            }
            (closure == candidate).then_some(candidate)
        })
        .collect()
}

#[test]
fn sat_small_worlds_completion_unsat_and_unfounded_candidates() {
    let cases = [
        vec![(2, vec![(0, false)]), (3, vec![(1, false)])],
        vec![(2, vec![(0, false)]), (3, vec![(0, true)])],
        vec![
            (2, vec![(0, false)]),
            (2, vec![(2, false)]),
            (3, vec![(1, false)]),
        ],
        vec![
            (2, vec![(0, false)]),
            (2, vec![(2, false)]),
            (3, vec![(0, false), (2, true)]),
        ],
        vec![
            (2, vec![(0, false)]),
            (3, vec![(2, false)]),
            (2, vec![(3, false)]),
        ],
        vec![(2, vec![]), (3, vec![])],
        vec![
            (2, vec![(0, false), (0, false)]),
            (3, vec![(1, false), (1, true)]),
        ],
    ];
    let mut unsupported = 0;
    let mut proved_recursive = 0;
    for spec in cases {
        for exclusive in [false, true] {
            let (c, keys, domains, constraints) = generic(&spec, exclusive);
            let l = limits();
            let ops = (&l).into();
            let mut request =
                CheckRequest::all_obligations(&c, &keys, &domains, &constraints, &l).unwrap();
            request.backend = BackendIdentity::sat();
            let RequestPreparation::Complete(g) = request.prepare(&c, &keys, &ops).unwrap() else {
                panic!()
            };
            let g = g.admit(&ops).unwrap();
            let CheckOutcome::Complete(report) = g.verify(&ops).unwrap() else {
                panic!()
            };
            let violating = (0..4)
                .filter(|w| !exclusive || *w != 3)
                .filter(|w| {
                    let models = stable(&spec, *w);
                    assert_eq!(models.len(), 1);
                    models[0] & 12 == 12
                })
                .collect::<BTreeSet<_>>();
            for result in report.results.value.groups.values() {
                match result {
                    ScopedResult::Proved => {
                        assert!(violating.is_empty());
                        proved_recursive +=
                            usize::from(g.program().components().any(|c| c.recursive));
                    }
                    ScopedResult::Counterexample(candidate, _) => {
                        let world = candidate.candidate.present.iter().fold(0, |w, a| {
                            w | if a.arguments[0].name.as_ref() == "a" {
                                1
                            } else {
                                2
                            }
                        });
                        assert!(violating.contains(&world));
                        // AtomKey order is a then b: lexicographic absent-first.
                        assert_eq!(
                            world,
                            *violating.iter().min_by_key(|w| (**w & 1, **w & 2)).unwrap()
                        );
                    }
                    ScopedResult::Unsupported(UnsupportedReason::UnfoundedSupport(candidate)) => {
                        unsupported += 1;
                        let world = candidate.present.iter().fold(0, |w, a| {
                            w | if a.arguments[0].name.as_ref() == "a" {
                                1
                            } else {
                                2
                            }
                        });
                        assert!(!violating.contains(&world));
                    }
                    other => panic!("unexpected SAT result: {other:?}"),
                }
            }
        }
    }
    assert!(unsupported > 0 && proved_recursive > 0);
}

#[test]
fn sat_bypass_and_validation_limits_preserve_results_and_status() {
    let (_, _, p) = lower("input i,j; slot a; a <- i; a <- j;");
    let fresh = run(&p, BackendIdentity::sat(), None);
    for bytes in [0, 1024, 16 * 1024] {
        let mut session = crate::Session::new(crate::Retention {
            max_bytes: bytes,
            ..Default::default()
        });
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
        assert_eq!(fresh, run(&p, BackendIdentity::sat(), Some(&mut session)));
    }
    let l = limits();
    let g = request_evidence::checked(&p, &l);
    let LocalCheckOutcome::Complete(r) = g.verify_local(&(&l).into()).unwrap() else {
        panic!()
    };
    let mut input = r
        .queries
        .values()
        .find(|a| matches!(a.input.scope, LocalScope::Group(_)))
        .unwrap()
        .input
        .clone();
    input.backend = BackendIdentity::sat();
    input.limits.max_work = 0;
    let memo = NoLocalMemo
        .execute(&input, &(&l).into(), &mut LocalMetrics::default())
        .unwrap();
    assert!(memo.failure.is_some());
    let cancelled = OperationalLimits::from(&l);
    cancelled.cancellation.cancel();
    assert!(matches!(
        NoLocalMemo.execute(&input, &cancelled, &mut LocalMetrics::default()),
        Err(CheckError::Cancelled)
    ));
    input.limits.max_work = l.max_work;
    let mut session = crate::Session::default();
    session.interrupt_after_evaluation();
    assert!(matches!(
        session.execute(
            &input,
            &OperationalLimits::from(&limits()),
            &mut LocalMetrics::default()
        ),
        Err(CheckError::Cancelled)
    ));
    let fresh_ops = OperationalLimits::from(&limits());
    let expected = NoLocalMemo
        .execute(&input, &fresh_ops, &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(
        expected,
        session
            .execute(&input, &fresh_ops, &mut LocalMetrics::default())
            .unwrap()
    );
    // A global admission budget failure must not erase a settled, disjoint cone.
    input.admission_limit = Some(Inconclusive {
        phase: "admission",
        resource: "work",
    });
    let bounded = NoLocalMemo
        .execute(&input, &fresh_ops, &mut LocalMetrics::default())
        .unwrap();
    assert_eq!(expected.answer, bounded.answer);
    assert!(bounded.failure.is_none());
}

#[test]
fn sat_keeps_valid_cone_finding_when_whole_program_needs_an_alternate_world() {
    // The conflict is unconditional. An unrelated negative cycle settles only
    // when i(a) is present. BDD retries that don't-care; SAT deliberately does not.
    let spec = vec![
        (2, vec![]),
        (3, vec![(0, false)]),
        (3, vec![(0, true)]),
        (4, vec![(0, true), (4, true)]),
    ];
    let (c, keys, domains, constraints) = generic(&spec, false);
    let l = limits();
    let ops = (&l).into();
    let mut request = CheckRequest::all_obligations(&c, &keys, &domains, &constraints, &l).unwrap();
    for sat in [false, true] {
        request.backend = if sat {
            BackendIdentity::sat()
        } else {
            BackendIdentity::bdd()
        };
        let RequestPreparation::Complete(g) = request.prepare(&c, &keys, &ops).unwrap() else {
            panic!()
        };
        let g = g.admit(&ops).unwrap();
        let CheckOutcome::Complete(r) = g.verify(&ops).unwrap() else {
            panic!()
        };
        let ScopedResult::Counterexample(candidate, _) =
            r.results.value.groups.values().next().unwrap()
        else {
            panic!("a certification failure erased the cone finding")
        };
        assert_eq!(
            candidate.scope,
            if sat {
                CertificationScope::ConeOnly
            } else {
                CertificationScope::WholeProgram
            }
        );
        if sat {
            assert!(candidate.candidate.present.is_empty());
            assert!(candidate.confined_to_no_meaning.is_empty());
        }
        assert!(!r.results.value.regions.is_empty());
    }
}
