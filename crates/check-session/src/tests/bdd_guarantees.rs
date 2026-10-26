//! BDD guarantees retained from the backend experiment: independent stable-model
//! oracle, fresh/cached equality, eviction, limits and cancellation recovery.
use super::*;

fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}

fn run(p: &LoweredProgram, session: Option<&mut crate::Session>) -> Accounted<ScopedResults> {
    let l = limits();
    let req = request_evidence::request(p, &l);
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
    r.checked.results.receipts.total().unwrap();
    r.checked.results
}

#[test]
fn bdd_corpus_edits_fresh_cold_warm_and_evicted() {
    let mut sources = regression_cases()
        .into_iter()
        .map(|r| r["source"].as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    for (_, a, b) in edit_cases() {
        sources.insert(a);
        sources.insert(b);
    }
    let mut session = crate::Session::default();
    let mut groups = 0;
    for source in sources {
        let (ast, src) = parse(&source);
        let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &src).unwrap() else {
            continue;
        };
        let fresh = run(&p, None);
        assert_eq!(fresh, run(&p, Some(&mut session)));
        assert_eq!(fresh, run(&p, Some(&mut session)));
        assert_eq!(
            session.stats().verdict_misses + session.stats().completion_misses,
            0,
            "{source}: {:?}",
            session.stats()
        );
        session.evict_values();
        assert_eq!(fresh, run(&p, Some(&mut session)));
        groups += fresh.value.groups.len();
    }
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
    let q = |n: &str| QualifiedKey::new("stable-model-tests", n);
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

// Independent GL-reduct enumeration; neither BDD evaluation nor checker replay
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
fn bdd_small_worlds_match_stable_models_including_recursive_support() {
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
    let mut proved_recursive = 0;
    for spec in cases {
        for exclusive in [false, true] {
            let (c, keys, domains, constraints) = generic(&spec, exclusive);
            let l = limits();
            let ops = (&l).into();
            let request =
                CheckRequest::all_obligations(&c, &keys, &domains, &constraints, &l).unwrap();
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
                    }
                    other => panic!("unexpected BDD result: {other:?}"),
                }
            }
        }
    }
    assert!(proved_recursive > 0);
}

#[test]
fn bdd_bypass_limits_and_cancellation_recovery_preserve_results() {
    let (_, _, p) = lower("input i,j; slot a; a <- i; a <- j;");
    let fresh = run(&p, None);
    for bytes in [0, 1024, 16 * 1024] {
        let mut session = crate::Session::new(crate::Retention {
            max_bytes: bytes,
            ..Default::default()
        });
        assert_eq!(fresh, run(&p, Some(&mut session)));
        assert_eq!(fresh, run(&p, Some(&mut session)));
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
    let expired = OperationalLimits {
        timeout: Duration::ZERO,
        ..OperationalLimits::from(&limits())
    };
    assert!(matches!(
        NoLocalMemo.execute(&input, &expired, &mut LocalMetrics::default()),
        Err(CheckError::Deadline { .. })
    ));
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
fn bdd_certifies_an_alternate_world_without_losing_the_cone_finding() {
    // The conflict is unconditional. An unrelated negative cycle settles only
    // when i(a) is present. Certification retries that don't-care input.
    let spec = vec![
        (2, vec![]),
        (3, vec![(0, false)]),
        (3, vec![(0, true)]),
        (4, vec![(0, true), (4, true)]),
    ];
    let (c, keys, domains, constraints) = generic(&spec, false);
    let l = limits();
    let ops = (&l).into();
    let request = CheckRequest::all_obligations(&c, &keys, &domains, &constraints, &l).unwrap();
    {
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
        assert_eq!(candidate.scope, CertificationScope::WholeProgram);
        assert!(!r.results.value.regions.is_empty());
    }
}
