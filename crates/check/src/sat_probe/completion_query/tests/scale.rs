use super::*;

fn state<T>(s: &Search<T>) -> u8 {
    match s {
        Search::NotAnalysed => 0,
        Search::None => 1,
        Search::Exists(_) => 2,
        Search::Inconclusive(_) => 3,
    }
}
pub(in crate::sat_probe::completion_query) fn same_report(a: &Report, b: &Report) {
    assert_eq!(a.context, b.context);
    assert_eq!(a.is_incomplete(), b.is_incomplete());
    assert_eq!(a.has_failures(), b.has_failures());
    assert_eq!(a.all_rejected(), b.all_rejected());
    if let Some(a) = &a.classification {
        let b = b.classification.as_ref().unwrap();
        assert_eq!(state(&a.accepted), state(&b.accepted));
        assert_eq!(state(&a.rejected), state(&b.rejected));
        assert_eq!(state(&a.ambiguous), state(&b.ambiguous));
        assert_eq!(state(&a.no_meaning), state(&b.no_meaning));
    }
    assert_eq!(state(&a.meaning.no_meaning), state(&b.meaning.no_meaning));
    assert_eq!(state(&a.meaning.ambiguous), state(&b.meaning.ambiguous));
    assert_eq!(a.meaning.applicable, b.meaning.applicable);
    for (id, a) in &a.obligations {
        let b = &b.obligations[id];
        assert_eq!(a.failed(), b.failed());
        assert_eq!(a.complete(), b.complete());
        assert_eq!(a.vacuous, b.vacuous);
    }
}

#[test]
fn symbolic_matches_enumeration_with_two_inputs_projected_helpers_and_w() {
    for negative in [false, true] {
        for projection in [None, Some(BTreeSet::new())] {
            let mut c = Corpus::new();
            let i = rel(&mut c, "i", true);
            let j = rel(&mut c, "j", true);
            let p = rel(&mut c, "p", false);
            let h = rel(&mut c, "h", false);
            let bad = rel(&mut c, "bad", false);
            rule(&mut c, p, &[(p, negative), (i, false)]);
            rule(&mut c, h, &[(p, false)]);
            rule(&mut c, h, &[(j, false)]);
            rule(&mut c, bad, &[(j, false), (p, true), (bad, true)]);
            let o = c.empty("clean", p, "").unwrap();
            let no_j = c.assume_empty_in(Namespace::default(), "no_j", j).unwrap();
            for assumptions in [vec![], vec![no_j]] {
                for hypothesis in [None, Some(h), Some(i)] {
                    let v = c
                        .verification_with_options_in(
                            Namespace::default(),
                            format!("v{}", c.verifications().count()),
                            assumptions.clone(),
                            [o],
                            [],
                            VerificationOptions {
                                semantics: Semantics::Completion,
                                hypothesis,
                                decisions: projection.clone(),
                            },
                        )
                        .unwrap();
                    let e = prepare(&c, v, &Domains::new());
                    let expected = e
                        .check_enumerated(&keys(&c), &CheckOptions::default())
                        .unwrap();
                    for _ in 0..2 {
                        same_report(
                            &e.check(&keys(&c), &CheckOptions::default()).unwrap(),
                            &expected,
                        );
                    }
                    same_report(
                        &prepare(&c, v, &Domains::new())
                            .check(&keys(&c), &CheckOptions::default())
                            .unwrap(),
                        &expected,
                    );
                }
            }
        }
    }
}

#[test]
fn input_independent_negative_cycle_is_certified_without_world_enumeration() {
    let mut c = Corpus::new();
    for i in 0..40 {
        rel(&mut c, &format!("input{i}"), true);
    }
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    let v = verification(&mut c, Some(p), &[]);
    let e = prepare(&c, v, &Domains::new());
    let r = e
        .check(
            &keys(&c),
            &CheckOptions {
                max_worlds: 1,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(!r.is_incomplete());
    assert!(!r.has_failures());
    let class = r.classification.unwrap();
    assert!(class.accepted.exists());
    assert!(matches!(class.rejected, Search::None));
    assert!(matches!(class.no_meaning, Search::None));
}

#[test]
fn known_failure_survives_an_independent_search_cutoff() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(p, true), (i, false)]);
    rule(&mut c, q, &[(p, true)]);
    rule(&mut c, bad, &[]);
    let o = c.empty("clean", bad, "").unwrap();
    let v = c
        .verification_with_options_in(
            Namespace::default(),
            "v",
            [],
            [o],
            [],
            VerificationOptions {
                semantics: Semantics::Completion,
                ..Default::default()
            },
        )
        .unwrap();
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 1;
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.is_incomplete());
    assert!(r.has_failures());
    assert!(r.obligations[&o].failed());
    assert!(matches!(r.meaning.no_meaning, Search::Inconclusive(_)));
}

#[test]
fn advisory_samples_worlds_separately_and_keeps_original_component_identity() {
    let mut c = Corpus::new();
    rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    let missing = rel(&mut c, "missing", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, q, &[(q, false)]);
    rule(&mut c, p, &[(q, false), (missing, false)]);
    rule(&mut c, q, &[(p, false), (missing, false)]);
    rule(&mut c, h, &[(p, false), (q, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    let ordinary = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    let r = e
        .check(
            &keys(&c),
            &CheckOptions {
                circular_support: true,
                ..Default::default()
            },
        )
        .unwrap();
    same_report(&ordinary, &r);
    let Advisory::Checked {
        findings,
        incomplete,
    } = r.advisory
    else {
        panic!()
    };
    assert!(incomplete.is_none());
    assert_eq!(findings.len(), 1);
    assert_eq!(findings[0].component, BTreeSet::from([atom(p), atom(q)]));
}

#[test]
fn requested_advisory_reports_empty_or_unknown_context_without_changing_it() {
    let mut c = Corpus::new();
    let missing = rel(&mut c, "missing", false);
    let a = c
        .assume_at_least_one_in(Namespace::default(), "impossible", missing, [])
        .unwrap();
    let v = verification(&mut c, Some(missing), &[a]);
    let mut e = prepare(&c, v, &Domains::new());
    let options = CheckOptions {
        circular_support: true,
        ..Default::default()
    };
    let r = e.check(&keys(&c), &options).unwrap();
    assert_eq!(r.context, Context::InconsistentAssumptions);
    assert!(matches!(
        r.advisory,
        Advisory::Checked {
            incomplete: None,
            ..
        }
    ));
    e.config.max_solves = 0;
    let ordinary = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    let r = e.check(&keys(&c), &options).unwrap();
    same_report(&ordinary, &r);
    assert!(matches!(
        r.advisory,
        Advisory::Checked {
            incomplete: Some(_),
            ..
        }
    ));
}

#[test]
fn local_non_total_boundary_is_not_a_global_counterexample() {
    for hypothesis in [false, true] {
        let mut c = Corpus::new();
        let p = rel(&mut c, "optional_provider", false);
        let bad = rel(&mut c, "contradiction_if_provider", false);
        rule(&mut c, p, &[(p, false)]);
        rule(&mut c, bad, &[(p, false), (bad, true)]);
        let v = verification(&mut c, hypothesis.then_some(p), &[]);
        let e = prepare(&c, v, &Domains::new());
        let r = e.check(&keys(&c), &Default::default()).unwrap();
        same_report(
            &r,
            &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
        );
        assert_eq!(r.meaning.no_meaning.exists(), hypothesis);
    }
}

#[test]
fn unreachable_boundary_assignment_is_checked_in_its_upstream_cone() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "impossible_provider", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(i, false), (i, true)]);
    rule(&mut c, bad, &[(p, false), (bad, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Domains::new());
    let r = e.check(&keys(&c), &Default::default()).unwrap();
    same_report(
        &r,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(matches!(r.meaning.no_meaning, Search::None));
}

#[test]
fn complementary_producers_lift_a_boundary_pin_without_losing_models() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(p, true)]);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, p, &[(i, true)]);
    rule(&mut c, q, &[(p, false)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Domains::new());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let r = e.check_unpruned(&keys(&c), &Default::default()).unwrap();
    same_report(
        &r,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    let snapshot = sizes.snapshot();
    let stats = &snapshot
        .searches
        .iter()
        .find(|s| s.phase == "completion processing existence")
        .unwrap()
        .existence;
    assert!(
        stats.lifted_pins > 0,
        "complementary alternatives should remove an otherwise unnecessary pin"
    );
    assert!(stats.validation_work > 0);
    assert!(matches!(r.meaning.no_meaning, Search::None));
}

#[test]
fn deadline_shares_leave_room_for_later_questions_and_never_restart_deadline() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Domains::new());
    let deadline = Instant::now() + Duration::from_secs(60);
    e.limits.run_deadline = Some(deadline);
    e.limits.timeout = Duration::from_secs(60);
    let first = e.shared_limits(4);
    let last = e.shared_limits(1);
    assert_eq!(first.run_deadline, Some(deadline));
    assert_eq!(last.run_deadline, Some(deadline));
    assert!(first.timeout < last.timeout);
    assert!(first.timeout <= Duration::from_secs(15));
    assert!(last.timeout <= Duration::from_secs(60));
}

#[test]
fn component_proofs_share_the_search_candidate_allowance() {
    let mut c = Corpus::new();
    for suffix in ["a", "b"] {
        let p = rel(&mut c, &format!("p_{suffix}"), false);
        let q = rel(&mut c, &format!("q_{suffix}"), false);
        let i = rel(&mut c, &format!("i_{suffix}"), true);
        rule(&mut c, p, &[(p, true)]);
        rule(&mut c, p, &[(i, false)]);
        rule(&mut c, p, &[(i, true)]);
        rule(&mut c, q, &[(p, false)]);
    }
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Domains::new());
    let short = e
        .check_unpruned(
            &keys(&c),
            &CheckOptions {
                max_worlds: 1,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(matches!(short.meaning.no_meaning, Search::Inconclusive(_)));
    let complete = e
        .check_unpruned(&keys(&c), &CheckOptions::default())
        .unwrap();
    assert!(matches!(complete.meaning.no_meaning, Search::None));
    same_report(
        &complete,
        &e.check_enumerated(&keys(&c), &CheckOptions::default())
            .unwrap(),
    );
}

#[test]
fn eligibility_lifts_many_irrelevant_pins_within_one_candidate_round() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, h, &[(q, false)]);
    for n in 0..80 {
        let i = rel(&mut c, &format!("i{n}"), true);
        let t = rel(&mut c, &format!("tautology{n}"), false);
        rule(&mut c, t, &[(i, false)]);
        rule(&mut c, t, &[(i, true)]);
        rule(&mut c, h, &[(t, false)]);
    }
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    let options = CheckOptions {
        max_worlds: 1,
        ..Default::default()
    };
    for _ in 0..2 {
        let r = e.check(&keys(&c), &options).unwrap();
        let class = r.classification.as_ref().unwrap();
        assert!(class.ambiguous.exists());
        assert!(matches!(class.accepted, Search::None));
        assert!(!r.is_incomplete());
    }
    let fresh = prepare(&c, v, &Domains::new())
        .check(&keys(&c), &options)
        .unwrap();
    assert!(!fresh.is_incomplete());
}

#[test]
fn call_consistent_components_need_no_boundary_enumeration_and_report_their_shape() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "left", false);
    let q = rel(&mut c, "right", false);
    for n in 0..80 {
        let i = rel(&mut c, &format!("guard{n}"), true);
        rule(&mut c, p, &[(q, true), (i, false)]);
    }
    rule(&mut c, q, &[(p, true)]);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Domains::new());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let events = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let observed = events.clone();
    e.limits.progress = crate::CheckingProgress::new(move |event| {
        if let Some(crate::CheckingTarget::CompletionExistence(s)) = event.target {
            if let Some(c) = s.current_component {
                observed.lock().unwrap().push(c);
            }
        }
    });
    let options = CheckOptions {
        max_worlds: 0,
        ..Default::default()
    };
    let first = e.check(&keys(&c), &options).unwrap();
    let again = e.check(&keys(&c), &options).unwrap();
    let fresh = prepare(&c, v, &Domains::new())
        .check(&keys(&c), &options)
        .unwrap();
    same_report(&first, &again);
    same_report(&first, &fresh);
    assert!(matches!(first.meaning.no_meaning, Search::None));
    let events = events.lock().unwrap();
    assert!(events.iter().any(|c| c.state == "analysing"));
    assert!(events.iter().any(|c| c.state == "total"
        && c.odd_components == 0
        && c.boundary == 80
        && c.relations.contains(&p)
        && c.relations.contains(&q)));
    let snapshot = sizes.snapshot();
    for search in snapshot.searches {
        assert_eq!(search.work, Some(search.work_by_phase.values().sum()));
        if search.phase == "completion processing existence" {
            assert!(
                !search
                    .encoding_details
                    .iter()
                    .any(|e| e.purpose == "component-totality"),
                "parity proof must precede SAT totality search"
            );
        }
    }
}
