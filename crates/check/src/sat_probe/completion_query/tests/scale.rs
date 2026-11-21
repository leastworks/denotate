use super::*;

fn state<T>(s: &Search<T>) -> u8 {
    match s {
        Search::NotAnalysed => 0,
        Search::None => 1,
        Search::Exists(_) => 2,
        Search::Inconclusive(_) => 3,
    }
}
pub(super) fn same_report(a: &Report, b: &Report) {
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
    rule(&mut c, p, &[(q, true), (i, false)]);
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
