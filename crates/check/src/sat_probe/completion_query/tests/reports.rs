use super::*;

#[test]
fn verification_reports_match_exhaustive_authored_equations_and_property_cones() {
    for left in 0..6 {
        for right in 0..6 {
            let mut c = Corpus::new();
            let input = rel(&mut c, "input", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let atoms = [input, p, q];
            rule(&mut c, p, &[(atoms[left / 2], left % 2 != 0)]);
            rule(&mut c, q, &[(atoms[right / 2], right % 2 != 0)]);
            let o = c.empty("empty_q", q, "").unwrap();
            for h in [None, Some(p)] {
                let v = selected(&mut c, h, &[o]);
                let e = prepare(&c, v, &Domains::new());
                let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
                let (mut accept, mut reject, mut ambiguous, mut no_meaning, mut many, mut failure) =
                    (false, false, false, false, false, false);
                for value in [false, true] {
                    if let Some(h) = h {
                        match oracle(&c, &[h], input, value, Some(h)).len() {
                            0 => {
                                reject = true;
                                continue;
                            }
                            1 => accept = true,
                            _ => {
                                ambiguous = true;
                                continue;
                            }
                        }
                    }
                    let meanings = oracle(&c, &[p, q], input, value, h);
                    no_meaning |= meanings.is_empty();
                    many |= meanings.len() > 1;
                    let mut roots = vec![q];
                    roots.extend(h);
                    failure |= oracle(&c, &roots, input, value, h)
                        .iter()
                        .any(|m| m.contains(&q));
                }
                assert!(!r.is_incomplete(), "{left} {right} {h:?}");
                if let Some(class) = &r.classification {
                    assert_eq!(class.accepted.exists(), accept);
                    assert_eq!(class.rejected.exists(), reject);
                    assert_eq!(class.ambiguous.exists(), ambiguous);
                }
                assert_eq!(r.meaning.no_meaning.exists(), no_meaning);
                assert_eq!(r.meaning.ambiguous.exists(), many);
                assert_eq!(r.obligations[&o].failed(), failure);
            }
        }
    }
}

#[test]
fn unknown_classification_does_not_prove_properties_or_invent_rejection() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[]);
    let o = c.empty("empty_h", h, "").unwrap();
    let total = c
        .require_no_rejections_in(Namespace::new(["test"]).unwrap(), "total", h, "")
        .unwrap();
    let v = selected(&mut c, Some(h), &[o, total]);
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 2;
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.is_incomplete());
    assert!(!r.obligations[&o].complete());
    assert!(!r.obligations[&o].failed());
    // A validated first classification model still proves that no input rejects.
    assert!(r.obligations[&total].complete());
    assert!(!r.obligations[&total].failed());
}

fn selected(c: &mut Corpus, h: Option<RelationId>, obligations: &[ObligationId]) -> VerificationId {
    c.verification_with_options_in(
        Namespace::new(["test"]).unwrap(),
        format!("check{}", c.verifications().count()),
        [],
        obligations.iter().copied(),
        [],
        VerificationOptions {
            semantics: Semantics::Completion,
            hypothesis: h,
        },
    )
    .unwrap()
}
#[test]
fn all_rejected_is_explicit_and_only_no_rejections_turns_it_into_failure() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    let bad = rel(&mut c, "bad", false);
    let empty = c.empty("clean", bad, "").unwrap();
    let total = c
        .require_no_rejections_in(Namespace::new(["test"]).unwrap(), "total", h, "")
        .unwrap();
    for obligations in [vec![empty], vec![empty, total]] {
        let v = selected(&mut c, Some(h), &obligations);
        let e = prepare(&c, v, &Domains::new());
        let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
        assert!(r.all_rejected());
        assert!(!r.meaning.applicable);
        assert!(!r.is_incomplete());
        assert_eq!(r.has_failures(), obligations.contains(&total));
        assert!(r.obligations[&empty].vacuous);
    }
}

#[test]
fn all_rejected_makes_symbolic_coverage_vacuous_without_running_that_solver() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "input", true);
    let h = rel(&mut c, "h", false);
    let o = c.at_least_one("coverage", i, [], "").unwrap();
    let v = selected(&mut c, Some(h), &[o]);
    let e = prepare(&c, v, &Domains::new());
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.all_rejected());
    assert!(!r.is_incomplete());
    assert!(r.obligations[&o].vacuous);
}
#[test]
fn acceptance_and_rejection_are_quantified_outside_the_hypothesis() {
    let mut c = Corpus::new();
    let input = rel(&mut c, "input", true);
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(input, false)]);
    let total = c
        .require_no_rejections_in(Namespace::new(["test"]).unwrap(), "total", h, "")
        .unwrap();
    let v = selected(&mut c, Some(h), &[total]);
    let e = prepare(&c, v, &Domains::new());
    for _ in 0..2 {
        let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
        let cls = r.classification.as_ref().unwrap();
        assert!(cls.accepted.exists());
        assert!(cls.rejected.exists());
        assert!(matches!(cls.ambiguous, Search::None));
        assert!(r.obligations[&total].failed());
        assert!(!r.is_incomplete());
        assert!(!r.all_rejected());
    }
}
#[test]
fn properties_keep_circular_completion_models_and_independent_processing_failures() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    let odd = rel(&mut c, "odd", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, odd, &[(odd, true)]);
    let o = c.empty("empty_p", p, "").unwrap();
    let v = selected(&mut c, Some(h), &[o]);
    let e = prepare(&c, v, &Domains::new());
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.meaning.no_meaning.exists());
    assert!(r.obligations[&o].failed());
    assert!(!r.is_incomplete());
    let m = r.obligations[&o].parts[0].example.as_ref().unwrap();
    assert_eq!(m.scope(), ModelScope::Property);
    assert_eq!(m.value(&atom(p)), Some(true));
    assert_eq!(m.value(&atom(odd)), None);
    assert!(matches!(r.advisory, Advisory::NotRequested));
    let r = e
        .check(
            &keys(&c),
            &CheckOptions {
                circular_support: true,
                ..Default::default()
            },
        )
        .unwrap();
    let Advisory::Checked {
        findings,
        incomplete,
    } = r.advisory
    else {
        panic!()
    };
    assert!(incomplete.is_none());
    assert_eq!(findings.len(), 1);
    assert!(!findings[0].cycle.is_empty());
    rule(&mut c, p, &[]);
    let e = prepare(&c, v, &Domains::new());
    let r = e
        .check(
            &keys(&c),
            &CheckOptions {
                circular_support: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(matches!(r.advisory,Advisory::Checked{findings,..} if findings.is_empty()));
}
#[test]
fn ambiguous_classification_is_never_used_as_an_accepted_property_witness() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, h, &[(p, true)]);
    let o = c.empty("empty_p", p, "").unwrap();
    let total = c
        .require_no_rejections_in(Namespace::new(["test"]).unwrap(), "total", h, "")
        .unwrap();
    let v = selected(&mut c, Some(h), &[o, total]);
    let e = prepare(&c, v, &Domains::new());
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.classification.as_ref().unwrap().ambiguous.exists());
    assert!(!r.obligations[&o].failed());
    assert!(r.obligations[&total].complete());
    assert!(!r.obligations[&total].failed());
    assert!(!r.is_incomplete());
    assert!(r.has_failures());
}
#[test]
fn a_confirmed_rejection_survives_enumeration_exhaustion() {
    let mut c = Corpus::new();
    rel(&mut c, "input", true);
    let h = rel(&mut c, "h", false);
    let total = c
        .require_no_rejections_in(Namespace::new(["test"]).unwrap(), "total", h, "")
        .unwrap();
    let v = selected(&mut c, Some(h), &[total]);
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
    assert!(r.is_incomplete());
    assert!(r.has_failures());
    assert!(r.obligations[&total].failed());
    assert!(!r.all_rejected());
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(!r.is_incomplete());
    assert!(r.all_rejected());
}
#[test]
fn no_hypothesis_keeps_independent_properties_and_no_rejection_classification() {
    let mut c = Corpus::new();
    let bad = rel(&mut c, "bad", false);
    let odd = rel(&mut c, "odd", false);
    rule(&mut c, bad, &[]);
    rule(&mut c, odd, &[(odd, true)]);
    let o = c.empty("clean", bad, "").unwrap();
    let v = selected(&mut c, None, &[o]);
    let e = prepare(&c, v, &Domains::new());
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.classification.is_none());
    assert!(r.meaning.no_meaning.exists());
    assert!(r.obligations[&o].failed());
    assert!(!r.is_incomplete());
    assert!(matches!(
        e.check(
            &keys(&c),
            &CheckOptions {
                meaning: MeaningMode::None,
                ..Default::default()
            }
        ),
        Err(CheckError::InvalidRequest(_))
    ));
}
#[test]
fn advisory_exhaustion_does_not_change_required_results() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    let v = selected(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Domains::new());
    let r = e
        .check(
            &keys(&c),
            &CheckOptions {
                circular_support: true,
                advisory_limits: Limits {
                    max_work: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
    assert!(!r.has_failures());
    assert!(!r.is_incomplete());
    assert!(matches!(
        r.advisory,
        Advisory::Checked {
            incomplete: Some(_),
            ..
        }
    ));
}
