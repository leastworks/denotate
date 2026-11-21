use super::*;

fn declared(
    c: &mut Corpus,
    h: Option<RelationId>,
    decisions: Option<BTreeSet<RelationId>>,
    obligations: &[ObligationId],
) -> VerificationId {
    c.verification_with_options_in(
        Namespace::default(),
        format!("projection{}", c.verifications().count()),
        [],
        obligations.iter().copied(),
        [],
        VerificationOptions {
            semantics: Semantics::Completion,
            hypothesis: h,
            decisions,
        },
    )
    .unwrap()
}

#[test]
fn a_contradictory_classification_is_not_rejection_even_with_empty_decisions() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(h, true)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    for decisions in [None, Some(BTreeSet::new())] {
        let v = declared(&mut c, Some(h), decisions, &[total]);
        let e = prepare(&c, v, &Domains::new());
        assert!(matches!(
            e.observation([]).unwrap(),
            ObservationOutcome::ClassificationNoMeaning
        ));
        for _ in 0..2 {
            let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
            let class = r.classification.as_ref().unwrap();
            assert!(class.no_meaning.exists());
            assert!(matches!(class.rejected, Search::None));
            assert!(r.has_failures());
            assert!(!r.all_rejected());
            assert!(!r.is_incomplete());
            assert!(r.obligations[&total].complete());
            assert!(!r.obligations[&total].failed());
        }
    }
}

#[test]
fn second_query_cutoff_is_unknown_and_one_base_model_suffices_for_rejection() {
    let mut c = Corpus::new();
    let h = rel(&mut c, "h", false);
    let p = rel(&mut c, "p", false);
    let absent = rel(&mut c, "absent", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false), (absent, false)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    let v = declared(&mut c, Some(h), None, &[total]);
    let mut e = prepare(&c, v, &Domains::new());
    e.config.max_solves = 1;
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.is_incomplete());
    assert!(!r.all_rejected());
    assert!(!r.has_failures());
    assert!(!r.obligations[&total].complete());
    let class = r.classification.unwrap();
    assert!(matches!(class.rejected, Search::Inconclusive(_)));
    assert!(matches!(class.no_meaning, Search::None));
    // The cone has two models without H. Existence must not spend another solve
    // distinguishing them: ambiguity without the hypothesis is irrelevant.
    e.config.max_solves = 3;
    let ObservationOutcome::Rejected { without_hypothesis } = e.observation([]).unwrap() else {
        panic!()
    };
    assert_eq!(
        without_hypothesis.scope(),
        ModelScope::ClassificationWithoutHypothesis
    );
    assert_eq!(without_hypothesis.value(&atom(h)), Some(false));
    assert_eq!(without_hypothesis.value(&atom(absent)), Some(false));
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.all_rejected());
    assert!(r.obligations[&total].failed());
    assert!(!r.is_incomplete());
}

#[test]
fn no_meaning_and_rejection_coexist_without_an_all_rejected_label() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(i, false), (h, true)]);
    let total = c
        .require_no_rejections_in(Namespace::default(), "total", h, "")
        .unwrap();
    let v = declared(&mut c, Some(h), None, &[total]);
    let r = prepare(&c, v, &Domains::new())
        .check(&keys(&c), &CheckOptions::default())
        .unwrap();
    let class = r.classification.as_ref().unwrap();
    assert!(class.rejected.exists());
    assert!(class.no_meaning.exists());
    assert!(!class.accepted.exists());
    assert!(!r.all_rejected());
    assert!(r.has_failures());
    assert!(!r.is_incomplete());
}

#[test]
fn projected_helpers_remain_free_for_processing_and_each_property() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "helper", false);
    let h = rel(&mut c, "h", false);
    let not_p = rel(&mut c, "not_helper", false);
    let not_h = rel(&mut c, "not_h", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, h, &[(p, true)]);
    rule(&mut c, not_p, &[(p, true)]);
    rule(&mut c, not_h, &[(h, true)]);
    let yes = c.empty("no_yes", p, "").unwrap();
    let no = c.empty("no_no", not_p, "").unwrap();
    let accepted_only = c.empty("accepted_only", not_h, "").unwrap();
    for decisions in [Some([h].into()), Some(BTreeSet::new())] {
        let v = declared(&mut c, Some(h), decisions, &[yes, no, accepted_only]);
        let e = prepare(&c, v, &Domains::new());
        for _ in 0..2 {
            let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
            assert!(r.classification.as_ref().unwrap().accepted.exists());
            assert!(!r.meaning.ambiguous.exists());
            assert!(!r.meaning.no_meaning.exists());
            assert!(r.obligations[&yes].failed());
            assert!(r.obligations[&no].failed());
            assert!(!r.obligations[&accepted_only].failed());
            assert!(!r.is_incomplete());
        }
        // A downstream contradiction for helper=false may narrow the helper,
        // but must not reject the already established decision h=true.
        let name = format!("odd{}", c.relations().count());
        let odd = rel(&mut c, &name, false);
        rule(&mut c, odd, &[(odd, true), (p, true)]);
        let fresh = prepare(&c, v, &Domains::new());
        let ObservationOutcome::Accepted {
            processing: Interpretations::Unique(model),
            ..
        } = fresh.observation([]).unwrap()
        else {
            panic!()
        };
        assert_eq!(model.value(&atom(p)), Some(true));
    }
    let strict = declared(&mut c, Some(h), None, &[]);
    assert!(matches!(
        prepare(&c, strict, &Domains::new())
            .observation([])
            .unwrap(),
        ObservationOutcome::Ambiguous { .. }
    ));
}

#[test]
fn projected_verification_reports_match_exhaustive_authored_equations() {
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
                for decisions in [
                    None,
                    Some(BTreeSet::new()),
                    Some([p].into()),
                    Some([q].into()),
                ] {
                    let count = |models: &[BTreeSet<RelationId>]| {
                        models
                            .iter()
                            .map(|m| {
                                m.iter()
                                    .copied()
                                    .filter(|r| decisions.as_ref().is_none_or(|ds| ds.contains(r)))
                                    .collect::<BTreeSet<_>>()
                            })
                            .collect::<BTreeSet<_>>()
                            .len()
                    };
                    let v = declared(&mut c, h, decisions.clone(), &[o]);
                    let e = prepare(&c, v, &Domains::new());
                    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
                    let (
                        mut accepted,
                        mut rejected,
                        mut class_many,
                        mut class_none,
                        mut processing_none,
                        mut processing_many,
                        mut failure,
                    ) = (false, false, false, false, false, false, false);
                    for value in [false, true] {
                        if let Some(h) = h {
                            let models = oracle(&c, &[h], input, value, Some(h));
                            match count(&models) {
                                0 => {
                                    if oracle(&c, &[h], input, value, None).is_empty() {
                                        class_none = true;
                                    } else {
                                        rejected = true;
                                    }
                                    continue;
                                }
                                1 => accepted = true,
                                _ => {
                                    class_many = true;
                                    continue;
                                }
                            }
                        }
                        let meanings = oracle(&c, &[p, q], input, value, h);
                        processing_none |= meanings.is_empty();
                        processing_many |= count(&meanings) > 1;
                        let mut roots = vec![q];
                        roots.extend(h);
                        failure |= oracle(&c, &roots, input, value, h)
                            .iter()
                            .any(|m| m.contains(&q));
                    }
                    assert!(!r.is_incomplete(), "{left}/{right}/{h:?}/{decisions:?}");
                    if let Some(class) = &r.classification {
                        assert_eq!(class.accepted.exists(), accepted);
                        assert_eq!(class.rejected.exists(), rejected);
                        assert_eq!(class.ambiguous.exists(), class_many);
                        assert_eq!(class.no_meaning.exists(), class_none);
                    }
                    assert_eq!(r.meaning.no_meaning.exists(), processing_none);
                    assert_eq!(r.meaning.ambiguous.exists(), processing_many);
                    assert_eq!(r.obligations[&o].failed(), failure);
                }
            }
        }
    }
}

#[test]
fn hypothesis_stays_required_when_it_is_not_a_selected_decision() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    let bad = rel(&mut c, "bad", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, h, &[(p, false)]);
    rule(&mut c, bad, &[(p, true)]);
    let o = c.empty("clean", bad, "").unwrap();
    let v = declared(&mut c, Some(h), Some(BTreeSet::new()), &[o]);
    let e = prepare(&c, v, &Domains::new());
    let ObservationOutcome::Accepted {
        processing: Interpretations::Unique(model),
        ..
    } = e.observation([]).unwrap()
    else {
        panic!()
    };
    assert_eq!(model.value(&atom(h)), Some(true));
    assert_eq!(model.value(&atom(p)), Some(true));
    let r = e.check(&keys(&c), &CheckOptions::default()).unwrap();
    assert!(r.obligations[&o].complete());
    assert!(!r.obligations[&o].failed());
}
