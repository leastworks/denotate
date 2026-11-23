use super::*;
fn compare(c: &Corpus, v: VerificationId) -> Report {
    let e = prepare(c, v, &Domains::new());
    let options = CheckOptions {
        prune: true,
        ..Default::default()
    };
    let default = e.check(&keys(c), &CheckOptions::default()).unwrap();
    assert!(!default.pruning.enabled);
    assert_eq!(default.pruning.attempts, 0);
    let original = e.check_unpruned(&keys(c), &options).unwrap();
    let expected = e.check_enumerated(&keys(c), &options).unwrap();
    let actual = e.check(&keys(c), &options).unwrap();
    super::scale::same_report(&actual, &original);
    super::scale::same_report(&default, &original);
    assert!(actual.pruning.enabled);
    super::scale::same_report(&actual, &expected);
    super::scale::same_report(&actual, &e.check(&keys(c), &options).unwrap());
    super::scale::same_report(
        &actual,
        &prepare(c, v, &Domains::new())
            .check(&keys(c), &options)
            .unwrap(),
    );
    actual
}
#[test]
fn profile_producer_is_removed_using_its_common_equation() {
    for negative in [false, true] {
        let mut c = Corpus::new();
        let input = rel(&mut c, "type_guard", true);
        let accepted = rel(&mut c, "accepted", false);
        let profile = rel(&mut c, "profile", false);
        rule(&mut c, accepted, &[(input, false)]);
        rule(&mut c, accepted, &[(profile, false)]);
        rule(&mut c, profile, &[(input, false), (accepted, negative)]);
        let v = verification(&mut c, None, &[]);
        let r = compare(&c, v);
        assert!(r.pruning.records.iter().any(|p| p.head == atom(accepted)
            && p.kind == PruningKind::Subsumption
            && p.context == PruningContext::World));
        assert!(!r.meaning.ambiguous.exists());
        assert!(matches!(r.meaning.no_meaning, Search::None));
    }
}
#[test]
fn h_only_coverage_does_not_erase_rejections_or_classification_no_meaning() {
    for contradictory in [false, true] {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let h = rel(&mut c, "h", false);
        let p = rel(&mut c, "p", false);
        let bad = rel(&mut c, "bad", false);
        rule(&mut c, h, &[(i, false), (bad, true)]);
        rule(&mut c, p, &[(i, false)]);
        if contradictory {
            rule(&mut c, bad, &[(i, true), (bad, true)]);
        }
        let v = verification(&mut c, Some(h), &[]);
        let r = compare(&c, v);
        let class = r.classification.as_ref().unwrap();
        assert_eq!(class.no_meaning.exists(), contradictory);
        assert_eq!(class.rejected.exists(), !contradictory);
        assert!(r.pruning.records.iter().any(|p0| p0.head == atom(p)
            && p0.context == PruningContext::Hypothesis
            && p0.kind == PruningKind::Coverage));
        assert!(!r.pruning.records.iter().any(|p0| p0.head == atom(p)
            && p0.context == PruningContext::World
            && p0.kind == PruningKind::Coverage));
    }
}
#[test]
fn a_contradiction_cannot_prove_its_own_equation_redundant() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    rule(&mut c, p, &[(p, true)]);
    for h in [None, Some(p)] {
        let v = verification(&mut c, h, &[]);
        let r = compare(&c, v);
        if let Some(class) = r.classification {
            assert!(class.no_meaning.exists());
            assert!(!class.rejected.exists());
        } else {
            assert!(r.meaning.no_meaning.exists());
        }
        assert!(
            !r.pruning
                .records
                .iter()
                .any(|p| p.kind == PruningKind::Coverage)
        );
    }
}
#[test]
fn coverage_and_sequential_subsumption_preserve_all_questions() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, p, &[(i, true)]);
    rule(&mut c, p, &[(q, true)]);
    rule(&mut c, q, &[(p, true)]);
    let v = verification(&mut c, None, &[]);
    let r = compare(&c, v);
    assert!(
        r.pruning
            .records
            .iter()
            .any(|p0| p0.head == atom(p) && p0.kind == PruningKind::Coverage)
    );
}
#[test]
fn frozen_property_and_h_scopes_do_not_gain_constraints_from_elsewhere() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let outside = rel(&mut c, "outside", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, outside, &[(p, false), (outside, true)]);
    let o = c.empty("no_p", p, "").unwrap();
    let v = c
        .verification_with_options_in(
            Namespace::default(),
            "v",
            [],
            [o],
            [],
            VerificationOptions {
                semantics: Semantics::Completion,
                hypothesis: None,
                decisions: Some(BTreeSet::from([i])),
            },
        )
        .unwrap();
    let r = compare(&c, v);
    assert!(
        r.obligations[&o].failed(),
        "processing equation outside's contradiction must not force property p false"
    );
}
#[test]
fn pruning_matches_exhaustive_signed_programs_with_w_h_and_decision_projection() {
    for code in 0..216 {
        let mut c = Corpus::new();
        let input = rel(&mut c, "input", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        let atoms = [input, p, q];
        let mut rest = code;
        for head in [p, p, q] {
            let n = rest % 6;
            rest /= 6;
            rule(&mut c, head, &[(atoms[n / 2], n % 2 != 0)]);
        }
        let no_input = c
            .assume_empty_in(Namespace::default(), "no_input", input)
            .unwrap();
        let obligation = c.empty("empty_q", q, "").unwrap();
        for (h, assumptions) in [(None, vec![]), (Some(p), vec![]), (Some(p), vec![no_input])] {
            let v = c
                .verification_with_options_in(
                    Namespace::default(),
                    format!("v{}", c.verifications().count()),
                    assumptions,
                    [obligation],
                    [],
                    VerificationOptions {
                        semantics: Semantics::Completion,
                        hypothesis: h,
                        decisions: Some(BTreeSet::from([q])),
                    },
                )
                .unwrap();
            compare(&c, v);
        }
    }
}

// Compare interpretations themselves, not only existence/ambiguity verdicts.
// Includes interrupted simplification: every installed prefix is equivalent.
#[test]
fn every_completed_or_interrupted_pruning_prefix_preserves_models_both_ways() {
    fn models(c: &Cone, h: Option<usize>) -> BTreeSet<usize> {
        (0..1usize << c.atoms.len())
            .filter(|bits| {
                let values: Vec<_> = (0..c.fixed.len())
                    .map(|i| {
                        if i < c.atoms.len() {
                            bits & (1 << i) != 0
                        } else {
                            c.fixed[i].unwrap_or(false)
                        }
                    })
                    .collect();
                h.is_none_or(|i| values[i])
                    && (0..c.atoms.len()).all(|i| {
                        if c.input[i] {
                            true
                        } else if let Some(v) = c.fixed[i] {
                            values[i] == v
                        } else {
                            values[i]
                                == c.rules
                                    .iter()
                                    .filter(|r| r.head == i)
                                    .any(|r| r.body.iter().all(|(a, p)| values[*a] == *p))
                        }
                    })
            })
            .collect()
    }
    let mut saw_cutoff = false;
    let mut saw_proof = false;
    for code in 0..216 {
        let mut c = Corpus::new();
        let input = rel(&mut c, "input", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        let atoms = [input, p, q];
        let mut rest = code;
        for head in [p, p, q] {
            let n = rest % 6;
            rest /= 6;
            rule(&mut c, head, &[(atoms[n / 2], n % 2 != 0)]);
        }
        let v = verification(&mut c, Some(p), &[]);
        for work in [0, 100, 500, 2000, 20000] {
            for h in [false, true] {
                let mut e = prepare(&c, v, &Domains::new());
                e.limits.max_work = work;
                e.pruning = Some(Arc::new(std::sync::Mutex::new(
                    super::super::pruning::Cache::default(),
                )));
                let view =
                    super::super::pruning::view(&e, &e.cone, h, std::time::Duration::from_secs(10))
                        .unwrap();
                let h = h.then_some(e.classification.as_ref().unwrap().2);
                assert_eq!(
                    models(&e.cone, h),
                    models(&view, h),
                    "code {code}, work {work}, H {h:?}"
                );
                let cache = e.pruning.as_ref().unwrap().lock().unwrap();
                saw_cutoff |= !cache.report.incomplete.is_empty();
                saw_proof |= cache.report.removed > 0;
            }
        }
    }
    assert!(saw_cutoff && saw_proof);
}
