use super::*;
pub(super) fn compare(c: &Corpus, v: VerificationId) -> Report {
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
    // Force partitions even on tiny questions that unsplit-first answers quickly.
    // Each branch must reuse the right proof context, never H in a no-H query.
    let mut branched = e.clone();
    branched.pruning = Some(Arc::new(std::sync::Mutex::new(
        crate::sat_probe::completion_query::pruning::Cache::for_engine(&e),
    )));
    let split = CheckOptions {
        split_depth: 2,
        prune: true,
        ..Default::default()
    };
    for class in [false, true] {
        if class && e.classification.is_none() {
            continue;
        }
        for exists in [false, true] {
            let got = symbolic::branches::test_partition(&branched, class, exists, &split).unwrap();
            let expected = if class {
                let c = actual.classification.as_ref().unwrap();
                if exists {
                    c.no_meaning.exists()
                } else {
                    c.ambiguous.exists()
                }
            } else if exists {
                actual.meaning.no_meaning.exists()
            } else {
                actual.meaning.ambiguous.exists()
            };
            assert_eq!(got.exists(), expected);
            assert!(matches!(got, Search::Exists(()) | Search::None));
        }
    }

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
        if negative {
            assert!(r.pruning.records.iter().any(|p| p.head == atom(accepted)
                && p.kind == PruningKind::Subsumption
                && p.context == PruningContext::World));
        } else {
            assert!(
                r.pruning.records.is_empty(),
                "locally unique positive loop needs no pruning"
            );
            assert!(r.pruning.components.iter().any(|c| c.kind == "unique"));
        }
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
        assert!(
            !r.pruning.records.iter().any(|p0| p0.head == atom(p)),
            "acyclic property head is not a pruning target"
        );
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
        r.pruning.records.is_empty(),
        "locally unique even cycle needs no pruning"
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
                    super::super::pruning::Cache::for_engine(&e),
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

#[test]
fn targeted_round_robin_reaches_both_wide_heads_and_skips_acyclic_decoys() {
    let mut c = Corpus::new();
    let input = rel(&mut c, "type_guard", true);
    let heads = [
        rel(&mut c, "accepted_a", false),
        rel(&mut c, "accepted_b", false),
    ];
    for (i, h) in heads.iter().enumerate() {
        rule(&mut c, *h, &[(input, false)]);
        for j in 0..32 {
            let profile = rel(&mut c, &format!("profile_{i}_{j}"), false);
            rule(&mut c, profile, &[(input, false), (*h, true)]);
            rule(&mut c, *h, &[(profile, false)]);
        }
    }
    let decoy = rel(&mut c, "acyclic_decoy", false);
    rule(&mut c, decoy, &[(input, false)]);
    rule(&mut c, decoy, &[(input, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Domains::new());
    let opts = CheckOptions {
        prune: true,
        ..Default::default()
    };
    let r = e.check(&keys(&c), &opts).unwrap();
    super::scale::same_report(&r, &e.check_unpruned(&keys(&c), &opts).unwrap());
    for h in heads {
        assert!(
            r.pruning
                .records
                .iter()
                .any(|p| p.head == atom(h) && p.kind == PruningKind::Subsumption)
        );
        assert!(
            r.pruning
                .components
                .iter()
                .any(|row| row.candidate_examples.contains(&atom(h)) && row.proved > 0)
        );
    }
    assert!(!r.pruning.records.iter().any(|p| p.head == atom(decoy)));
    assert!(
        r.pruning
            .components
            .iter()
            .all(|row| row.considered >= row.proved)
    );
    assert!(matches!(r.meaning.no_meaning, Search::None));
    assert!(matches!(r.meaning.ambiguous, Search::None));
}

#[test]
fn locally_nonunique_positive_loop_can_be_pruned_without_becoming_unique() {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(p, false)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(p, false)]);
    let v = verification(&mut c, None, &[]);
    let r = compare(&c, v);
    assert!(r.meaning.ambiguous.exists());
    assert!(
        r.pruning
            .records
            .iter()
            .any(|r| r.kind == PruningKind::Subsumption)
    );
    assert!(
        r.pruning
            .components
            .iter()
            .any(|r| r.kind == "non-unique" && r.proved > 0)
    );
}

#[test]
fn pruning_refreshes_targets_until_a_complete_unchanged_round() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false)]);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(i, false), (p, true)]);
    let v = verification(&mut c, None, &[]);
    let report = compare(&c, v);
    assert!(!report.pruning.records.is_empty());
    assert!(
        report
            .pruning
            .views
            .iter()
            .any(|v| v.rounds > 1 && v.stop == PruningStop::Saturated)
    );
    let e = prepare(&c, v, &Domains::new());
    let mut limited = e.clone();
    limited.limits.pruning_allowance = Some(Duration::ZERO);
    let report = limited
        .check(
            &keys(&c),
            &CheckOptions {
                prune: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(
        report
            .pruning
            .views
            .iter()
            .any(|v| v.stop == PruningStop::OverallCutoff)
    );
    super::scale::same_report(&report, &e.check(&keys(&c), &Default::default()).unwrap());
}
