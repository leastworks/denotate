//! Cube lifting on cover paths that previously excluded unlifted cubes: the
//! no-H fallback of classification existence's H-first coverage (selected when
//! pruning is on), and rejection's H-model covers.
use super::*;

fn phase_stats(sizes: &crate::CompletionSizes, phase: &str) -> (usize, usize, usize) {
    sizes
        .snapshot()
        .searches
        .iter()
        .filter(|s| s.phase == phase)
        .fold((0, 0, 0), |(r, a, l), s| {
            (
                r + s.existence.rounds,
                a + s.existence.lifting_attempts,
                l + s.existence.lifted_pins,
            )
        })
}

/// `q :- b, !q` keeps an odd component. q's other support runs through the even
/// loop `s :- !t`, `t :- !s`, so no producer is redundant and pruning cannot remove
/// the loop. H (`h :- a, !a, q`) never holds, so every classification-existence
/// round uses the no-H fallback. With `q :- b, s, d` and `q :- b, s, !d` every input
/// has a model (choose s) and the pin on d is redundant; without the second, b true
/// and d false has no model.
fn unreachable_h(no_meaning: bool) -> (Corpus, Engine) {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let d = rel(&mut c, "d", true);
    let s = rel(&mut c, "s", false);
    let t = rel(&mut c, "t", false);
    let q = rel(&mut c, "q", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, s, &[(t, true)]);
    rule(&mut c, t, &[(s, true)]);
    rule(&mut c, q, &[(b, false), (q, true)]);
    rule(&mut c, q, &[(b, false), (s, false), (d, false)]);
    if !no_meaning {
        rule(&mut c, q, &[(b, false), (s, false), (d, true)]);
    }
    rule(&mut c, h, &[(a, false), (a, true), (q, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let e = prepare(&c, v, &Default::default());
    (c, e)
}

#[test]
fn no_hypothesis_fallback_cubes_are_lifted() {
    let (c, mut e) = unreachable_h(false);
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    // Pruning selects H-first coverage with its no-H fallback (the corpus path).
    let options = CheckOptions {
        prune: true,
        ..Default::default()
    };
    let got = e.check(&keys(&c), &options).unwrap();
    scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(!got.classification.as_ref().unwrap().no_meaning.exists());
    let (rounds, attempts, lifted) = phase_stats(&sizes, "completion classification existence");
    assert!(rounds > 0, "the odd component needs covers");
    assert!(attempts > 0, "no-H cubes are lifted");
    assert!(lifted > 0, "the pin on d is redundant");
    // Telemetry: every cube pins b (the loop's guard); the covered mass is positive.
    let search = sizes
        .snapshot()
        .searches
        .into_iter()
        .find(|s| s.phase == "completion classification existence" && s.existence.rounds > 0)
        .unwrap();
    let cover = search
        .existence
        .covers
        .iter()
        .find(|c| c.kind == "search")
        .unwrap();
    assert!(cover.coverage_estimate.unwrap() > 0.0);
    assert_eq!(
        cover.pinned.first().map(|(a, _)| a.clone()),
        Some(GroundAtom::new(
            c.relations().find(|r| r.name == "b").unwrap().id,
            [],
        ))
    );
}

#[test]
fn no_hypothesis_fallback_still_reports_no_meaning() {
    let (c, e) = unreachable_h(true);
    let expected = e.check_enumerated(&keys(&c), &Default::default()).unwrap();
    assert!(
        expected
            .classification
            .as_ref()
            .unwrap()
            .no_meaning
            .exists()
    );
    for options in [
        CheckOptions::default(),
        CheckOptions {
            prune: true,
            split_depth: 2,
            ..Default::default()
        },
    ] {
        scale::same_report(&e.check(&keys(&c), &options).unwrap(), &expected);
    }
}

/// The same odd loop with `h :- h, a, q`: inputs with a false have no H model, so
/// they go through the no-H fallback; but h = false is also a model wherever a
/// holds, so a no-H cube need not stay inside the no-H region. Crossing into inputs
/// that have H models is safe because every covered input still has a model.
/// Lifting never reads earlier exclusions: its solve activates only its own gate.
#[test]
fn no_hypothesis_cubes_may_cross_into_inputs_with_hypothesis_models() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let d = rel(&mut c, "d", true);
    let s = rel(&mut c, "s", false);
    let t = rel(&mut c, "t", false);
    let q = rel(&mut c, "q", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, s, &[(t, true)]);
    rule(&mut c, t, &[(s, true)]);
    rule(&mut c, q, &[(b, false), (q, true)]);
    rule(&mut c, q, &[(b, false), (s, false), (d, false)]);
    rule(&mut c, q, &[(b, false), (s, false), (d, true)]);
    rule(&mut c, h, &[(h, false), (a, false), (q, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let mut e = prepare(&c, v, &Default::default());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let options = CheckOptions {
        prune: true,
        ..Default::default()
    };
    let got = e.check(&keys(&c), &options).unwrap();
    scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(!got.classification.as_ref().unwrap().no_meaning.exists());
    let (rounds, attempts, _) = phase_stats(&sizes, "completion classification existence");
    assert!(rounds > 0 && attempts > 0);
}

/// `h :- h, p` lets every input choose H, so rejection must cover H models; `p :- a`
/// and `p :- !a` make the pin on a redundant.
#[test]
fn rejection_cover_cubes_are_lifted() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", true);
    let p = rel(&mut c, "p", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, p, &[(a, false)]);
    rule(&mut c, p, &[(a, true)]);
    rule(&mut c, h, &[(h, false), (p, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let mut e = prepare(&c, v, &Default::default());
    let sizes = crate::CompletionSizes::default();
    e.limits.completion_sizes = Some(sizes.clone());
    let got = e.check(&keys(&c), &Default::default()).unwrap();
    scale::same_report(
        &got,
        &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
    );
    assert!(matches!(
        got.classification.as_ref().unwrap().rejected,
        Search::None
    ));
    let (rounds, attempts, _) = phase_stats(&sizes, "completion rejection");
    assert!(rounds > 0);
    assert!(attempts > 0, "rejection's H-model cubes are lifted");
}
