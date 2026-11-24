use super::super::search_free;
use super::*;

fn cyclic(c: &Cone) -> bool {
    symbolic::has_cycle_for_test(c)
}
fn reduced(c: &Cone) -> Cone {
    search_free::reduce(c, &mut Budget::new(&Limits::default()))
        .unwrap()
        .cone
}

#[test]
fn fixed_producers_and_presence_implications_cut_all_views_without_sat_pruning() {
    for fixed in [false, true] {
        let mut c = Corpus::new();
        let value = rel(&mut c, "value", true);
        let present = rel(&mut c, "present", false);
        let selected = rel(&mut c, "selected", false);
        let body = if fixed { vec![] } else { vec![(value, false)] };
        rule(&mut c, present, &body);
        rule(&mut c, present, &[(selected, true)]);
        rule(&mut c, selected, &[(value, false), (present, false)]);
        for h in [None, Some(present)] {
            let v = verification(&mut c, h, &[]);
            let e = prepare(&c, v, &Domains::new());
            assert!(cyclic(&e.cone), "the control starts with a syntactic loop");
            for cone in std::iter::once(&e.cone).chain(e.classification.iter().map(|c| &c.0)) {
                for hypothesis in [false, true] {
                    let view = super::super::pruning::view(&e, cone, hypothesis, e.limits.timeout)
                        .unwrap();
                    assert!(!cyclic(&view));
                }
            }
            let sizes = crate::CompletionSizes::default();
            let mut e = e;
            e.limits.completion_sizes = Some(sizes.clone());
            let actual = e.check(&keys(&c), &Default::default()).unwrap();
            scale::same_report(
                &actual,
                &e.check_enumerated(&keys(&c), &Default::default()).unwrap(),
            );
            scale::same_report(&actual, &e.check(&keys(&c), &Default::default()).unwrap());
            scale::same_report(
                &actual,
                &prepare(&c, v, &Domains::new())
                    .check(&keys(&c), &Default::default())
                    .unwrap(),
            );
            for search in sizes.snapshot().searches {
                assert_eq!(search.existence.components, 0, "{}", search.phase);
            }
        }
    }
}

#[test]
fn dead_by_negation_edges_do_not_change_frozen_classification_membership() {
    let mut c = Corpus::new();
    let known = rel(&mut c, "known", false);
    let h = rel(&mut c, "h", false);
    let p = rel(&mut c, "p", false);
    rule(&mut c, known, &[]);
    rule(&mut c, h, &[]);
    rule(&mut c, h, &[(p, false), (known, true)]);
    rule(&mut c, p, &[(p, false)]);
    let v = verification(&mut c, Some(h), &[]);
    let r = super::pruning::compare(&c, v);
    assert!(
        r.classification.unwrap().ambiguous.exists(),
        "p stays in frozen C(H), even though h's reader is dead"
    );
}

#[test]
fn tiny_signed_equations_preserve_every_completion_model_after_reduction_and_pins() {
    let mut corpus = Corpus::new();
    let input = rel(&mut corpus, "input", true);
    let p = rel(&mut corpus, "p", false);
    let q = rel(&mut corpus, "q", false);
    rule(&mut corpus, p, &[(p, false)]);
    rule(&mut corpus, q, &[(q, false)]);
    let v = verification(&mut corpus, None, &[]);
    let e = prepare(&corpus, v, &Domains::new());
    let [i, p, q] = [input, p, q].map(|r| e.program.atom_index[&atom(r)]);
    let bodies = vec![
        vec![],
        vec![(i, true)],
        vec![(i, false)],
        vec![(p, true)],
        vec![(p, false)],
        vec![(q, true)],
        vec![(q, false)],
        vec![(i, true), (p, true)],
        vec![(i, true), (q, true)],
        vec![(i, false), (q, true)],
        vec![(p, true), (q, true)],
        vec![(p, false), (q, true)],
        vec![(p, true), (q, false)],
    ];
    fn models(c: &Cone) -> BTreeSet<usize> {
        (0..1usize << c.atoms.len())
            .filter(|bits| {
                let value = |i: usize| *bits & (1usize << i) != 0;
                (0..c.atoms.len()).all(|i| {
                    if let Some(v) = c.fixed[i] {
                        value(i) == v
                    } else if c.input[i] {
                        true
                    } else {
                        value(i)
                            == c.rules
                                .iter()
                                .filter(|r| r.head == i)
                                .any(|r| r.body.iter().all(|(a, p)| value(*a) == *p))
                    }
                })
            })
            .collect()
    }
    for a in &bodies {
        for b in &bodies {
            for d in &bodies {
                let mut c = (*e.cone).clone();
                c.fixed.fill(None);
                c.rules = [(p, a), (p, b), (q, d)]
                    .into_iter()
                    .map(|(head, body)| super::super::super::Rule {
                        head,
                        body: body.clone(),
                        ground: None,
                        source: None,
                    })
                    .collect::<Vec<_>>()
                    .into();
                for pin in [None, Some(false), Some(true)] {
                    c.fixed[i] = pin;
                    let after = reduced(&c);
                    assert_eq!(
                        models(&c),
                        models(&after),
                        "bodies {a:?}, {b:?}, {d:?}; pin {pin:?}"
                    );
                }
            }
        }
    }
}
