use super::super::pruning;
use super::*;

fn fixture(alias: bool, guarded: bool) -> (Corpus, VerificationId, RelationId, RelationId) {
    let mut c = Corpus::new();
    let value = rel(&mut c, "value", true);
    let gate = rel(&mut c, "gate", true);
    let present = rel(&mut c, "present", false);
    let selected = rel(&mut c, "selected", false);
    let helper = if alias {
        let a = rel(&mut c, "alias", false);
        rule(&mut c, a, &[(value, false)]);
        a
    } else {
        value
    };
    let mut body = vec![(helper, false)];
    if guarded {
        body.push((gate, false));
    }
    rule(&mut c, present, &body);
    rule(&mut c, present, &[(selected, true)]);
    rule(&mut c, selected, &[(value, false), (present, false)]);
    let h = rel(&mut c, "hypothesis", false);
    rule(&mut c, h, &[(gate, false)]);
    let v = verification(&mut c, guarded.then_some(h), &[]);
    (c, v, present, selected)
}

#[test]
fn presence_conjunct_cuts_a_spurious_odd_edge_by_both_paths() {
    for alias in [false, true] {
        let (c, v, present, selected) = fixture(alias, false);
        let report = super::pruning::compare(&c, v);
        assert!(
            report
                .pruning
                .records
                .iter()
                .any(|r| r.kind == PruningKind::ImpliedBodyLiteral
                    && r.head == atom(selected)
                    && r.literal == Some(atom(present))
                    && r.structural != alias)
        );
        let mut e = prepare(&c, v, &Domains::new());
        let head = e.program.atom_index[&atom(selected)];
        let literal = e.program.atom_index[&atom(present)];
        assert!(
            e.cone
                .rules
                .iter()
                .any(|r| r.head == head && r.body.contains(&(literal, true)))
        );
        e.pruning = Some(Arc::new(std::sync::Mutex::new(pruning::Cache::for_engine(
            &e,
        ))));
        let view = pruning::view(&e, &e.cone, false, e.limits.timeout).unwrap();
        assert!(
            !view
                .rules
                .iter()
                .any(|r| r.head == head && r.body.contains(&(literal, true)))
        );
        let before: Vec<_> = e
            .cone
            .rules
            .iter()
            .filter(|r| r.head == head)
            .map(|r| r.ground)
            .collect();
        let after: Vec<_> = view
            .rules
            .iter()
            .filter(|r| r.head == head)
            .map(|r| r.ground)
            .collect();
        assert_eq!(
            before, after,
            "shortening retains the selected producer and its source"
        );
    }
}

#[test]
fn implied_literal_proof_under_h_never_changes_the_w_view() {
    let (c, v, present, selected) = fixture(false, true);
    let report = super::pruning::compare(&c, v);
    let matching: Vec<_> = report
        .pruning
        .records
        .iter()
        .filter(|r| {
            r.kind == PruningKind::ImpliedBodyLiteral
                && r.head == atom(selected)
                && r.literal == Some(atom(present))
        })
        .collect();
    assert!(!matching.is_empty());
    assert!(
        matching
            .iter()
            .all(|r| r.context == PruningContext::Hypothesis && !r.structural)
    );
}

fn models(c: &Cone, h: Option<usize>) -> BTreeSet<usize> {
    (0..1usize << c.atoms.len())
        .filter(|bits| {
            let v = |i: usize| *bits & (1usize << i) != 0;
            h.is_none_or(v)
                && (0..c.atoms.len()).all(|i| {
                    if let Some(f) = c.fixed[i] {
                        v(i) == f
                    } else if c.input[i] {
                        true
                    } else {
                        v(i) == c
                            .rules
                            .iter()
                            .filter(|r| r.head == i)
                            .any(|r| r.body.iter().all(|(j, p)| v(*j) == *p))
                    }
                })
        })
        .collect()
}

#[test]
fn every_literal_shortening_prefix_preserves_all_completion_models() {
    let mut structural = false;
    let mut proved = false;
    // Vary both signed operands, including dependencies on the target equation,
    // positive self-support and contradictions. Compare every model, not only a verdict.
    for code in 0..64 {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", true);
        let b = rel(&mut c, "b", true);
        let x = rel(&mut c, "x", false);
        let l = rel(&mut c, "l", false);
        let atoms = [a, b, x, l];
        let left = code % 8;
        let right = code / 8;
        rule(&mut c, l, &[(atoms[left / 2], left % 2 != 0)]);
        rule(&mut c, l, &[(atoms[right / 2], right % 2 != 0)]);
        rule(&mut c, x, &[(a, false), (l, false)]);
        let v = verification(&mut c, Some(b), &[]);
        for h in [false, true] {
            for work in [100, 10000] {
                let mut e = prepare(&c, v, &Domains::new());
                e.limits.max_work = work;
                e.pruning = Some(Arc::new(std::sync::Mutex::new(pruning::Cache::for_engine(
                    &e,
                ))));
                let view = pruning::view(&e, &e.cone, h, e.limits.timeout).unwrap();
                let hypothesis = h.then_some(e.classification.as_ref().unwrap().2);
                assert_eq!(
                    models(&e.cone, hypothesis),
                    models(&view, hypothesis),
                    "code {code} H {h} work {work}"
                );
                for r in &e.pruning.as_ref().unwrap().lock().unwrap().report.records {
                    if r.kind == PruningKind::ImpliedBodyLiteral {
                        structural |= r.structural;
                        proved |= !r.structural;
                    }
                }
            }
        }
    }
    assert!(structural && proved);
}
