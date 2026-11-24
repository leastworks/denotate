use super::*;
use crate::sat_probe::completion_query::tests::{keys, prepare, verification};
use crate::test_support::rewrites::{atom, rel, rule};

#[test]
fn formula_trials_survive_a_full_inventory_of_higher_scoring_inputs() {
    let mut c = Corpus::new();
    for n in 0..70 {
        let i = rel(&mut c, &format!("input{n}"), true);
        for side in 0..2 {
            let p = rel(&mut c, &format!("loop{n}_{side}"), false);
            rule(&mut c, p, &[(i, false), (p, true)]);
        }
    }
    let a = rel(&mut c, "a", true);
    let b = rel(&mut c, "b", true);
    let f = rel(&mut c, "formula", false);
    rule(&mut c, f, &[(a, false), (b, true)]);
    rule(&mut c, f, &[(a, true), (b, false)]);
    let p = rel(&mut c, "formula_loop", false);
    rule(&mut c, p, &[(f, false), (p, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let mut budget = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut budget).unwrap();
    let mut rows = vec![];
    let mut omitted = 0;
    choose(
        &e,
        &root,
        false,
        true,
        8,
        &mut e.config.clone(),
        &mut rows,
        &mut omitted,
        &mut budget,
    )
    .unwrap();
    assert!(omitted > 0);
    let f = rows.iter().find(|r| r.split == atom(f)).unwrap();
    assert!(f.formula);
    assert_eq!(f.state, "verified");
    assert_eq!(f.child_trials.len(), 2);
    assert_eq!(
        f.child_trials
            .iter()
            .map(|c| c.cycles_cut)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    assert!(rows.iter().any(|r| !r.formula && r.state == "verified"));
    assert!(rows.iter().filter(|r| r.state != "not-shortlisted").count() <= 8);
}

#[test]
fn both_sides_of_a_one_sided_cut_rank_the_untouched_component() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let j = rel(&mut c, "j", true);
    let p = rel(&mut c, "p", false);
    let q = rel(&mut c, "q", false);
    rule(&mut c, p, &[(i, false), (p, true)]);
    rule(&mut c, q, &[(j, false), (q, true)]);
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &Default::default());
    let mut b = Budget::new(&e.limits);
    let root = fitting::Bundle::new(&e, &mut b).unwrap();
    let mut config = e.config.clone();
    let mut rows = vec![];
    let (choice, _) = choose(
        &e,
        &root,
        false,
        true,
        8,
        &mut config,
        &mut rows,
        &mut 0,
        &mut b,
    )
    .unwrap()
    .unwrap();
    let row = rows.iter().find(|r| r.selected).unwrap();
    assert_eq!(row.cycles_cut_every_child, 0);
    assert_eq!(
        row.child_trials
            .iter()
            .map(|c| c.cycles_cut)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    for n in 0..2 {
        let child = &choice.child_states[n];
        let (next, _) = ranking::choose_in(
            &e,
            child,
            false,
            true,
            8,
            Some(&choice.residual_only(n)),
            &mut config,
            &mut vec![],
            &mut 0,
            &mut b,
        )
        .unwrap()
        .unwrap();
        assert_ne!(next.selected, choice.selected);
    }
    let options = CheckOptions {
        split_depth: 3,
        ..Default::default()
    };
    let expected = e.check_enumerated(&keys(&c), &options).unwrap();
    for exists in [false, true] {
        let answer = test_partition(&e, false, exists, &options).unwrap();
        let want = if exists {
            expected.meaning.no_meaning.exists()
        } else {
            expected.meaning.ambiguous.exists()
        };
        assert_eq!(answer.exists(), want);
        assert!(matches!(answer, Search::None | Search::Exists(())));
    }
}

#[test]
fn breadth_first_units_serve_siblings_after_a_leaf_cutoff() {
    let mut c = Corpus::new();
    for n in 0..3 {
        let i = rel(&mut c, &format!("i{n}"), true);
        let p = rel(&mut c, &format!("p{n}"), false);
        rule(&mut c, p, &[(i, false), (p, true)]);
    }
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    let end = Instant::now() + e.limits.timeout;
    e.limits.run_deadline = Some(end);
    let report = Arc::new(std::sync::Mutex::new(BranchReport::default()));
    e.branches = Some(report.clone());
    let options = CheckOptions {
        split_depth: 3,
        ..Default::default()
    };
    let calls = std::cell::Cell::new(0);
    let answer = partition(&e, false, true, &options, 1, |branch, _| {
        assert!(branch.limits.run_deadline.unwrap() <= end);
        calls.set(calls.get() + 1);
        if calls.get() == 1 {
            Ok(Search::<()>::Inconclusive(inconclusive(
                CheckError::deadline("test sibling", Duration::ZERO),
            )?))
        } else {
            Ok(Search::None)
        }
    })
    .unwrap();
    assert!(matches!(answer, Search::Inconclusive(_)));
    assert!(calls.get() > 1, "a leaf cutoff must not skip its siblings");
    let report = report.lock().unwrap();
    assert!(
        report
            .records
            .windows(2)
            .all(|rs| rs[0].depth <= rs[1].depth)
    );
    assert!(report.records.iter().any(|r| r.depth >= 2));
}

#[test]
fn interrupted_uniqueness_discovery_does_not_refund_its_explicit_query_allowance() {
    let mut c = Corpus::new();
    for name in ["p", "q"] {
        let p = rel(&mut c, name, false);
        rule(&mut c, p, &[(p, false)]);
    }
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.config.max_solves = 1;
    let mut remaining = e.config.clone();
    let mut b = Budget::new(&e.limits);
    let state = fitting::Bundle::new(&e, &mut b).unwrap();
    let answer = choose(
        &e,
        &state,
        false,
        false,
        8,
        &mut remaining,
        &mut vec![],
        &mut 0,
        &mut b,
    );
    assert!(answer.is_err(), "two local questions cannot use one solve");
    assert_eq!(
        remaining.max_solves, 0,
        "residual checking cannot reuse the spent solve"
    );
}
