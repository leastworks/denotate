use super::rewrites::{atom, compare, rel, rule, subsets, supported_models};
use crate::{limits::Budget, *};
use denotate_ir::*;
use std::cell::RefCell;

fn sound(c: &Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &p.original_rules().cloned().collect::<Vec<_>>(), &world),
            supported_models(p, &p.rules().cloned().collect::<Vec<_>>(), &world),
        );
    }
}

// A <= all(inputs), because blocked >= any(!input). The exact producer
// independently covers that region; the two negations keep the raw SCC blocked.
fn cycle(c: &mut Corpus, name: &str, inputs: &[RelationId]) -> [RelationId; 3] {
    let a = rel(c, &format!("{name}_a"), false);
    let blocked = rel(c, &format!("{name}_blocked"), false);
    let kept = rel(c, &format!("{name}_kept"), false);
    rule(c, a, &[(blocked, true)]);
    rule(c, blocked, &[(kept, true)]);
    for i in inputs {
        rule(c, blocked, &[(*i, true)]);
    }
    rule(c, kept, &[(inputs[0], false)]);
    rule(c, kept, &[(a, false)]);
    [a, blocked, kept]
}

#[test]
fn bounds_never_use_recursive_self_support_as_cover() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "c", false);
    let candidate = rule(&mut c, a, &[(i, true), (b, true)]);
    rule(&mut c, a, &[(d, false)]);
    rule(&mut c, d, &[(a, false)]);
    rule(&mut c, b, &[(a, false), (i, false)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    assert!(p.rules().any(|r| r.source == candidate));
    assert!(
        !p.rewrite_proofs()
            .any(|p| p.candidate().source == candidate && p.kind == RewriteKind::RedundantProducer)
    );
    sound(&c, &p);
    let models = super::rewrites::stable_models(
        &p.atoms().cloned().collect::<Vec<_>>(),
        &p.input_atoms().cloned().collect(),
        &p.rules().cloned().collect::<Vec<_>>(),
        &Default::default(),
    );
    assert_eq!(
        models,
        std::collections::BTreeSet::from([std::collections::BTreeSet::from([atom(a), atom(d)])])
    );
}

#[test]
fn guaranteed_bounds_keep_positive_self_support_possible() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    let [a, _, kept] = cycle(&mut c, "cycle", &[i]);
    rule(&mut c, a, &[(a, false)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    sound(&c, &p);
    let models = supported_models(
        &p,
        &p.rules().cloned().collect::<Vec<_>>(),
        &Default::default(),
    );
    assert!(
        models
            .iter()
            .any(|m| m.contains(&atom(a)) && m.contains(&atom(kept)))
    );
    assert!(
        !p.rewrite_proofs()
            .any(|p| p.bound_removal().is_some() && p.candidate().head.atom == atom(kept))
    );
}

#[test]
fn random_small_bound_removals_preserve_stable_and_supported_models() {
    let mut seed = 0x5eed_u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut removals = 0;
    for _ in 0..256 {
        let mut c = Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let derived = cycle(&mut c, "cycle", &[i]);
        let all = [i, j, derived[0], derived[1], derived[2]];
        for _ in 0..next() % 5 {
            let head = derived[next() as usize % derived.len()];
            let body: Vec<_> = (0..1 + next() % 3)
                .map(|_| (all[next() as usize % all.len()], next() % 2 == 0))
                .collect();
            rule(&mut c, head, &body);
        }
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
            .unwrap()
            .admit(&Limits::default())
            .unwrap();
        removals += p
            .rewrite_proofs()
            .filter(|p| p.bound_removal().is_some())
            .count();
        sound(&c, &p);
    }
    assert!(
        removals > 0,
        "exercise the new pass, not just programs with no rewrites"
    );
}

#[test]
fn bound_attempt_exhaustion_is_local_and_keeps_independent_proofs() {
    let mut c = Corpus::new();
    let inputs: Vec<_> = (0..4)
        .map(|i| rel(&mut c, &format!("i{i}"), true))
        .collect();
    cycle(&mut c, "wide", &inputs);
    cycle(&mut c, "small", &inputs[..1]);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut skipped = std::collections::BTreeSet::new();
    for max_bdd_tasks in 0..32 {
        let limits = Limits {
            max_bdd_tasks,
            ..Limits::default()
        };
        let events = RefCell::new(Vec::new());
        let p = raw
            .clone()
            .admit_observed(
                &mut Budget::new(&limits),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        sound(&c, &p);
        if p.admission_limit().is_none() && p.rewrite_proofs().count() > 0 {
            skipped.extend(
                events
                    .borrow()
                    .iter()
                    .filter_map(|e| e.skipped.as_ref().map(|s| s.kind)),
            );
        }
    }
    assert!(
        skipped.contains(&AdmissionAttemptKind::GuaranteedBounds),
        "{skipped:?}"
    );
}

#[test]
fn cancellation_during_guaranteed_bounds_propagates() {
    let mut c = Corpus::new();
    let i = rel(&mut c, "i", true);
    cycle(&mut c, "cycle", &[i]);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let token = limits.cancellation.clone();
    let result = raw.admit_observed(
        &mut Budget::new(&limits),
        Some(&|e| {
            if e.stage == "guaranteed-bounds" {
                token.cancel();
            }
        }),
    );
    assert!(matches!(result, Err(CheckError::Cancelled)));
}
