use crate::{
    limits::Budget,
    test_support::rewrites::{atom, compare, rel, rule, subsets, supported_models},
    *,
};
use denotate_ir::*;
use std::{cell::RefCell, collections::BTreeSet};

fn fixture(depth: usize) -> (Corpus, RelationId) {
    fixture_width(depth, 1)
}
fn fixture_width(depth: usize, width: usize) -> (Corpus, RelationId) {
    fn add(c: &mut Corpus, head: RelationId, body: &[(RelationId, bool)], width: usize) {
        let repeated = body
            .iter()
            .copied()
            .cycle()
            .take(body.len() * width)
            .collect::<Vec<_>>();
        rule(c, head, &repeated);
    }
    let mut c = Corpus::new();
    let kind = rel(&mut c, "kind", true);
    let ready = rel(&mut c, "ready", true);
    let priority = rel(&mut c, "priority", true);
    let booked = rel(&mut c, "booked", false);
    let fails = rel(&mut c, "fails", false);
    let claim = rel(&mut c, "claim", false);
    let inspected = rel(&mut c, "inspected", false);
    let held = rel(&mut c, "held", false);
    let cleared = rel(&mut c, "cleared", false);
    let mut next = cleared;
    for n in 0..depth {
        let link = rel(&mut c, &format!("link{n}"), false);
        add(&mut c, link, &[(next, false)], width);
        next = link;
    }
    add(&mut c, booked, &[(kind, false), (next, false)], width);
    add(&mut c, fails, &[(ready, false), (booked, true)], width);
    add(&mut c, claim, &[(kind, true), (fails, true)], width);
    add(&mut c, inspected, &[(kind, false)], width);
    add(&mut c, inspected, &[(claim, false)], width);
    add(
        &mut c,
        held,
        &[(priority, false), (inspected, false)],
        width,
    );
    add(&mut c, cleared, &[(ready, false), (held, true)], width);
    (c, claim)
}

fn sound(c: &Corpus, p: &GroundProgram) {
    compare(c, &Domains::new(), p);
    let before = p.original_rules().cloned().collect::<Vec<_>>();
    let after = p.rules().cloned().collect::<Vec<_>>();
    for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
        assert_eq!(
            supported_models(p, &before, &world),
            supported_models(p, &after, &world)
        );
    }
}

#[test]
fn guarded_settlement_cuts_the_cycle_and_preserves_every_world() {
    for depth in [0, 3] {
        let (c, claim) = fixture(depth);
        let limits = Limits::default();
        let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        assert!(!raw.is_admitted());
        let p = raw.clone().admit(&limits).unwrap();
        assert!(p.is_admitted(), "{:?}", p.admission_limit());
        assert!(p.rewrite_proofs().any(|p| p.guarded_settlement().is_some()));
        sound(&c, &p);
        let reference = raw
            .admit_without_negative_reuse(&mut Budget::new(&limits), None)
            .unwrap();
        super::unchanged_attempts::equal(&p, &reference);
        let replay = p.evaluate([], &limits).unwrap();
        assert!(replay.established_facts().any(|a| *a == atom(claim)));
        crate::findings::collect_evidence(
            &replay,
            &BTreeSet::from([atom(claim)]),
            &mut Budget::new(&limits),
        )
        .unwrap();
        let mut exercised = false;
        for world in subsets(&p.input_atoms().cloned().collect::<Vec<_>>()) {
            let replay = p.evaluate(world, &limits).unwrap();
            for fact in replay.established_facts() {
                if matches!(&replay.derivation(fact).unwrap().evidence,
                    Evidence::Derived { premises, .. } if premises.iter().any(|p| matches!(p, PremiseEvidence::Replaced { .. })))
                {
                    crate::findings::collect_evidence(
                        &replay,
                        &BTreeSet::from([fact.clone()]),
                        &mut Budget::new(&limits),
                    )
                    .unwrap();
                    exercised = true;
                }
            }
        }
        assert!(exercised);
    }
}

#[test]
fn guarded_settlement_does_not_unfold_unresolved_self_support() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(b, true)]);
    rule(&mut c, b, &[(a, true)]);
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits::default())
        .unwrap();
    assert!(!p.is_admitted());
    assert_eq!(p.rewrite_proofs().count(), 0);
    sound(&c, &p);
}

#[test]
fn guarded_settlement_randomized_and_constrained_runs_preserve_models() {
    let mut seed = 1234567u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for _ in 0..192 {
        let mut c = Corpus::new();
        let inputs = [rel(&mut c, "i", true), rel(&mut c, "j", true)];
        let derived = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "c", false),
        ];
        let all: Vec<_> = inputs.into_iter().chain(derived).collect();
        for _ in 0..(3 + random() % 6) {
            let head = derived[random() % derived.len()];
            let body: Vec<_> = (0..(1 + random() % 3))
                .map(|_| (all[random() % all.len()], random() % 2 == 0))
                .collect();
            rule(&mut c, head, &body);
        }
        let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let p = raw.admit(&Limits::default()).unwrap();
        sound(&c, &p);
    }
    let mut replacements = 0;
    for n in 0..24 {
        let (mut c, _) = fixture(0);
        let all: Vec<_> = c.relations().map(|r| r.id).collect();
        let derived: Vec<_> = c
            .relations()
            .filter(|r| r.role == RelationRole::Derived)
            .map(|r| r.id)
            .collect();
        if n % 4 != 0 {
            rule(
                &mut c,
                derived[random() % derived.len()],
                &[
                    (all[random() % all.len()], random() % 2 == 0),
                    (all[random() % all.len()], random() % 2 == 0),
                ],
            );
        }
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
            .unwrap()
            .admit(&Limits::default())
            .unwrap();
        replacements += p
            .rewrite_proofs()
            .filter(|p| p.guarded_settlement().is_some())
            .count();
        sound(&c, &p);
    }
    assert!(replacements > 0);
    let (c, _) = fixture(0);
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    for tasks in [0, 1, 2, 4, 8, 16, 64] {
        let limits = Limits {
            max_bdd_tasks: tasks,
            ..Limits::default()
        };
        sound(&c, &raw.clone().admit(&limits).unwrap());
    }
    let events = RefCell::new(Vec::new());
    let limits = Limits {
        max_work: 50,
        ..Limits::default()
    };
    let p = raw
        .admit_observed(
            &mut Budget::new(&limits),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    assert!(p.admission_limit().is_some());
    sound(&c, &p);
}

#[test]
fn guarded_settlement_invalidates_failed_cover_when_a_producer_becomes_exact() {
    let (mut c, claim) = fixture(0);
    let named = |name: &str| c.relations().find(|r| r.name == name).unwrap().id;
    let kind = named("kind");
    let ready = named("ready");
    let a = rel(&mut c, "external_a", false);
    let b = rel(&mut c, "external_b", false);
    let out = rel(&mut c, "out", false);
    rule(&mut c, a, &[(b, true)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, out, &[(claim, false)]);
    let redundant = rule(&mut c, out, &[(kind, true), (ready, true), (a, false)]);
    let limits = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let events = RefCell::new(Vec::new());
    let p = raw
        .clone()
        .admit_observed(
            &mut Budget::new(&limits),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    let reference = raw
        .admit_without_negative_reuse(&mut Budget::new(&limits), None)
        .unwrap();
    super::unchanged_attempts::equal(&p, &reference);
    assert!(
        p.rewrite_proofs()
            .any(|p| p.candidate().source == redundant)
    );
    assert!(events.borrow().iter().any(|e| {
        e.attempts
            .values()
            .any(|a| a.retry_causes.contains_key("guarded-replacement"))
    }));
    sound(&c, &p);
}

#[test]
fn guarded_settlement_expansion_cutoff_is_atomic_and_not_exhaustion() {
    let (c, _) = fixture_width(0, 1025);
    let limits = Limits {
        timeout: std::time::Duration::from_secs(120),
        ..Limits::default()
    };
    let raw = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
    let events = RefCell::new(Vec::new());
    let p = raw
        .clone()
        .admit_observed(
            &mut Budget::new(&limits),
            Some(&|e| events.borrow_mut().push(e.clone())),
        )
        .unwrap();
    assert!(p.admission_limit().is_none(), "{:?}", p.admission_limit());
    assert!(p.rewrite_proofs().all(|p| p.guarded_settlement().is_none()));
    assert_eq!(
        p.rules().collect::<Vec<_>>(),
        raw.rules().collect::<Vec<_>>()
    );
    assert!(
        events
            .borrow()
            .iter()
            .any(|e| e.attempts.values().any(|a| a.cutoffs > 0))
    );
    sound(&c, &p);
}

#[test]
fn guarded_expression_is_respected_by_observation_certification() {
    let mut c = Corpus::new();
    let input = rel(&mut c, "input", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let source = rule(&mut c, a, &[(b, true), (input, true)]);
    rule(&mut c, b, &[(a, true)]);
    let limits = Limits::default();
    let mut p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    // Exercise the executable representation without relying on an admission
    // pass choosing this particular occurrence. The original meaning is unchanged.
    let r = p.rules.iter_mut().find(|r| r.source == source).unwrap();
    let premise = r.body.pop().unwrap();
    r.replacements.push(SettledReplacement {
        occurrence: premise.term.occurrence,
        expression: std::sync::Arc::new(SettledExpression::Not(std::sync::Arc::new(
            SettledExpression::Atom(atom(input)),
        ))),
    });
    crate::graph::analyze(&mut p, &mut Budget::new(&limits)).unwrap();
    let CertificationOutcome::Certified(replay) =
        p.certify_observation([atom(input)], &limits).unwrap()
    else {
        panic!()
    };
    assert!(replay.facts.contains(&atom(b)));
    assert!(!replay.facts.contains(&atom(a)));
    assert!(
        replay
            .pruning
            .iter()
            .any(|p| matches!(p.reason, ObservationPruningReason::SettledExpression { .. }))
    );
    assert!(matches!(
        p.certify_observation([], &limits).unwrap(),
        CertificationOutcome::NotCertified
    ));
    sound(&c, &p);
}
