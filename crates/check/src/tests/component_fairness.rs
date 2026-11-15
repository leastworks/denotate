use crate::{
    admission_progress::AdmissionReporter,
    admission_skips::Attempts,
    limits::Budget,
    test_support::rewrites::{atom, compare, rel, rule, summaries},
    *,
};
use denotate_ir::*;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

#[test]
fn component_order_respects_dependencies_before_size_or_declaration_order() {
    let mut c = Corpus::new();
    let a = rel(&mut c, "down_a", false);
    let b = rel(&mut c, "down_b", false);
    let u = rel(&mut c, "up_a", false);
    let v = rel(&mut c, "up_b", false);
    let w = rel(&mut c, "up_c", false);
    rule(&mut c, a, &[(b, true), (u, false)]);
    rule(&mut c, b, &[(a, true)]);
    rule(&mut c, u, &[(v, true)]);
    rule(&mut c, v, &[(w, false)]);
    rule(&mut c, w, &[(u, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let mut budget = Budget::new(&limits);
    let scope =
        crate::admission_scope::AdmissionScope::build(&p, AdmissionPhase::Relevant, &mut budget)
            .unwrap();
    let order = scope.ordered_targets(&p, &mut budget).unwrap();
    assert_eq!(order.len(), 2);
    assert_eq!(order[0].0, p.component_for(&atom(u)).unwrap().id);
    assert_eq!(order[1].0, p.component_for(&atom(a)).unwrap().id);
    assert!(
        p.component(order[0].0).unwrap().atoms.len() > p.component(order[1].0).unwrap().atoms.len()
    );
}

fn cycle(
    c: &mut Corpus,
    name: &str,
    width: usize,
    depth: usize,
    p: RelationId,
    q: RelationId,
    guard: RelationId,
) -> RelationId {
    let head = rel(c, name, false);
    rule(c, head, &[(p, false)]);
    rule(c, head, &[(q, false)]);
    for i in 0..width {
        let leaf = rel(c, &format!("{name}_leaf{i}"), false);
        rule(c, leaf, &[(head, true)]);
        rule(c, leaf, &[(q, false)]); // no single-producer unfolding shortcut
        let mut next = leaf;
        for j in 0..depth {
            let link = rel(c, &format!("{name}_link{i}_{j}"), false);
            rule(c, link, &[(next, false)]);
            next = link;
        }
        rule(c, head, &[(guard, false), (next, false)]);
    }
    head
}

fn fixture() -> (Corpus, RelationId, RelationId, RelationId) {
    let mut c = Corpus::new();
    let p = rel(&mut c, "p", true);
    let q = rel(&mut c, "q", true);
    let guard = rel(&mut c, "guard", false);
    rule(&mut c, guard, &[(p, false)]);
    rule(&mut c, guard, &[(q, false)]);
    // Declare the wide one first; independent components are ordered by size.
    let wide = cycle(&mut c, "wide", 5, 0, p, q, guard);
    let first = cycle(&mut c, "first", 1, 0, p, q, guard);
    let last = cycle(&mut c, "last", 1, 6, p, q, guard);
    (c, first, wide, last)
}

#[test]
fn component_storage_discards_pending_proofs_but_keeps_committed_and_later_work() {
    let (c, first, wide, last) = fixture();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
    let mut exercised = false;
    for cap in (100..1600).step_by(10) {
        let limits = Limits {
            max_condition_nodes: cap,
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
        let skip = events.borrow().iter().position(|e| {
            e.skipped.as_ref().is_some_and(|s| {
                s.kind == AdmissionAttemptKind::ComponentStorage && s.head == atom(wide)
            })
        });
        if skip.is_none() || p.admission_limit().is_some() {
            continue;
        }
        let proved = |r| {
            p.rewrite_proofs()
                .any(|p| p.candidate().head.atom.relation == r && p.symbolic().is_some())
        };
        if !proved(first) || !proved(last) {
            continue;
        }
        exercised = true;
        assert!(
            !proved(wide),
            "the failed component must not publish partial proof evidence"
        );
        assert!(p.component_for(&atom(first)).unwrap().blocked_by.is_empty());
        assert!(p.component_for(&atom(last)).unwrap().blocked_by.is_empty());
        let blocked = p.component_for(&atom(wide)).unwrap();
        assert!(blocked.cycle.is_some());
        assert!(
            p.admission_skips_for(blocked)
                .any(|s| s.kind == AdmissionAttemptKind::ComponentStorage)
        );
        let events = events.into_inner();
        let skip = skip.unwrap();
        assert!(events[..skip].iter().any(|e| e.stage == "committed"));
        assert!(events[skip + 1..].iter().any(|e| e.stage == "committed"));
        assert!(
            events
                .iter()
                .filter(|e| e
                    .skipped
                    .as_ref()
                    .is_some_and(|s| s.kind == AdmissionAttemptKind::ComponentStorage
                        && s.head == atom(wide)))
                .count()
                == 1,
            "unrelated commits must not retry unchanged component inputs"
        );
        break;
    }
    assert!(
        exercised,
        "exercise owned proof-storage pressure between two successful components"
    );
}

#[test]
fn recovery_releases_several_pending_proofs_and_never_refunds_work() {
    let (c, _, wide, last) = fixture();
    let l = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let meaning = p.symbolic(&l).unwrap();
    let summaries = summaries(&p, &meaning, &l);
    let mut producers = BTreeMap::<_, Vec<_>>::new();
    for s in summaries.values() {
        producers
            .entry(&s.rule.head.atom)
            .or_default()
            .push(s.rule.id);
    }
    let targets = summaries
        .values()
        .filter(|s| s.rule.head.atom == atom(wide) && !s.exact)
        .map(|s| s.rule.id)
        .collect::<BTreeSet<_>>();
    let prefix = targets.iter().take(3).copied().collect::<BTreeSet<_>>();
    let reporter = AdmissionReporter::new(None);
    let baseline = meaning.metrics().retained_condition_nodes
        + summaries.values().map(|s| s.nodes()).sum::<usize>();
    let mut partial_nodes = baseline;
    let proofs = p
        .producer_removals(
            &summaries,
            &prefix,
            &producers,
            meaning.context(),
            &mut partial_nodes,
            &mut Budget::new(&l),
            &reporter,
            &mut Attempts::default(),
        )
        .unwrap();
    assert_eq!(proofs.len(), 3, "fixture needs several real pending proofs");
    drop(proofs);
    // Enough for that prefix and its live coverage, but not all five proofs.
    let coverage_nodes = summaries[targets.first().unwrap()].condition.node_count();
    let limits = Limits {
        max_condition_nodes: partial_nodes + coverage_nodes,
        ..l
    };
    let mut attempts = Attempts::default();
    let mut budget = Budget::new(&limits);
    let mut retained = baseline;
    let before_work = budget.used();
    let result = attempts
        .component_pass(
            &atom(wide),
            &p,
            &mut retained,
            &mut budget,
            &reporter,
            |attempts, retained, budget| {
                let result = p.producer_removals(
                    &summaries,
                    &targets,
                    &producers,
                    meaning.context(),
                    retained,
                    budget,
                    &reporter,
                    attempts,
                );
                assert!(
                    *retained >= partial_nodes,
                    "the failing pass had already retained the successful prefix"
                );
                result
            },
        )
        .unwrap();
    assert!(result.is_none());
    assert_eq!(retained, baseline, "only owned storage is restored");
    assert!(budget.used() > before_work, "spent work is never refunded");
    let later = summaries
        .values()
        .filter(|s| s.rule.head.atom == atom(last) && !s.exact)
        .map(|s| s.rule.id)
        .collect();
    let proofs = attempts
        .component_pass(
            &atom(last),
            &p,
            &mut retained,
            &mut budget,
            &reporter,
            |attempts, retained, budget| {
                p.producer_removals(
                    &summaries,
                    &later,
                    &producers,
                    meaning.context(),
                    retained,
                    budget,
                    &reporter,
                    attempts,
                )
            },
        )
        .unwrap()
        .unwrap();
    assert_eq!(proofs.len(), 1);
}

#[test]
fn removing_own_cycle_is_distinct_from_settling_its_upstream_dependencies() {
    for keeps_upstream in [false, true] {
        let mut c = Corpus::new();
        let p = rel(&mut c, "p", true);
        let q = rel(&mut c, "q", true);
        let guard = rel(&mut c, "guard", false);
        rule(&mut c, guard, &[(p, false)]);
        rule(&mut c, guard, &[(q, false)]);
        let u = rel(&mut c, "u", false);
        let v = rel(&mut c, "v", false);
        rule(&mut c, u, &[(v, true)]);
        rule(&mut c, v, &[(u, true)]);
        let h = cycle(&mut c, "consumer", 1, 0, p, q, guard);
        if keeps_upstream {
            rule(&mut c, h, &[(u, false)]);
        } else {
            let leaf = c
                .relations()
                .find(|r| r.name == "consumer_leaf0")
                .unwrap()
                .id;
            rule(&mut c, leaf, &[(u, false)]);
        }
        let limits = Limits::default();
        let events = RefCell::new(Vec::new());
        let checked = GroundProgram::prepare(&c, &Domains::new(), &limits)
            .unwrap()
            .admit_observed(
                &mut Budget::new(&limits),
                Some(&|e| events.borrow_mut().push(e.clone())),
            )
            .unwrap();
        let own = checked.component_for(&atom(h)).unwrap();
        assert!(own.cycle.is_none());
        assert_eq!(own.blocked_by.is_empty(), !keeps_upstream);
        assert!(checked.admission_limit().is_none());
        compare(&c, &Domains::new(), &checked);
        let end = events.into_inner().pop().unwrap();
        assert_eq!(end.unresolved_components, 1);
        assert_eq!(
            end.blocked_atoms,
            checked
                .components()
                .filter(|c| !c.blocked_by.is_empty())
                .map(|c| c.atoms.len())
                .sum::<usize>()
        );
    }
}

#[test]
fn shared_preparation_storage_is_still_global() {
    let (c, _, _, _) = fixture();
    let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default())
        .unwrap()
        .admit(&Limits {
            max_condition_nodes: 0,
            ..Limits::default()
        })
        .unwrap();
    assert!(p.admission_limit().is_some());
    assert!(p.admission_skips().next().is_none());
}

#[test]
fn guarded_proofs_commit_before_work_moves_to_another_component() {
    let mut c = Corpus::new();
    let mut claims = Vec::new();
    for prefix in ["left", "right"] {
        let kind = rel(&mut c, &format!("{prefix}_kind"), true);
        let ready = rel(&mut c, &format!("{prefix}_ready"), true);
        let priority = rel(&mut c, &format!("{prefix}_priority"), true);
        let booked = rel(&mut c, &format!("{prefix}_booked"), false);
        let fails = rel(&mut c, &format!("{prefix}_fails"), false);
        let claim = rel(&mut c, &format!("{prefix}_claim"), false);
        let inspected = rel(&mut c, &format!("{prefix}_inspected"), false);
        let held = rel(&mut c, &format!("{prefix}_held"), false);
        let cleared = rel(&mut c, &format!("{prefix}_cleared"), false);
        rule(&mut c, booked, &[(kind, false), (cleared, false)]);
        rule(&mut c, fails, &[(ready, false), (booked, true)]);
        rule(&mut c, claim, &[(kind, true), (fails, true)]);
        rule(&mut c, inspected, &[(kind, false)]);
        rule(&mut c, inspected, &[(claim, false)]);
        rule(&mut c, held, &[(priority, false), (inspected, false)]);
        rule(&mut c, cleared, &[(ready, false), (held, true)]);
        claims.push(claim);
    }
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let checked = raw.clone().admit(&l).unwrap();
    assert!(checked.is_admitted());
    let mut snapshots = BTreeMap::new();
    for proof in checked
        .rewrite_proofs()
        .filter(|p| p.guarded_settlement().is_some())
    {
        let original = raw.component_for(&proof.candidate().head.atom).unwrap().id;
        snapshots.insert(original, proof.snapshot);
    }
    assert_eq!(snapshots.len(), claims.len());
    assert_eq!(
        snapshots.values().collect::<BTreeSet<_>>().len(),
        claims.len(),
        "a guarded batch cannot span components"
    );
}

#[test]
fn guarded_turns_are_upstream_first_and_a_stuck_provider_does_not_starve_readers() {
    use crate::guarded_settlement::BOUNDS_PER_TURN;
    let mut c = Corpus::new();
    let flag = rel(&mut c, "flag", true);
    // Declare the smaller consumer first; its guard also gives it a cheaper
    // old global rank. The dependency order must take priority over both.
    let down = (0..6)
        .map(|i| rel(&mut c, &format!("down{i}"), false))
        .collect::<Vec<_>>();
    let up = (0..8)
        .map(|i| rel(&mut c, &format!("up{i}"), false))
        .collect::<Vec<_>>();
    for i in 0..up.len() {
        rule(&mut c, up[i], &[(up[(i + 1) % up.len()], true)]);
    }
    for i in 0..down.len() {
        let mut body = vec![(down[(i + 1) % down.len()], true)];
        if i == 0 {
            body.extend([(flag, false), (up[0], false)]);
        }
        rule(&mut c, down[i], &body);
    }
    let l = Limits::default();
    let raw = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
    let meaning = raw.symbolic(&l).unwrap();
    let summaries = summaries(&raw, &meaning, &l);
    let events = RefCell::new(Vec::new());
    let observe = |e: &AdmissionProgress| events.borrow_mut().push(e.clone());
    let reporter = AdmissionReporter::new(Some(&observe));
    let mut attempts = Attempts::default();
    let mut retained = 0;
    let proofs = raw
        .guarded_settlements(
            &meaning,
            &summaries,
            &summaries.keys().copied().collect(),
            &mut retained,
            &mut Budget::new(&l),
            &reporter,
            &mut attempts,
        )
        .unwrap();
    assert!(proofs.is_empty(), "the fixture is genuinely unresolved");
    assert_eq!(
        retained,
        attempts.nodes(),
        "waiting ranks and temporary bounds are released"
    );
    let order = events
        .borrow()
        .iter()
        .filter_map(|e| e.guarded.as_ref())
        .filter_map(|g| g.position.map(|position| (position, g.head.clone())))
        .collect::<BTreeMap<_, _>>()
        .into_values()
        .collect::<Vec<_>>();
    assert_eq!(order.len(), up.len() + down.len());
    let is_up = |a: &GroundAtom| up.contains(&a.relation);
    assert!(order[..BOUNDS_PER_TURN].iter().all(is_up));
    assert!(
        order[BOUNDS_PER_TURN..2 * BOUNDS_PER_TURN]
            .iter()
            .all(|a| !is_up(a))
    );
    assert!(
        order[2 * BOUNDS_PER_TURN..3 * BOUNDS_PER_TURN]
            .iter()
            .all(is_up),
        "the provider resumes from its waiting candidates on the next turn"
    );
    assert!(order.iter().any(|a| a.relation == down[0]));
}
