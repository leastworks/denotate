//! Controlled-observation probe: this follows the H-coverage encode/replay/cube/
//! lift path directly, even when an acyclic program needs no existence search.
use super::*;
use crate::sat_probe::completion_query::tests::{keys, prepare, verification};
use crate::test_support::rewrites::{atom, rel, rule};
use denotate_ir::{Corpus, Literal, Namespace, Parameter, RelationRole, Term};

#[derive(Clone, Copy, Debug)]
enum Form {
    Redundant,
    Removed,
    RetainedScope,
}
fn emit(c: &mut Corpus, head: &GroundAtom, body: &[(&GroundAtom, bool)]) {
    let head = c
        .atom(
            head.relation,
            head.arguments.iter().copied().map(Term::Constant),
        )
        .unwrap();
    let body: Vec<_> = body
        .iter()
        .map(|(a, p)| {
            let a = c
                .atom(a.relation, a.arguments.iter().copied().map(Term::Constant))
                .unwrap();
            if *p {
                Literal::Positive(a)
            } else {
                Literal::Negative(a)
            }
        })
        .collect();
    c.add_rule(head, body).unwrap();
}
struct Fixture {
    engine: Engine,
    observation: Observation,
    // Stable fixture order: readable, then received/written for each value.
    inputs: Vec<GroundAtom>,
    presence: GroundAtom,
    matched: GroundAtom,
    scalar: bool,
    keys: denotate_ir::SemanticKeys,
}
fn fixture(n: usize, form: Form, scalar: bool) -> Fixture {
    fixture_with_h(n, form, scalar, false)
}
fn fixture_with_h(n: usize, form: Form, scalar: bool, absent: bool) -> Fixture {
    fixture_full(n, form, scalar, absent, false)
}
fn fixture_full(n: usize, form: Form, scalar: bool, absent: bool, cycle: bool) -> Fixture {
    let mut c = Corpus::new();
    let es = c.declare_sort("Element").unwrap();
    let item = c.declare_constant("item", es).unwrap();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = (0..n)
        .map(|i| c.declare_constant(format!("v{i}"), vs).unwrap())
        .collect();
    let mut relation = |name, input, params| {
        c.declare_relation(
            name,
            if input {
                RelationRole::Input
            } else {
                RelationRole::Derived
            },
            params,
        )
        .unwrap()
    };
    let received = relation(
        "received",
        true,
        vec![Parameter::new("element", es), Parameter::new("value", vs)],
    );
    let written = relation(
        "written",
        true,
        vec![Parameter::new("element", es), Parameter::new("value", vs)],
    );
    let readable = relation("readable", true, vec![Parameter::new("element", es)]);
    let value = relation(
        "value",
        false,
        vec![Parameter::new("element", es), Parameter::new("value", vs)],
    );
    let presence = relation("present", false, vec![Parameter::new("element", es)]);
    let presence = GroundAtom::new(presence, [item]);
    let readable = GroundAtom::new(readable, [item]);
    for v in &values {
        let target = GroundAtom::new(value, [item, *v]);
        emit(
            &mut c,
            &target,
            &[
                (&GroundAtom::new(received, [item, *v]), true),
                (&readable, true),
            ],
        );
        emit(
            &mut c,
            &target,
            &[(&GroundAtom::new(written, [item, *v]), true)],
        );
        emit(&mut c, &presence, &[(&target, true)]);
    }
    let matched = rel(&mut c, "matched", false);
    let selected = GroundAtom::new(value, [item, values[0]]);
    let mut body = vec![(&selected, true)];
    if matches!(form, Form::Redundant) {
        body.insert(0, (&presence, true));
    }
    emit(&mut c, &atom(matched), &body);
    let h = rel(&mut c, "accepted", false);
    if cycle {
        let risk = rel(&mut c, "risk", true);
        let conflict = rel(&mut c, "conflict", false);
        rule(&mut c, conflict, &[(risk, false), (conflict, true)]);
        rule(&mut c, h, &[(matched, absent), (conflict, true)]);
    } else {
        rule(&mut c, h, &[(matched, absent)]);
    }
    if matches!(form, Form::RetainedScope) {
        let always = rel(&mut c, "always", false);
        rule(&mut c, always, &[]);
        emit(
            &mut c,
            &atom(h),
            &[(&presence, true), (&atom(always), false)],
        );
    }
    let assumptions = if scalar {
        vec![
            c.assume_in(
                Namespace::default(),
                "scalar",
                denotate_ir::Cardinality::AtMostOne,
                value,
                ["element".into()],
            )
            .unwrap(),
        ]
    } else {
        vec![]
    };
    let v = verification(&mut c, Some(h), &assumptions);
    let engine = prepare(&c, v, &[(es, vec![item]), (vs, values.clone())].into());
    let mut present = BTreeSet::from([readable.clone()]);
    if !absent {
        present.insert(GroundAtom::new(received, [item, values[0]]));
    }
    let absent = engine
        .cone
        .atoms
        .iter()
        .enumerate()
        .filter(|(i, a)| engine.cone.input[*i] && !present.contains(*a))
        .map(|(_, a)| a.clone())
        .collect();
    Fixture {
        engine,
        observation: Observation { present, absent },
        inputs: std::iter::once(readable)
            .chain(values.iter().flat_map(|v| {
                [
                    GroundAtom::new(received, [item, *v]),
                    GroundAtom::new(written, [item, *v]),
                ]
            }))
            .collect(),
        presence,
        matched: atom(matched),
        scalar,
        keys: keys(&c),
    }
}
#[derive(Debug)]
struct Probe {
    before: BTreeSet<(crate::AtomKey, bool)>,
    after: BTreeSet<(crate::AtomKey, bool)>,
    scope_heads: usize,
    attempts: usize,
    cnf: (usize, usize),
}
fn probe(f: &Fixture, pruning: bool, cached: bool) -> Probe {
    probe_mode(f, pruning, cached, false)
}
fn probe_mode(f: &Fixture, pruning: bool, cached: bool, projected: bool) -> Probe {
    let mut e = f.engine.clone();
    if pruning {
        e.pruning = Some(Arc::new(std::sync::Mutex::new(pruning::Cache::for_engine(
            &e,
        ))));
    }
    let original = &e.classification.as_ref().unwrap().0;
    let h = e.classification.as_ref().unwrap().2;
    let p = e.program.atom_index[&f.presence];
    let m = e.program.atom_index[&f.matched];
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    if cached {
        let _ = s.simplified(original, true).unwrap();
    }
    let world_view = s.simplified(original, false).unwrap();
    let view = s.simplified(original, true).unwrap();
    for v in [&world_view, &view] {
        assert!(
            v.rules
                .iter()
                .filter(|r| r.head == m)
                .all(|r| !r.body.contains(&(p, true))),
            "presence literal was not removed"
        );
    }
    let scope_heads = view
        .rules
        .iter()
        .map(|r| r.head)
        .filter(|i| view.fixed[*i].is_none())
        .collect::<BTreeSet<_>>()
        .len();
    let slice =
        projected.then(|| existence_slice::Slice::new(&view, Some(h), s.run.budget).unwrap());
    let view = slice.as_ref().map_or(&*view, |v| &v.core);
    let before_cnf = (s.run.cnf.solver.num_vars() as usize, s.run.cnf.clauses);
    let accepted = s.encode_view(view, original, true).unwrap();
    let cnf = (
        s.run.cnf.solver.num_vars() as usize - before_cnf.0,
        s.run.cnf.clauses - before_cnf.1,
    );
    let pins = s.pins(&f.observation).unwrap();
    assert!(s.solve(&[accepted.gate], &pins).unwrap());
    // Original-equation replay is retained, exactly as in H coverage.
    let values = if let Some(slice) = &slice {
        s.existence_values(slice, original, &accepted).unwrap()
    } else {
        s.values(original, &accepted).unwrap()
    };
    let mut cube = cover(&view, &values, Some(h), s.run.budget).unwrap();
    let atoms = |cube: &Cube| {
        cube.iter()
            .map(|(i, v)| {
                (
                    crate::AtomKey::from_atom(&f.keys, &view.atoms[*i]).unwrap(),
                    *v,
                )
            })
            .collect()
    };
    let before = atoms(&cube);
    existence::lift(&view, &values, &accepted, &mut cube, &mut s).unwrap();
    Probe {
        before,
        after: atoms(&cube),
        scope_heads,
        attempts: s.stats.lifting_attempts,
        cnf,
    }
}
#[test]
fn redundant_presence_lifting_depends_on_frozen_scope_not_a_missing_reduction() {
    for n in [3, 297] {
        for scalar in [false, true] {
            let full = fixture(n, Form::Redundant, scalar);
            let removed = fixture(n, Form::Removed, scalar);
            let retained = fixture(n, Form::RetainedScope, scalar);
            for pruning in [false, true] {
                let a = probe(&full, pruning, false);
                let b = probe(&removed, pruning, false);
                let c = probe(&retained, pruning, false);
                let cached = probe(&full, pruning, true);
                assert_eq!(
                    a.after, c.after,
                    "same original scope, same generalized observation"
                );
                assert_eq!(
                    a.after, cached.after,
                    "cached view must preserve reduction and cube"
                );
                assert!(
                    a.scope_heads > b.scope_heads,
                    "authored rewrite changes classification scope"
                );
                if !scalar {
                    assert!(a.after.len() > b.after.len());
                    assert!(b.after.is_subset(&a.after));
                }
                eprintln!(
                    "values={n} scalar={} pruning={pruning}: redundant heads={} cube={}->{} ({} attempts); removed heads={} cube={}->{} ({} attempts); retained-scope cube={}->{}",
                    full.scalar,
                    a.scope_heads,
                    a.before.len(),
                    a.after.len(),
                    a.attempts,
                    b.scope_heads,
                    b.before.len(),
                    b.after.len(),
                    b.attempts,
                    c.before.len(),
                    c.after.len()
                );
                eprintln!("raw model CNF: full {:?}; removed {:?}", a.cnf, b.cnf);
            }
        }
    }
}

// Independent acyclic equation oracle. The smaller source scope changes the
// lifting task, but not acceptance or processing in this particular fixture.
#[test]
fn presence_source_rewrite_preserves_outcomes_over_every_small_input_world() {
    for scalar in [false, true] {
        for form in [Form::Redundant, Form::Removed, Form::RetainedScope] {
            let f = fixture(3, form, scalar);
            for bits in 0..1usize << f.inputs.len() {
                let on = |i: usize| bits & (1usize << i) != 0;
                let values: Vec<_> = (0..3)
                    .map(|v| (on(0) && on(1 + 2 * v)) || on(2 + 2 * v))
                    .collect();
                let present = f
                    .inputs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| on(*i))
                    .map(|(_, a)| a.clone());
                let actual = f.engine.observation(present).unwrap();
                let valid = if scalar && values.iter().filter(|v| **v).count() > 1 {
                    matches!(actual, ObservationOutcome::NotPermitted)
                } else if values[0] {
                    matches!(
                        actual,
                        ObservationOutcome::Accepted {
                            processing: Interpretations::Unique(_),
                            ..
                        }
                    )
                } else {
                    matches!(actual, ObservationOutcome::Rejected { .. })
                };
                assert!(valid, "{form:?} scalar={scalar} inputs={bits}: {actual:?}");
            }
        }
    }
}

#[test]
fn absent_presence_keeps_all_value_blockers_in_the_frozen_scope() {
    for n in [3, 297] {
        let full = fixture_with_h(n, Form::Redundant, false, true);
        let removed = fixture_with_h(n, Form::Removed, false, true);
        for pruning in [false, true] {
            let a = probe(&full, pruning, false);
            let b = probe(&removed, pruning, false);
            assert!(b.after.is_subset(&a.after));
            assert!(a.after.len() > b.after.len());
            eprintln!(
                "absent values={n} pruning={pruning}: full {}->{}; removed {}->{}",
                a.before.len(),
                a.after.len(),
                b.before.len(),
                b.after.len()
            );
        }
    }
}

#[test]
fn existential_slice_matches_source_rewrite_for_present_and_absent_values() {
    for n in [3, 297] {
        for absent in [false, true] {
            for scalar in [false, true] {
                let full = fixture_with_h(n, Form::Redundant, scalar, absent);
                let removed = fixture_with_h(n, Form::Removed, scalar, absent);
                let retained = fixture_with_h(n, Form::RetainedScope, scalar, absent);
                for pruning in [false, true] {
                    let a = probe_mode(&full, pruning, false, true);
                    let b = probe_mode(&removed, pruning, false, true);
                    let c = probe_mode(&retained, pruning, false, true);
                    let cached = probe_mode(&full, pruning, true, true);
                    assert_eq!(
                        a.before, b.before,
                        "same relevant equations, same initial cube"
                    );
                    assert_eq!(a.after, b.after);
                    assert_eq!(
                        a.after, c.after,
                        "original scope is reconstructed, not discarded"
                    );
                    assert_eq!(a.after, cached.after);
                    eprintln!(
                        "projected values={n} absent={absent} scalar={scalar} pruning={pruning}: full {}->{} cnf={:?}; removed {}->{} cnf={:?}",
                        a.before.len(),
                        a.after.len(),
                        a.cnf,
                        b.before.len(),
                        b.after.len(),
                        b.cnf
                    );
                }
            }
        }
    }
}

#[test]
fn cyclic_existence_search_preserves_no_meaning_and_source_rewrite_results() {
    use crate::sat_probe::completion_query::tests::scale::same_report;
    for absent in [false, true] {
        let a = fixture_full(3, Form::Redundant, false, absent, true);
        let b = fixture_full(3, Form::Removed, false, absent, true);
        let expected = a
            .engine
            .check_enumerated(&a.keys, &Default::default())
            .unwrap();
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
                ..Default::default()
            },
        ] {
            let actual = a.engine.check(&a.keys, &options).unwrap();
            same_report(&actual, &expected);
            same_report(&actual, &a.engine.check(&a.keys, &options).unwrap());
            same_report(&actual, &b.engine.check(&b.keys, &options).unwrap());
        }
    }
}

/// Pair questions: a positive loop makes `matched` ambiguous, so the pair query
/// encodes both copies. Presence and every other value are acyclic and read by
/// no decision, cycle or H, so the sliced pair must not grow with n.
fn pair_fixture(n: usize, form: Form, decided: bool) -> (Engine, denotate_ir::SemanticKeys) {
    let mut c = Corpus::new();
    let es = c.declare_sort("Element").unwrap();
    let item = c.declare_constant("item", es).unwrap();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = (0..n)
        .map(|i| c.declare_constant(format!("v{i}"), vs).unwrap())
        .collect();
    let params = |c: &mut Corpus, name: &str, input: bool, element_only: bool| {
        let mut p = vec![Parameter::new("element", es)];
        if !element_only {
            p.push(Parameter::new("value", vs));
        }
        c.declare_relation(
            name,
            if input {
                RelationRole::Input
            } else {
                RelationRole::Derived
            },
            p,
        )
        .unwrap()
    };
    let received = params(&mut c, "received", true, false);
    let written = params(&mut c, "written", true, false);
    let readable = params(&mut c, "readable", true, true);
    let value = params(&mut c, "value", false, false);
    let presence = params(&mut c, "present", false, true);
    let presence = GroundAtom::new(presence, [item]);
    let readable = GroundAtom::new(readable, [item]);
    for v in &values {
        let target = GroundAtom::new(value, [item, *v]);
        emit(
            &mut c,
            &target,
            &[
                (&GroundAtom::new(received, [item, *v]), true),
                (&readable, true),
            ],
        );
        emit(
            &mut c,
            &target,
            &[(&GroundAtom::new(written, [item, *v]), true)],
        );
        emit(&mut c, &presence, &[(&target, true)]);
    }
    let free = rel(&mut c, "free", true);
    let looped = rel(&mut c, "looped", false);
    rule(&mut c, looped, &[(looped, false), (free, false)]);
    let matched = rel(&mut c, "matched", false);
    let selected = GroundAtom::new(value, [item, values[0]]);
    let looped = atom(looped);
    let mut body = vec![(&selected, true), (&looped, true)];
    if matches!(form, Form::Redundant) {
        body.insert(0, (&presence, true));
    }
    emit(&mut c, &atom(matched), &body);
    let v = c
        .verification_with_options_in(
            Namespace::new(["test"]).unwrap(),
            "pair",
            [],
            [],
            [],
            denotate_ir::VerificationOptions {
                semantics: denotate_ir::Semantics::Completion,
                hypothesis: None,
                decisions: decided.then(|| BTreeSet::from([matched])),
            },
        )
        .unwrap();
    let engine = prepare(&c, v, &[(es, vec![item]), (vs, values)].into());
    (engine, keys(&c))
}

fn pair_cnf(e: &Engine) -> ((usize, usize), bool) {
    let original = e.cone.clone();
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(e, &mut budget).unwrap();
    let view = s.simplified(&original, true).unwrap();
    let before = (s.run.cnf.solver.num_vars() as usize, s.run.cnf.clauses);
    let pair = determinacy::search(
        e,
        &view,
        view.label(),
        &original,
        None,
        ModelScope::WholeProgram,
        false,
        true,
        &CheckOptions::default(),
        &mut s,
    )
    .unwrap();
    (
        (
            s.run.cnf.solver.num_vars() as usize - before.0,
            s.run.cnf.clauses - before.1,
        ),
        pair.is_some(),
    )
}

#[test]
fn pair_slice_does_not_grow_with_unread_acyclic_values() {
    let mut sizes = BTreeSet::new();
    for n in [3, 297] {
        for form in [Form::Redundant, Form::Removed] {
            let (e, _) = pair_fixture(n, form, true);
            let (cnf, found) = pair_cnf(&e);
            assert!(found, "{n} {form:?}: the loop makes matched ambiguous");
            sizes.insert(cnf);
        }
    }
    assert_eq!(
        sizes.len(),
        1,
        "pair CNF depends on unread values: {sizes:?}"
    );
}

#[test]
fn sliced_pairs_agree_with_enumeration() {
    use crate::sat_probe::completion_query::tests::scale::same_report;
    for decided in [true, false] {
        for form in [Form::Redundant, Form::Removed] {
            let (e, keys) = pair_fixture(3, form, decided);
            let expected = e.check_enumerated(&keys, &Default::default()).unwrap();
            assert!(expected.meaning.ambiguous.exists());
            for options in [
                CheckOptions::default(),
                CheckOptions {
                    prune: true,
                    ..Default::default()
                },
            ] {
                let actual = e.check(&keys, &options).unwrap();
                same_report(&actual, &expected);
            }
        }
    }
}

#[test]
fn lifting_retires_its_gate_so_assumptions_do_not_accumulate() {
    // The 297-value presence fixture's H-coverage cube, lifted repeatedly with
    // retirement: the gate list does not grow, every lift gives the same cube, and
    // the CNF counters keep counting what the solver still stores (batsat 0.6 does
    // not remove satisfied original clauses).
    let f = fixture(297, Form::Redundant, false);
    let mut e = f.engine.clone();
    e.limits.completion_retire_lift_gates = true;
    let original = &e.classification.as_ref().unwrap().0;
    let h = e.classification.as_ref().unwrap().2;
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    let view = s.simplified(original, true).unwrap();
    let slice = existence_slice::Slice::new(&view, Some(h), s.run.budget).unwrap();
    let accepted = s.encode_view(&slice.core, original, true).unwrap();
    let pins = s.pins(&f.observation).unwrap();
    assert!(s.solve(&[accepted.gate], &pins).unwrap());
    let values = s.existence_values(&slice, original, &accepted).unwrap();
    let cube = cover(&slice.core, &values, Some(h), s.run.budget).unwrap();
    let mut first = None;
    for _ in 0..3 {
        let gates = s.gates.len();
        let counted = s.run.cnf.clauses;
        let stored = s.run.cnf.solver.num_clauses();
        let mut lifted = cube.clone();
        existence::lift(&slice.core, &values, &accepted, &mut lifted, &mut s).unwrap();
        assert_eq!(s.gates.len(), gates, "a retired gate is no longer assumed");
        let counted = s.run.cnf.clauses - counted;
        let stored = (s.run.cnf.solver.num_clauses() - stored) as usize;
        assert!(counted > 1, "the lift's encoding stays counted");
        assert!(
            stored <= counted,
            "the solver stores no more than is counted"
        );
        assert_eq!(*first.get_or_insert(lifted.clone()), lifted);
    }
}

#[test]
fn by_default_a_lift_keeps_its_gate() {
    // Retirement is opt-in: by default each lift leaves its gate inactive, as before.
    let f = fixture(3, Form::Redundant, false);
    let e = f.engine.clone();
    let original = &e.classification.as_ref().unwrap().0;
    let h = e.classification.as_ref().unwrap().2;
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    let view = s.simplified(original, true).unwrap();
    let slice = existence_slice::Slice::new(&view, Some(h), s.run.budget).unwrap();
    let accepted = s.encode_view(&slice.core, original, true).unwrap();
    let pins = s.pins(&f.observation).unwrap();
    assert!(s.solve(&[accepted.gate], &pins).unwrap());
    let values = s.existence_values(&slice, original, &accepted).unwrap();
    let mut cube = cover(&slice.core, &values, Some(h), s.run.budget).unwrap();
    assert!(!cube.is_empty());
    let gates = s.gates.len();
    existence::lift(&slice.core, &values, &accepted, &mut cube, &mut s).unwrap();
    assert_eq!(s.gates.len(), gates + 1);
}

#[test]
fn cover_telemetry_weighs_group_pins_by_the_values_they_allow() {
    // An input field with three values under at-most-one, plus a plain input.
    let mut c = Corpus::new();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = ["a", "b", "c"]
        .iter()
        .map(|v| c.declare_constant(*v, vs).unwrap())
        .collect();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Input,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let flag = rel(&mut c, "flag", true);
    let one = c
        .assume_in(
            Namespace::default(),
            "one_value",
            denotate_ir::Cardinality::AtMostOne,
            field,
            [],
        )
        .unwrap();
    let v = verification(&mut c, None, &[one]);
    let mut e = prepare(&c, v, &[(vs, values.clone())].into());
    // The estimate is built only when sizes are measured.
    e.limits.completion_sizes = Some(Default::default());
    let index = |a: GroundAtom| e.program.atom_index[&a];
    let fa = index(GroundAtom::new(field, [values[0]]));
    let fb = index(GroundAtom::new(field, [values[1]]));
    let fl = index(atom(flag));
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    let world = e.world.clone();
    let selector = s.gate().unwrap();
    let estimate = |s: &Solver<'_, '_, '_>| s.stats.covers[0].coverage_estimate.unwrap();
    let mass = |cube: &[(usize, bool)], s: &mut Solver<'_, '_, '_>| {
        let before = if s.stats.covers.is_empty() {
            0.0
        } else {
            estimate(s)
        };
        s.cube_metrics(&cube.iter().copied().collect(), &world, true, selector)
            .unwrap();
        estimate(s) - before
    };
    // One value chosen: 1 of 4 options (three values or none).
    assert!((mass(&[(fa, true)], &mut s) - 0.25).abs() < 1e-12);
    // Two values excluded: 2 of 4 options remain.
    assert!((mass(&[(fa, false), (fb, false)], &mut s) - 0.5).abs() < 1e-12);
    // A plain input halves the mass.
    assert!((mass(&[(fa, true), (fl, false)], &mut s) - 0.125).abs() < 1e-12);
    // Field a was pinned in all three cubes (true in two): counted apart,
    // and the ranking lists only the inputs that vary.
    let first = &s.stats.covers[0];
    assert_eq!(first.always_pinned, 1);
    assert_eq!(
        first.always_pinned_sample,
        vec![(GroundAtom::new(field, [values[0]]), 2)]
    );
    let mut varying = first.pinned.clone();
    varying.sort();
    let mut expected = vec![
        (GroundAtom::new(field, [values[1]]), 1, 0),
        (atom(flag), 1, 0),
    ];
    expected.sort();
    assert_eq!(varying, expected);
    assert!(s.stats.group_index_work.is_some());
    // Field a was pinned both ways (true twice, false once): the mixed list.
    assert_eq!(
        first.mixed,
        vec![(GroundAtom::new(field, [values[0]]), 3, 2)]
    );
    // A second loop (its own selector) keeps its own counters.
    let other = s.gate().unwrap();
    s.cube_metrics(&[(fl, true)].into_iter().collect(), &world, true, other)
        .unwrap();
    assert_eq!(s.stats.covers.len(), 2);
    assert_eq!(s.stats.covers[0].cubes, 3);
    assert_eq!(s.stats.covers[1].cubes, 1);
    assert!((s.stats.covers[1].coverage_estimate.unwrap() - 0.5).abs() < 1e-12);
    assert_eq!(s.stats.covers[1].always_pinned, 1);
    assert!(s.stats.covers[1].pinned.is_empty());
    // A capped group index makes the estimate unavailable, not wrong.
    assert!(
        GroupIndex::capped(&e, 0, std::time::Duration::MAX, s.run.budget)
            .unwrap()
            .index
            .is_none()
    );
    // At most 16 loops are retained; a new one releases the oldest record.
    for _ in 0..15 {
        let next = s.gate().unwrap();
        s.cube_metrics(&[(fl, true)].into_iter().collect(), &world, true, next)
            .unwrap();
    }
    assert_eq!(s.stats.covers.len(), 16);
    assert_eq!(s.stats.omitted_covers, 1);
    assert_eq!(s.stats.covers[0].index, 1, "the oldest loop was released");
    assert_eq!(s.covers.len(), 16);
}

#[test]
fn cover_telemetry_maps_a_derived_value_group_to_its_inputs() {
    // The corpus shape: at-most-one is stated over a derived relation whose members
    // each read a fact and one input (`scalar_observed(E, V) :- scalar(E),
    // observed_value(E, V)`); the estimate weighs the inputs as that group.
    let mut c = Corpus::new();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = ["a", "b", "c"]
        .iter()
        .map(|v| c.declare_constant(*v, vs).unwrap())
        .collect();
    let raw = c
        .declare_relation(
            "raw",
            RelationRole::Input,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Derived,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let scalar = c
        .declare_relation("scalar", RelationRole::Derived, vec![])
        .unwrap();
    emit(&mut c, &GroundAtom::new(scalar, []), &[]);
    for v in &values {
        emit(
            &mut c,
            &GroundAtom::new(field, [*v]),
            &[
                (&GroundAtom::new(scalar, []), true),
                (&GroundAtom::new(raw, [*v]), true),
            ],
        );
    }
    let one = c
        .assume_in(
            Namespace::default(),
            "one_value",
            denotate_ir::Cardinality::AtMostOne,
            field,
            [],
        )
        .unwrap();
    let v = verification(&mut c, None, &[one]);
    let mut e = prepare(&c, v, &[(vs, values.clone())].into());
    e.limits.completion_sizes = Some(Default::default());
    let premises = e.assumptions[0]
        .cone
        .rules
        .iter()
        .map(|r| r.body.len())
        .max();
    assert_eq!(
        premises,
        Some(2),
        "the fact premise stays in the assumption cone"
    );
    let ra = e.program.atom_index[&GroundAtom::new(raw, [values[0]])];
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    let world = e.world.clone();
    let selector = s.gate().unwrap();
    s.cube_metrics(&[(ra, true)].into_iter().collect(), &world, true, selector)
        .unwrap();
    assert!((s.stats.covers[0].coverage_estimate.unwrap() - 0.25).abs() < 1e-12);
}

#[test]
fn group_index_construction_polls_cancellation_and_deadlines() {
    // One at-most-one input group of 5,000 values: the scan crosses a poll point.
    let mut c = Corpus::new();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = (0..5000)
        .map(|n| c.declare_constant(format!("v{n}"), vs).unwrap())
        .collect();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Input,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let one = c
        .assume_in(
            Namespace::default(),
            "one_value",
            denotate_ir::Cardinality::AtMostOne,
            field,
            [],
        )
        .unwrap();
    let v = verification(&mut c, None, &[one]);
    let e = prepare(&c, v, &[(vs, values)].into());
    let budget = Budget::new(&e.limits);
    assert!(
        GroupIndex::capped(&e, usize::MAX, std::time::Duration::MAX, &budget)
            .unwrap()
            .index
            .is_some()
    );
    let mut expired = e.limits.clone();
    expired.timeout = std::time::Duration::ZERO;
    let budget = Budget::new(&expired);
    // The caller's own deadline propagates; it is not a quiet cutoff.
    let error = GroupIndex::capped(&e, usize::MAX, budget.remaining_time(), &budget)
        .err()
        .unwrap();
    assert!(inconclusive(error).is_ok(), "a deadline cutoff");
    e.limits.cancellation.cancel();
    let budget = Budget::new(&e.limits);
    assert!(matches!(
        GroupIndex::capped(&e, usize::MAX, std::time::Duration::MAX, &budget),
        Err(CheckError::Cancelled)
    ));
}

#[test]
fn equally_pinned_inputs_rank_by_atom_whatever_the_cube_order() {
    // Nine inputs pinned once each, the smallest last: it displaces the largest.
    let mut c = Corpus::new();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = (0..9)
        .map(|n| c.declare_constant(format!("v{n}"), vs).unwrap())
        .collect();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Input,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let v = verification(&mut c, None, &[]);
    let e = prepare(&c, v, &[(vs, values.clone())].into());
    let index = |v| e.program.atom_index[&GroundAtom::new(field, [v])];
    let mut budget = Budget::new(&e.limits);
    let mut s = Solver::new(&e, &mut budget).unwrap();
    let world = e.world.clone();
    let selector = s.gate().unwrap();
    for v in values[1..].iter().chain(&values[..1]) {
        s.cube_metrics(
            &[(index(*v), true)].into_iter().collect(),
            &world,
            true,
            selector,
        )
        .unwrap();
    }
    let pinned: Vec<_> = s.stats.covers[0]
        .pinned
        .iter()
        .map(|(a, _, _)| a.clone())
        .collect();
    let expected: Vec<_> = values[..8]
        .iter()
        .map(|v| GroundAtom::new(field, [*v]))
        .collect();
    assert_eq!(pinned, expected);
}

#[test]
fn empty_coverage_groups_count_toward_the_group_index_cap() {
    // Exactly-one per key over a relation nothing derives: one empty group per
    // key, 5,000 of them, and no members to scan.
    let mut c = Corpus::new();
    let ks = c.declare_sort("Key").unwrap();
    let keys: Vec<_> = (0..5000)
        .map(|n| c.declare_constant(format!("k{n}"), ks).unwrap())
        .collect();
    let vs = c.declare_sort("Value").unwrap();
    let value = c.declare_constant("v", vs).unwrap();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Derived,
            vec![Parameter::new("key", ks), Parameter::new("value", vs)],
        )
        .unwrap();
    let one = c
        .assume_in(
            Namespace::default(),
            "one_value",
            denotate_ir::Cardinality::ExactlyOne,
            field,
            [denotate_ir::Column::Index(0)],
        )
        .unwrap();
    let v = verification(&mut c, None, &[one]);
    let e = prepare(&c, v, &[(ks, keys), (vs, vec![value])].into());
    assert_eq!(e.assumptions[0].groups.len(), 5000);
    let budget = Budget::new(&e.limits);
    assert!(
        GroupIndex::capped(&e, usize::MAX, std::time::Duration::MAX, &budget)
            .unwrap()
            .index
            .is_some()
    );
    assert!(
        GroupIndex::capped(&e, 1000, std::time::Duration::MAX, &budget)
            .unwrap()
            .index
            .is_none()
    );
}

#[test]
fn the_group_index_is_built_once_per_preparation_and_only_when_measured() {
    let mut c = Corpus::new();
    let vs = c.declare_sort("Value").unwrap();
    let values: Vec<_> = ["a", "b"]
        .iter()
        .map(|v| c.declare_constant(*v, vs).unwrap())
        .collect();
    let field = c
        .declare_relation(
            "field",
            RelationRole::Input,
            vec![Parameter::new("value", vs)],
        )
        .unwrap();
    let one = c
        .assume_in(
            Namespace::default(),
            "one_value",
            denotate_ir::Cardinality::AtMostOne,
            field,
            [],
        )
        .unwrap();
    let v = verification(&mut c, None, &[one]);
    let mut e = prepare(&c, v, &[(vs, values.clone())].into());
    let fa = e.program.atom_index[&GroundAtom::new(field, [values[0]])];
    let world = e.world.clone();
    // Not measured: no index, no estimate.
    {
        let mut budget = Budget::new(&e.limits);
        let mut s = Solver::new(&e, &mut budget).unwrap();
        let selector = s.gate().unwrap();
        s.cube_metrics(&[(fa, true)].into_iter().collect(), &world, true, selector)
            .unwrap();
        assert!(s.stats.covers[0].coverage_estimate.is_none());
        assert!(s.stats.group_index_work.is_none());
        assert!(e.group_index.lock().unwrap().is_none());
    }
    // Measured: built by the first search, reused by a clone's search.
    e.limits.completion_sizes = Some(Default::default());
    let mut budget = Budget::new(&e.limits);
    // A time cutoff of the builder's own share is not shared: the next search
    // builds the index.
    let (cut, built) = GroupIndex::shared_with(&e, || {
        GroupIndex::capped(&e, usize::MAX, std::time::Duration::ZERO, &budget)
    })
    .unwrap();
    assert!(built && cut.timed_out && cut.index.is_none());
    assert!(e.group_index.lock().unwrap().is_none());
    let (first, built) = GroupIndex::shared(&e, &budget).unwrap();
    assert!(built && first.index.is_some());
    let branch = e.clone();
    let (again, built) = GroupIndex::shared(&branch, &budget).unwrap();
    assert!(!built, "a clone reuses the index");
    assert!(Arc::ptr_eq(&first, &again));
    let mut s = Solver::new(&branch, &mut budget).unwrap();
    let selector = s.gate().unwrap();
    s.cube_metrics(&[(fa, true)].into_iter().collect(), &world, true, selector)
        .unwrap();
    assert!((s.stats.covers[0].coverage_estimate.unwrap() - 1.0 / 3.0).abs() < 1e-12);
}
