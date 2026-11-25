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
