use super::*;
use crate::test_support::rewrites::{rel, rule, stable_models, subsets};
use denotate_ir::{Cardinality, Literal, Parameter, RelationRole, Term};

fn limits() -> Limits {
    Limits {
        timeout: Duration::from_secs(60),
        ..Limits::default()
    }
}
fn prepared(c: &Corpus, domains: &Domains) -> Measurement {
    Measurement::prepare(c, domains, &limits()).unwrap()
}
fn model(m: &Measurement) -> Model {
    Model::new(&m.program, &mut Budget::new(&limits())).unwrap()
}
fn run(m: &mut Model, pass: Pass, local: &SimplificationLimits) -> (PassStats, Changes) {
    let mut changes = Changes { records: vec![] };
    let stats = apply(m, pass, local, &mut changes, &mut Budget::new(&limits())).unwrap();
    (stats, changes)
}
fn id(m: &Model, r: RelationId) -> usize {
    m.atoms.iter().position(|a| a.relation == r).unwrap()
}
fn permitted(m: &Model, world: &[bool]) -> bool {
    m.groups.iter().all(|(kind, atoms, _)| {
        let n = atoms.iter().filter(|a| world[**a]).count();
        (!kind.has_coverage() || n > 0) && (!kind.has_uniqueness() || n <= 1)
    })
}
// Independent propositional reduct/least-model enumeration. Restore aliases and
// constants as definitions over the original names; do not use BDDs or the
// production simplifier's body substitution/evaluator to compute the oracle.
fn models(m: &Model, world: &[bool]) -> BTreeSet<Vec<bool>> {
    assert!(m.atoms.len() <= 12);
    let mut rules = vec![];
    for h in 0..m.atoms.len() {
        if m.inputs[h] {
            continue;
        }
        match m.binding[h] {
            Binding::Constant(true) => rules.push((h, vec![])),
            Binding::Constant(false) => (),
            Binding::Atom(rep) if h != rep => rules.push((h, vec![(rep, false)])),
            _ => {
                for body in &m.bodies[h] {
                    rules.push((h, body.iter().map(|l| (atom(*l), *l < 0)).collect()));
                }
            }
        }
    }
    (0..1usize << m.atoms.len())
        .filter_map(|bits| {
            let guess: Vec<_> = (0..m.atoms.len()).map(|a| bits & (1 << a) != 0).collect();
            if (0..m.atoms.len()).any(|a| m.inputs[a] && guess[a] != world[a]) {
                return None;
            }
            let reduct: Vec<_> = rules
                .iter()
                .filter(|(_, body)| body.iter().all(|(a, neg)| !*neg || !guess[*a]))
                .collect();
            let mut value = world.to_vec();
            loop {
                let old = value.clone();
                for (h, body) in &reduct {
                    if body.iter().all(|(a, neg)| *neg || value[*a]) {
                        value[*h] = true;
                    }
                }
                if old == value {
                    break;
                }
            }
            (value == guess).then_some(value)
        })
        .collect()
}
fn check_models(p: &Measurement, m: &Model) {
    let all_atoms = p.program.atoms().cloned().collect::<Vec<_>>();
    let rules = p.program.rules().cloned().collect::<Vec<_>>();
    let fixed: BTreeSet<_> = all_atoms
        .iter()
        .filter(|a| p.program.fixed_value(a) == Some(true))
        .cloned()
        .collect();
    for world in subsets(&p.program.inputs.iter().cloned().collect::<Vec<_>>()) {
        let bits: Vec<_> = m.atoms.iter().map(|a| world.contains(a)).collect();
        if !permitted(m, &bits) {
            continue;
        }
        let expected = stable_models(&all_atoms, &p.program.inputs, &rules, &world);
        let actual: BTreeSet<BTreeSet<_>> = models(m, &bits)
            .into_iter()
            .map(|values| {
                fixed
                    .iter()
                    .cloned()
                    .chain(
                        m.atoms
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| values[*i])
                            .map(|(_, a)| a.clone()),
                    )
                    .collect()
            })
            .collect();
        assert_eq!(actual, expected, "world {world:?}");
    }
}
fn check_all(p: &Measurement) {
    for passes in [
        vec![Pass::Hash],
        vec![Pass::Constants],
        vec![Pass::DeadPremises],
        vec![Pass::Subsumption],
        vec![
            Pass::Hash,
            Pass::Constants,
            Pass::DeadPremises,
            Pass::Subsumption,
        ],
    ] {
        let mut m = model(p);
        check_models(p, &m);
        for pass in passes {
            run(&mut m, pass, &SimplificationLimits::default());
            check_models(p, &m);
        }
    }
}
#[test]
fn hashing_shares_derived_definitions_bottom_up_but_not_inputs() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let d = rel(&mut c, "d", false);
    let aa = rel(&mut c, "aa", false);
    let bb = rel(&mut c, "bb", false);
    rule(&mut c, a, &[(x, false)]);
    rule(&mut c, b, &[(x, false)]);
    rule(&mut c, d, &[(y, false)]);
    rule(&mut c, aa, &[(a, true)]);
    rule(&mut c, bb, &[(b, true)]);
    let p = prepared(&c, &Domains::new());
    let mut m = model(&p);
    let (s, changes) = run(&mut m, Pass::Hash, &SimplificationLimits::default());
    assert_eq!(s.proved, 2);
    assert_eq!(m.resolve(id(&m, a)), m.resolve(id(&m, b)));
    assert_eq!(m.resolve(id(&m, aa)), m.resolve(id(&m, bb)));
    assert_ne!(m.resolve(id(&m, a)), m.resolve(id(&m, d)));
    assert_ne!(m.resolve(id(&m, x)), m.resolve(id(&m, y)));
    assert!(
        changes
            .records
            .iter()
            .all(|r| matches!(r.reason, Reason::Identical(_)))
    );
    check_all(&p);
}
fn cardinality(kind: Cardinality) -> (Measurement, RelationId, RelationId, RelationId, RelationId) {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let x = c.declare_constant("x", s).unwrap();
    let y = c.declare_constant("y", s).unwrap();
    let input = c
        .declare_relation(
            "input",
            RelationRole::Input,
            [Parameter {
                name: "s".into(),
                sort: s,
            }],
        )
        .unwrap();
    c.constrain_input(input, kind, []).unwrap();
    let both = rel(&mut c, "both", false);
    let either = rel(&mut c, "either", false);
    let either_copy = rel(&mut c, "either_copy", false);
    let first = rel(&mut c, "first", false);
    let exclusive = rel(&mut c, "exclusive", false);
    for (head, body) in [
        (both, vec![(x, false), (y, false)]),
        (either, vec![(x, false)]),
        (either, vec![(y, false)]),
        (first, vec![(x, false)]),
        (exclusive, vec![(x, false), (y, true)]),
        (either_copy, vec![(x, false)]),
        (either_copy, vec![(y, false)]),
    ] {
        let head = c.atom(head, []).unwrap();
        let body: Vec<_> = body
            .into_iter()
            .map(|(value, neg)| {
                let atom = c.atom(input, [Term::Constant(value)]).unwrap();
                if neg {
                    Literal::Negative(atom)
                } else {
                    Literal::Positive(atom)
                }
            })
            .collect();
        c.add_rule(head, body).unwrap();
    }
    (
        prepared(&c, &Domains::from([(s, vec![x, y])])),
        both,
        either,
        first,
        exclusive,
    )
}
#[test]
fn u_constants_dead_bodies_and_implied_premises_preserve_every_world() {
    for kind in [Cardinality::AtMostOne, Cardinality::ExactlyOne] {
        let (p, both, either, first, exclusive) = cardinality(kind);
        let mut m = model(&p);
        run(&mut m, Pass::Constants, &SimplificationLimits::default());
        assert_eq!(m.resolve(id(&m, both)), Binding::Constant(false));
        assert_eq!(
            matches!(m.resolve(id(&m, either)), Binding::Constant(true)),
            kind == Cardinality::ExactlyOne
        );
        assert_eq!(m.resolve(id(&m, first)), Binding::Atom(id(&m, first)));
        let mut m = model(&p);
        let (_, changes) = run(&mut m, Pass::DeadPremises, &SimplificationLimits::default());
        assert!(m.bodies[id(&m, both)].is_empty());
        assert_eq!(m.bodies[id(&m, exclusive)][0].len(), 1);
        assert!(
            changes
                .records
                .iter()
                .any(|r| matches!(r.reason,Reason::Implied(l) if l<0))
        );
        check_all(&p);
    }
}
#[test]
fn complete_group_or_weakened_u_never_forces_one_boundary_input() {
    let (p, _, _, first, _) = cardinality(Cardinality::ExactlyOne);
    for max_cone_atoms in [1, 2, 3] {
        let mut m = model(&p);
        run(
            &mut m,
            Pass::Constants,
            &SimplificationLimits {
                max_cone_atoms,
                ..Default::default()
            },
        );
        assert_eq!(m.resolve(id(&m, first)), Binding::Atom(id(&m, first)));
        check_models(&p, &m);
    }
}
#[test]
fn free_cut_points_are_not_assumed_true_or_equal() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    let h = rel(&mut c, "h", false);
    rule(&mut c, a, &[(x, false)]);
    rule(&mut c, b, &[(y, false)]);
    rule(&mut c, h, &[(a, false), (b, false)]);
    let p = prepared(&c, &Domains::new());
    let mut m = model(&p);
    run(
        &mut m,
        Pass::DeadPremises,
        &SimplificationLimits {
            max_cone_atoms: 2,
            ..Default::default()
        },
    );
    assert_eq!(m.bodies[id(&m, h)][0].len(), 2);
    check_models(&p, &m);
}
#[test]
fn syntactic_subsumption_keeps_smallest_producer_and_negative_premises() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let y = rel(&mut c, "y", true);
    let h = rel(&mut c, "h", false);
    rule(&mut c, h, &[(x, true)]);
    rule(&mut c, h, &[(x, true), (y, false)]);
    rule(&mut c, h, &[(x, false), (y, false)]);
    let p = prepared(&c, &Domains::new());
    let mut m = model(&p);
    let (s, changes) = run(&mut m, Pass::Subsumption, &SimplificationLimits::default());
    assert_eq!(s.proved, 1);
    assert_eq!(m.bodies[id(&m, h)].len(), 2);
    assert!(
        matches!(&changes.records[0].reason,Reason::Subsumed(body) if body.len()==1 && body[0]<0)
    );
    check_all(&p);
}
#[test]
fn recursive_support_no_meaning_and_two_meanings_survive_all_passes() {
    for case in 0..5 {
        let mut c = Corpus::new();
        let seed = rel(&mut c, "seed", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        match case {
            0 => {
                rule(&mut c, p, &[(seed, false)]);
                rule(&mut c, p, &[(q, false)]);
                rule(&mut c, q, &[(p, false)]);
            }
            1 => {
                rule(&mut c, p, &[(q, true)]);
                rule(&mut c, q, &[(p, true)]);
            }
            2 => {
                rule(&mut c, p, &[(p, false)]);
            }
            3 => {
                rule(&mut c, p, &[(seed, false), (p, true)]);
            }
            _ => {
                rule(&mut c, p, &[(seed, false)]);
                rule(&mut c, p, &[(p, false)]);
                rule(&mut c, q, &[(p, true)]);
            }
        }
        let measurement = prepared(&c, &Domains::new());
        check_all(&measurement);
        if case == 0 {
            let mut m = model(&measurement);
            for pass in [
                Pass::Hash,
                Pass::Constants,
                Pass::DeadPremises,
                Pass::Subsumption,
            ] {
                assert_eq!(run(&mut m, pass, &Default::default()).0.proved, 0);
            }
        }
    }
}
#[test]
fn generated_tiny_programs_preserve_stable_models_after_each_pass() {
    for mask in 0..64 {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        let a = rel(&mut c, "a", false);
        let z = rel(&mut c, "z", false);
        let defs = [
            (a, vec![(x, false)]),
            (a, vec![(x, false), (y, true)]),
            (z, vec![(a, false), (y, false)]),
            (z, vec![(a, true)]),
            (a, vec![(z, true)]),
            (z, vec![(x, false)]),
        ];
        for (i, (h, body)) in defs.iter().enumerate() {
            if mask & (1 << i) != 0 {
                rule(&mut c, *h, body);
            }
        }
        check_all(&prepared(&c, &Domains::new()));
    }
}
#[test]
fn local_cutoff_keeps_candidate_global_exhaustion_returns_error() {
    let (p, _, _, _, _) = cardinality(Cardinality::ExactlyOne);
    for pass in [Pass::Constants, Pass::DeadPremises, Pass::Subsumption] {
        let mut m = model(&p);
        let original = m.clone();
        let (s, _) = run(
            &mut m,
            pass,
            &SimplificationLimits {
                max_proof_work: 0,
                ..Default::default()
            },
        );
        assert!(s.cut_off > 0);
        assert_eq!(m.binding, original.binding);
        assert_eq!(m.bodies, original.bodies);
    }
    assert!(
        p.simplify_comparison(
            &Default::default(),
            &Limits {
                max_work: 0,
                ..limits()
            }
        )
        .is_err()
    );
    let stopped = limits();
    stopped.cancellation.cancel();
    assert!(matches!(
        p.simplify_comparison(&Default::default(), &stopped),
        Err(CheckError::Cancelled)
    ));
}
#[test]
fn composition_is_deterministic_and_repeated_measurements_do_not_mutate_source() {
    let (p, _, _, _, _) = cardinality(Cardinality::ExactlyOne);
    let before = p.measure(false, &limits()).unwrap();
    let run = || {
        p.simplify_comparison(&Default::default(), &limits())
            .unwrap()
    };
    let a = run();
    let b = run();
    for (a, b) in a.iter().zip(b) {
        assert_eq!(
            (
                a.report.after.variables,
                a.report.after.clauses,
                a.report.after.literals
            ),
            (
                b.report.after.variables,
                b.report.after.clauses,
                b.report.after.literals
            )
        );
        for (a, b) in a.passes.iter().zip(b.passes) {
            assert_eq!(
                (
                    a.candidates,
                    a.proved,
                    a.unchanged,
                    a.unsupported,
                    a.cut_off
                ),
                (
                    b.candidates,
                    b.proved,
                    b.unchanged,
                    b.unsupported,
                    b.cut_off
                )
            );
        }
    }
    let after = p.measure(false, &limits()).unwrap();
    assert_eq!(
        (before.after.variables, before.after.clauses),
        (after.after.variables, after.after.clauses)
    );
}

#[test]
fn transformed_cnf_and_elimination_reconstruct_original_acyclic_models() {
    let (p, _, _, _, _) = cardinality(Cardinality::ExactlyOne);
    let mut m = model(&p);
    let mut changes = Changes { records: vec![] };
    for pass in [
        Pass::Hash,
        Pass::Constants,
        Pass::DeadPremises,
        Pass::Subsumption,
    ] {
        apply(
            &mut m,
            pass,
            &Default::default(),
            &mut changes,
            &mut Budget::new(&limits()),
        )
        .unwrap();
    }
    // Retained alias/constant records recover the exact translation, including
    // aliases whose representatives were folded by a later pass.
    let mut binding: Vec<_> = (0..m.atoms.len()).map(Binding::Atom).collect();
    for record in &changes.records {
        match record.reason {
            Reason::Identical(a) => binding[record.head] = Binding::Atom(a),
            Reason::Constant(v) => binding[record.head] = Binding::Constant(v),
            _ => (),
        }
    }
    assert_eq!(binding, m.binding);
    let active: Vec<_> = (0..m.atoms.len())
        .filter(|a| m.resolve(*a) == Binding::Atom(*a))
        .collect();
    let (mut cnf, candidates) = m.encode(&mut Budget::new(&limits())).unwrap();
    cnf.eliminate(&candidates, &mut Budget::new(&limits()))
        .unwrap();
    assert!(cnf.owners.len() < 16);
    let mut actual = BTreeSet::new();
    for bits in 0..1usize << cnf.owners.len() {
        let values: Vec<_> = (0..cnf.owners.len())
            .map(|i| bits & (1 << i) != 0)
            .collect();
        if !cnf
            .clauses
            .iter()
            .all(|c| c.lits.iter().any(|l| values[atom(*l)] == (*l > 0)))
        {
            continue;
        }
        let values = cnf.reconstruct(values);
        let result: Vec<_> = (0..m.atoms.len())
            .map(|i| match m.resolve(i) {
                Binding::Constant(v) => v,
                Binding::Atom(a) => values[active.iter().position(|v| *v == a).unwrap()],
            })
            .collect();
        actual.insert(result);
    }
    let original = model(&p);
    let mut expected = BTreeSet::new();
    for world in subsets(&p.program.inputs.iter().cloned().collect::<Vec<_>>()) {
        let bits: Vec<_> = m.atoms.iter().map(|a| world.contains(a)).collect();
        if permitted(&m, &bits) {
            expected.extend(models(&original, &bits));
        }
    }
    assert_eq!(actual, expected);
}

#[test]
fn composition_proves_against_substituted_providers() {
    let (p, _, either, _, _) = cardinality(Cardinality::ExactlyOne);
    let mut m = model(&p);
    let (stats, _) = run(&mut m, Pass::Hash, &Default::default());
    assert!(stats.proved > 0);
    let alias = m
        .binding
        .iter()
        .enumerate()
        .find_map(|(h, b)| match b {
            Binding::Atom(a) if *a != h => Some(h),
            _ => None,
        })
        .unwrap();
    run(&mut m, Pass::Constants, &Default::default());
    assert_eq!(m.resolve(alias), Binding::Constant(true));
    assert_eq!(m.resolve(id(&m, either)), Binding::Constant(true));
    check_models(&p, &m);
    m.encode(&mut Budget::new(&limits())).unwrap();
}
