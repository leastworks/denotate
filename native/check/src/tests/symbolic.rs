use crate::*;
use denotate_ir::*;
use std::{collections::BTreeSet, time::Instant};

pub(super) use crate::test_support::symbolic::*;

#[test]
fn boolean_queries_do_not_require_admissibility_and_reject_foreign_conditions() {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let bad = relation(&mut c, "bad", false);
    rule(&mut c, bad, &[(bad, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert!(!p.is_admitted());
    let ctx = p.condition_context(&limits).unwrap();
    let x_c = ctx.input(&nullary(x), &limits).unwrap();
    let not_x = ctx.not(&x_c, &limits).unwrap();
    let never = ctx.and(&x_c, &not_x, &limits).unwrap();
    let always = ctx.or(&x_c, &not_x, &limits).unwrap();
    assert!(!never.can_hold());
    assert!(!always.can_fail());
    assert!(x_c.can_hold() && x_c.can_fail());
    assert!(!ctx.may_overlap(&x_c, &not_x, &limits).unwrap());
    assert!(ctx.implies(&x_c, &always, &limits).unwrap());
    assert!(!ctx.implies(&always, &x_c, &limits).unwrap());
    assert!(
        ctx.equivalent(&ctx.not(&not_x, &limits).unwrap(), &x_c, &limits)
            .unwrap()
    );
    assert!(ctx.input(&nullary(bad), &limits).is_err());
    assert!(ctx.evaluate(&x_c, [nullary(bad)], &limits).is_err());
    let other = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let foreign = other.condition_context(&limits).unwrap().true_condition();
    assert!(matches!(
        ctx.and(&x_c, &foreign, &limits),
        Err(CheckError::ForeignCondition)
    ));
    assert!(matches!(
        ctx.not(&foreign, &limits),
        Err(CheckError::ForeignCondition)
    ));
    assert_eq!(
        ctx.equivalent(&x_c, &foreign, &limits),
        Err(CheckError::ForeignCondition)
    );
    assert_eq!(
        ctx.evaluate(&foreign, [], &limits),
        Err(CheckError::ForeignCondition)
    );
    // Recreating a context for the SAME immutable program uses the same universe.
    let same = p
        .condition_context(&limits)
        .unwrap()
        .input(&nullary(x), &limits)
        .unwrap();
    assert!(ctx.equivalent(&x_c, &same, &limits).unwrap());
}

#[test]
fn acyclic_components_skip_confirmation_without_losing_alternative_derivations() {
    for length in [8, 64] {
        let limits = Limits::default();
        let mut c = Corpus::new();
        let x = relation(&mut c, "x", true);
        let y = relation(&mut c, "y", true);
        let mut head = x;
        for n in 0..length {
            let next = relation(&mut c, &format!("r{n}"), false);
            rule(&mut c, next, &[(head, false)]);
            // Multiple producers must all run even without an internal edge.
            rule(&mut c, next, &[(y, false)]);
            head = next;
        }
        let mut p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        assert!(p.components().all(|c| !c.recursive));
        assert_symbolic_agrees(&p);
        let m = p.symbolic(&limits).unwrap();
        let expected: Vec<_> = p
            .atoms()
            .map(|a| (a.clone(), condition(&m, a.clone())))
            .collect();
        let one_pass_work = m.metrics().work;
        let ctx = m.context();
        let either = ctx
            .or(
                &ctx.input(&nullary(x), &limits).unwrap(),
                &ctx.input(&nullary(y), &limits).unwrap(),
                &limits,
            )
            .unwrap();
        assert!(
            ctx.equivalent(&condition(&m, nullary(head)), &either, &limits)
                .unwrap()
        );
        drop(m);

        // Test-only conservative schedule: force the former extra pass while
        // leaving the same program and its input universe intact.
        for component in &mut p.components {
            component.recursive = true;
        }
        let conservative = p.symbolic(&limits).unwrap();
        for (atom, expected) in expected {
            assert!(
                conservative
                    .context()
                    .equivalent(&condition(&conservative, atom), &expected, &limits)
                    .unwrap()
            );
        }
        assert!(conservative.metrics().work > one_pass_work);
    }
}

#[test]
fn long_growing_guard_chain_exceeds_default_limits_without_a_successful_meaning() {
    let limits = Limits::default();
    let size = 1_000;
    let (corpus, domains) = super::sparse::mapping_corpus(size, true);
    let program = GroundProgram::prepare(&corpus, &domains, &limits).unwrap();
    assert!(program.is_admitted());
    assert!(program.components().all(|c| !c.recursive));
    assert_eq!(program.atoms().count(), 4 * size);
    assert_eq!(program.rules().count(), 3 * size);
    assert_eq!(program.dependencies().count(), 4 * size - 1);
    let replay = program
        .evaluate(program.input_atoms().cloned(), &limits)
        .unwrap();
    assert_eq!(replay.established_facts().count(), 4 * size);

    // Sparse grounding and concrete replay succeed, but retaining all growing
    // prefix conditions in independently owned BDD vectors exceeds the current
    // defaults. Revisit this expectation if the backend/storage model changes.
    assert!(matches!(
        program.symbolic(&limits),
        Err(CheckError::LimitExceeded { .. })
    ));
}

#[test]
#[ignore = "manual growing-condition measurement; run alone with --release --nocapture"]
fn measure_growing_guard_chain() {
    let limits = Limits::default();
    println!(
        "slots,atoms,rules,dependencies,prepare_ms,symbolic_ms,replay_ms,retained_nodes,work,result"
    );
    for size in [20, 100, 250, 500, 1_000] {
        let (corpus, domains) = super::sparse::mapping_corpus(size, true);
        let start = Instant::now();
        let program = GroundProgram::prepare(&corpus, &domains, &limits).unwrap();
        let prepare_ms = start.elapsed().as_secs_f64() * 1_000.0;
        let start = Instant::now();
        let result = program.symbolic(&limits);
        let symbolic_ms = start.elapsed().as_secs_f64() * 1_000.0;
        let start = Instant::now();
        let replay = program
            .evaluate(program.input_atoms().cloned(), &limits)
            .unwrap();
        let replay_ms = start.elapsed().as_secs_f64() * 1_000.0;
        assert_eq!(replay.established_facts().count(), 4 * size);
        let (nodes, work, status) = match result {
            Ok(meaning) => {
                // Inputs, mapped_to, supplies and available all retain a condition.
                let expected = (3 * size * size + 19 * size) / 2;
                assert_eq!(meaning.metrics().retained_condition_nodes, expected);
                (
                    expected.to_string(),
                    meaning.metrics().work.to_string(),
                    "complete".to_owned(),
                )
            }
            Err(CheckError::LimitExceeded { phase, resource }) => (
                "-".to_owned(),
                "-".to_owned(),
                format!("LimitExceeded: {phase}/{resource}"),
            ),
            Err(error) => panic!("unexpected measurement failure: {error}"),
        };
        println!(
            "{size},{},{},{},{prepare_ms:.2},{symbolic_ms:.2},{replay_ms:.2},{nodes},{work},{status}",
            program.atoms().count(),
            program.rules().count(),
            program.dependencies().count()
        );
    }
}

#[test]
fn recursive_conditions_keep_broadening_until_their_meanings_stabilize() {
    let mut c = Corpus::new();
    let x = relation(&mut c, "x", true);
    let y = relation(&mut c, "y", true);
    let p = relation(&mut c, "p", false);
    let q = relation(&mut c, "q", false);
    let not_p = relation(&mut c, "not_p", false);
    let dead = relation(&mut c, "dead", false);
    let not_dead = relation(&mut c, "not_dead", false);
    let impossible = relation(&mut c, "impossible", false);
    let not_impossible = relation(&mut c, "not_impossible", false);
    rule(&mut c, p, &[(q, false)]);
    rule(&mut c, q, &[(p, false)]);
    rule(&mut c, p, &[(x, false)]);
    rule(&mut c, q, &[(y, false)]);
    // Once p covers x OR y, this narrower derivation adds no worlds.
    rule(&mut c, p, &[(x, false), (y, false)]);
    rule(&mut c, not_p, &[(p, true)]);
    rule(&mut c, dead, &[(dead, false)]);
    rule(&mut c, not_dead, &[(dead, true)]);
    rule(&mut c, impossible, &[(x, false), (x, true)]);
    rule(&mut c, not_impossible, &[(impossible, true)]);
    let limits = Limits::default();
    let program = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    assert_symbolic_agrees(&program);
    let m = program.symbolic(&limits).unwrap();
    let ctx = m.context();
    let either = ctx
        .or(
            &ctx.input(&nullary(x), &limits).unwrap(),
            &ctx.input(&nullary(y), &limits).unwrap(),
            &limits,
        )
        .unwrap();
    assert!(
        ctx.equivalent(&condition(&m, nullary(p)), &either, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(&condition(&m, nullary(q)), &either, &limits)
            .unwrap()
    );
    assert!(
        ctx.equivalent(
            &condition(&m, nullary(not_p)),
            &ctx.not(&either, &limits).unwrap(),
            &limits,
        )
        .unwrap()
    );
    assert!(condition(&m, nullary(dead)).is_false());
    assert!(condition(&m, nullary(not_dead)).is_true());
    assert!(!m.conditions.contains_key(&nullary(dead)));
    assert!(program.is_possible(&nullary(impossible)).unwrap());
    assert!(condition(&m, nullary(impossible)).is_false());
    assert!(condition(&m, nullary(not_impossible)).is_true());
    assert!(!m.conditions.contains_key(&nullary(impossible)));
    let cone = program
        .dependency_cone([nullary(not_dead)], &limits)
        .unwrap();
    assert!(cone.facts.contains(&nullary(dead))); // Structural absence, no component.
    assert_eq!(cone.components.len(), 1);
}

#[test]
fn cone_retains_other_producers_even_if_a_true_alternative_hides_them_booleanly() {
    let mut c = Corpus::new();
    let t = relation(&mut c, "t", true);
    let bad = relation(&mut c, "bad", false);
    let out = relation(&mut c, "out", false);
    rule(&mut c, bad, &[(bad, true)]);
    let first = rule(&mut c, out, &[]);
    let second = rule(&mut c, out, &[(t, false), (bad, false)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
    let m = p.symbolic(&limits).unwrap();
    assert!(matches!(
        m.fact(&nullary(out)).unwrap(),
        SymbolicFact::Blocked(_)
    ));
    let cone = p.dependency_cone([nullary(out)], &limits).unwrap();
    let sources: BTreeSet<_> = cone
        .rules
        .iter()
        .map(|id| p.rule(*id).unwrap().source)
        .collect();
    assert!(sources.contains(&first) && sources.contains(&second));
    assert!(cone.facts.contains(&nullary(t)));
    assert!(cone.facts.contains(&nullary(bad)));
    assert_eq!(cone.blocked_by.len(), 1);
}

#[test]
fn constant_groups_work_with_zero_input_variables_including_trivial_groups() {
    let limits = Limits::default();
    for count in [0, 1, 3] {
        let mut c = Corpus::new();
        let s = c.declare_sort("Value").unwrap();
        let values: Vec<_> = (0..3)
            .map(|i| c.declare_constant(format!("v{i}"), s).unwrap())
            .collect();
        let r = c
            .declare_relation("r", RelationRole::Derived, [Parameter::new("value", s)])
            .unwrap();
        for value in &values[..count] {
            let head = c.atom(r, [(*value).into()]).unwrap();
            c.add_rule(head, []).unwrap();
        }
        c.at_most_one("one", r, Vec::<Column>::new(), "one value")
            .unwrap();
        let p = GroundProgram::prepare(&c, &Domains::from([(s, values)]), &limits).unwrap();
        assert_symbolic_agrees(&p);
        let m = p.symbolic(&limits).unwrap();
        assert_eq!(m.context().inputs().count(), 0);
        let report = m.check_at_most_one(&limits).unwrap();
        assert!(report.whole_program_admitted);
        if count <= 1 {
            assert!(report.groups.is_empty());
        } else {
            assert_eq!(report.groups.len(), 1);
            assert_eq!(report.groups[0].group.tuples.len(), 3);
            let GroupOutcome::Overlap(overlap) = &report.groups[0].outcome else {
                panic!("missing constant conflict")
            };
            assert!(overlap.is_true());
            assert!(m.context().evaluate(overlap, [], &limits).unwrap());
        }
    }
}
