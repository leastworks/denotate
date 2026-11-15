use super::*;
use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets, summaries};
use denotate_ir::Corpus;

fn compact(p: &GroundProgram, target: RelationId, limits: &Limits) -> SatProbeReport {
    let meaning = p.symbolic(&Limits::default()).unwrap();
    let sums = summaries(p, &meaning, &Limits::default());
    let comp = p.component_for(&atom(target)).unwrap();
    let rules = sums
        .values()
        .filter(|s| comp.atoms.contains(&s.rule.head.atom))
        .map(|s| s.rule.id)
        .collect();
    probe_built(
        comp.id,
        &Default::default(),
        limits,
        comp.cycle.is_some(),
        &|b| compact_cone(p, comp.id, &rules, &sums, meaning.context(), b),
    )
    .unwrap()
}

#[test]
fn exact_boundary_and_world_covers_agree_with_exhaustive_stable_models() {
    let limits = Limits::default();
    let mut seed = 572921u64;
    let mut rand = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    for case in 0..100 {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        let u = rel(&mut c, "upstream", false);
        let v = rel(&mut c, "recursive_provider", false);
        rule(&mut c, u, &[(x, false)]);
        rule(&mut c, u, &[(y, true)]);
        rule(&mut c, v, &[(v, false)]);
        rule(&mut c, v, &[(u, false), (y, false)]);
        let ds = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "d", false),
        ];
        for i in 0..3 {
            rule(
                &mut c,
                ds[i],
                &[(ds[(i + 1) % 3], case % 2 == 0 || i != 0), (u, false)],
            );
        }
        let all = [x, y, u, v, ds[0], ds[1], ds[2]];
        for _ in 0..3 {
            let body = (0..2)
                .map(|_| (all[rand() % all.len()], rand() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, ds[rand() % 3], &body);
        }
        let mut p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
        if case % 3 != 0 {
            let ctx = p.condition_context(&limits).unwrap();
            p.assumption_condition = Some(if case % 7 == 0 {
                ctx.false_condition()
            } else {
                ctx.input(&atom(x), &limits).unwrap()
            });
        }
        let result = compact(&p, ds[0], &limits);
        assert_ne!(
            result.answer,
            SatProbeAnswer::Unknown,
            "case {case}: {result:?}"
        );
        let ctx = p.condition_context(&limits).unwrap();
        let inputs = BTreeSet::from([atom(x), atom(y)]);
        let atoms = all.map(atom);
        let rules = p.rules().cloned().collect::<Vec<_>>();
        let comp = p.component_for(&atom(ds[0])).unwrap();
        let mut worlds = 0;
        let mut ambiguous = false;
        let mut missing = false;
        for world in subsets(&[atom(x), atom(y)]) {
            if !ctx
                .evaluate(&ctx.permitted_worlds(), world.iter().cloned(), &limits)
                .unwrap_or(false)
            {
                continue;
            }
            worlds += 1;
            let models = stable_models(&atoms, &inputs, &rules, &world);
            missing |= models.is_empty();
            let projected = models
                .iter()
                .map(|m| {
                    comp.atoms
                        .iter()
                        .filter(|a| m.contains(*a))
                        .cloned()
                        .collect::<BTreeSet<_>>()
                })
                .collect::<BTreeSet<_>>();
            ambiguous |= projected.len() > 1;
            if let Some(pair) = &result.pair {
                if pair.world == world {
                    assert!(
                        pair.models.iter().all(|m| projected.contains(m)),
                        "case {case}"
                    );
                }
            }
            if result.existence.as_ref().and_then(|e| e.world.as_ref()) == Some(&world) {
                assert!(models.is_empty(), "case {case}: invalid no-meaning world");
            }
        }
        assert_eq!(
            result.answer == SatProbeAnswer::Sat,
            ambiguous,
            "case {case}"
        );
        if !ambiguous {
            assert_eq!(
                result.existence.unwrap().answer,
                if worlds == 0 {
                    SatExistenceAnswer::InconsistentAssumptions
                } else if missing {
                    SatExistenceAnswer::NoMeaning
                } else {
                    SatExistenceAnswer::EveryWorld
                },
                "case {case}"
            );
        }
    }
}

#[test]
fn settled_boundary_replaces_a_large_upstream_cone() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let mut previous = x;
    for i in 0..1000 {
        let next = rel(&mut c, &format!("layer_{i}"), false);
        rule(&mut c, next, &[(previous, false)]);
        previous = next;
    }
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(previous, false), (b, true)]);
    rule(&mut c, b, &[(previous, false), (a, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
    let old = probe_component(
        &p,
        p.component_for(&atom(a)).unwrap().id,
        &[],
        &Default::default(),
        &limits,
    )
    .unwrap();
    let new = compact(&p, a, &limits);
    assert_eq!(old.answer, SatProbeAnswer::Sat);
    assert_eq!(new.answer, old.answer);
    assert!(new.cone_atoms < old.cone_atoms);
    assert!(new.cone_rules < old.cone_rules);
    assert!(new.variables < old.variables);
    println!(
        "full cone: atoms={} rules={} variables={}; settled boundary: atoms={} rules={} condition nodes={} variables={}",
        old.cone_atoms,
        old.cone_rules,
        old.variables,
        new.cone_atoms,
        new.cone_rules,
        new.condition_nodes,
        new.variables
    );
}

#[test]
fn compact_encoding_limits_are_unknown_with_a_resource_reason() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    rule(&mut c, a, &[(x, false), (a, true)]);
    let limits = Limits::default();
    let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &limits).unwrap();
    for limits in [
        Limits {
            max_atoms: 1,
            ..limits.clone()
        },
        Limits {
            max_rules: 0,
            ..limits.clone()
        },
        Limits {
            max_work: 1,
            ..limits.clone()
        },
        Limits {
            max_dependencies: 0,
            ..limits.clone()
        },
        Limits {
            timeout: Duration::ZERO,
            ..limits
        },
    ] {
        let r = compact(&p, a, &limits);
        assert_eq!(r.answer, SatProbeAnswer::Unknown);
        assert!(r.reason.is_some());
        assert!(r.existence.is_none());
    }
}

#[test]
fn replacement_expressions_retain_their_signed_input_guard() {
    let mut c = Corpus::new();
    let x = rel(&mut c, "x", true);
    let a = rel(&mut c, "a", false);
    let b = rel(&mut c, "b", false);
    rule(&mut c, a, &[(x, true), (b, true)]);
    rule(&mut c, b, &[(x, true), (a, true)]);
    let l = Limits::default();
    let mut p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
    // An equivalent executable spelling of each input premise, as installed
    // guarded replacements use. The original stable pair is possible only at !x.
    for rule in &mut p.rules {
        let index = rule
            .body
            .iter()
            .position(|v| v.term.atom == atom(x))
            .unwrap();
        let literal = rule.body.remove(index);
        rule.replacements.push(SettledReplacement {
            occurrence: literal.term.occurrence,
            expression: std::sync::Arc::new(SettledExpression::Not(std::sync::Arc::new(
                SettledExpression::Atom(atom(x)),
            ))),
        });
    }
    let r = compact(&p, a, &l);
    assert_eq!(r.answer, SatProbeAnswer::Sat);
    assert!(r.pair.unwrap().world.is_empty());
    let ctx = p.condition_context(&l).unwrap();
    p.assumption_condition = Some(ctx.input(&atom(x), &l).unwrap());
    let r = compact(&p, a, &l);
    assert_eq!(r.answer, SatProbeAnswer::Unsat);
    assert_eq!(r.existence.unwrap().answer, SatExistenceAnswer::EveryWorld);
}
