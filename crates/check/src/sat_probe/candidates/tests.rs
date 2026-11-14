use super::*;
use crate::{
    guarded_bounds::{Preparation, prepare},
    test_support::rewrites::{atom, rel, rule, subsets, summaries, supported_models},
};
use denotate_ir::Corpus;

#[test]
fn relaxed_reading_is_optional_and_positive_support_is_not_refined() {
    for positive in [false, true] {
        let mut c = Corpus::new();
        let h = rel(&mut c, "h", false);
        let p = rel(&mut c, "p", false);
        rule(&mut c, h, &[(p, !positive)]);
        rule(&mut c, p, &[(h, !positive)]);
        let l = Limits::default();
        let program = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        let meaning = program.symbolic(&l).unwrap();
        let summaries = summaries(&program, &meaning, &l);
        // Positive recursion is settled by the ordinary evaluator, so deliberately
        // construct unresolved summaries here to test the supported-model query.
        let mut summaries = summaries;
        for s in summaries.values_mut() {
            s.settled.clear();
            s.condition = meaning.context().true_condition();
            s.exact = false;
        }
        let r = summaries
            .values()
            .find(|s| s.rule.head.atom == atom(h))
            .unwrap();
        let index = summaries
            .values()
            .fold(BTreeMap::<_, Vec<_>>::new(), |mut m, s| {
                m.entry(&s.rule.head.atom).or_default().push(s.rule.id);
                m
            });
        let cone = prepare(
            &program,
            program.component_for(&atom(h)).unwrap(),
            r,
            &atom(p),
            &summaries,
            &index,
            meaning.context(),
            &mut 0,
            &mut Budget::new(&l),
            &mut Preparation::default(),
        )
        .unwrap();
        let report = probe(
            &cone,
            meaning.context(),
            r,
            &r.rule.body[0],
            &mut Budget::new(&l),
        )
        .unwrap();
        assert_eq!(report.answer, SatProbeAnswer::Sat, "{:?}", report.reason);
        assert!(report.pair.unwrap().differing.contains(&atom(p)));
    }
}

#[test]
fn tiny_candidate_queries_agree_with_exhaustive_supported_models() {
    let l = Limits::default();
    let mut seed = 97821u64;
    let mut rand = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed as usize
    };
    let mut checked = 0;
    for case in 0..48 {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let y = rel(&mut c, "y", true);
        let derived = [
            rel(&mut c, "a", false),
            rel(&mut c, "b", false),
            rel(&mut c, "c", false),
        ];
        for i in 0..3 {
            rule(&mut c, derived[i], &[(derived[(i + 1) % 3], true)]);
        }
        let all = [x, y, derived[0], derived[1], derived[2]];
        for _ in 0..3 {
            let body = (0..2)
                .map(|_| (all[rand() % all.len()], rand() % 2 == 0))
                .collect::<Vec<_>>();
            rule(&mut c, derived[rand() % 3], &body);
        }
        let mut program = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        if case % 2 == 0 {
            let ctx = program.condition_context(&l).unwrap();
            program.assumption_condition = Some(ctx.input(&atom(x), &l).unwrap());
        }
        let meaning = program.symbolic(&l).unwrap();
        let ctx = meaning.context();
        let sums = summaries(&program, &meaning, &l);
        let index = sums
            .values()
            .fold(BTreeMap::<_, Vec<_>>::new(), |mut m, s| {
                m.entry(&s.rule.head.atom).or_default().push(s.rule.id);
                m
            });
        for r in sums.values().filter(|s| !s.exact) {
            let comp = program.component_for(&r.rule.head.atom).unwrap();
            for literal in &r.rule.body {
                if program.component_for(&literal.term.atom).unwrap().id != comp.id {
                    continue;
                }
                let cone = prepare(
                    &program,
                    comp,
                    r,
                    &literal.term.atom,
                    &sums,
                    &index,
                    ctx,
                    &mut 0,
                    &mut Budget::new(&l),
                    &mut Preparation::default(),
                )
                .unwrap();
                let answer = probe(&cone, ctx, r, literal, &mut Budget::new(&l)).unwrap();
                assert_ne!(
                    answer.answer,
                    SatProbeAnswer::Unknown,
                    "{:?}",
                    answer.reason
                );
                let pair = subsets(&[atom(x), atom(y)]).iter().any(|world| {
                    if !ctx
                        .evaluate(&cone.domain, world.iter().cloned(), &l)
                        .unwrap_or(false)
                    {
                        return false;
                    }
                    let mut values = BTreeSet::new();
                    for firing in [false, true] {
                        let rules = program
                            .rules()
                            .filter_map(|orig| {
                                if orig.id == r.rule.id {
                                    if !firing {
                                        return None;
                                    }
                                    let mut fact = orig.clone();
                                    fact.body.clear();
                                    fact.replacements.clear();
                                    Some(fact)
                                } else {
                                    Some(orig.clone())
                                }
                            })
                            .collect::<Vec<_>>();
                        for m in supported_models(&program, &rules, world) {
                            values.insert(m.contains(&literal.term.atom));
                        }
                    }
                    values.len() == 2
                });
                assert_eq!(
                    answer.answer == SatProbeAnswer::Sat,
                    pair,
                    "case {case}, {:?}",
                    r.rule.id
                );
                checked += 1;
            }
        }
    }
    assert!(checked > 50);
}

#[test]
fn diagnostic_deadline_and_work_are_separate_and_cancellation_is_live() {
    let l = Limits::default();
    let mut budget = Budget::tracked(&l);
    budget.charge(7, "before diagnostic").unwrap();
    let before = budget.snapshot();
    let result: Result<()> =
        budget.excluding_time(|| Err(CheckError::deadline("probe", Duration::ZERO)));
    assert!(result.is_err());
    budget.check("ordinary admission").unwrap();
    assert_eq!(before, budget.snapshot());
    budget.excluding_time(|| l.cancellation.cancel());
    assert!(matches!(
        budget.check("ordinary admission"),
        Err(CheckError::Cancelled)
    ));
}
