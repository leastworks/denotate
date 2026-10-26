//! Production portable conditions checked against exhaustive Boolean worlds.
use super::*;
use denotate_ir::{QualifiedKey, RelationKey};

#[test]
fn constrained_queries_match_exhaustive_boolean_worlds_without_mutating_the_formula() {
    let selected: Vec<_> = ["a", "b", "c"]
        .into_iter()
        .map(|name| AtomKey {
            relation: RelationKey::Named(QualifiedKey::new("boolean-oracle", name)),
            arguments: vec![],
        })
        .collect();
    let current = Current::new(&selected, false);
    let ctx = current.context();
    let limits = &current.limits;
    let variables: Vec<_> = current
        .atoms
        .values()
        .map(|atom| ctx.input(atom, limits).unwrap())
        .collect();
    // Preserve the retired solver's independent CNF oracle on the BDD query path.
    for seed in 0..128_u32 {
        let mut rng = seed + 1;
        let mut clauses = Vec::new();
        let mut formula = ctx.true_condition();
        for _ in 0..5 {
            let mut literals = Vec::new();
            let mut clause = ctx.false_condition();
            for _ in 0..3 {
                rng = rng.wrapping_mul(1664525).wrapping_add(1013904223);
                let (index, positive) = ((rng as usize >> 4) % 3, rng & 1 != 0);
                literals.push((index, positive));
                let literal = if positive {
                    variables[index].clone()
                } else {
                    ctx.not(&variables[index], limits).unwrap()
                };
                clause = ctx.or(&clause, &literal, limits).unwrap();
            }
            clauses.push(literals);
            formula = ctx.and(&formula, &clause, limits).unwrap();
        }
        let mut any = false;
        for mask in 0..8 {
            let expected = clauses.iter().all(|clause| {
                clause
                    .iter()
                    .any(|(index, positive)| (mask & (1 << index) != 0) == *positive)
            });
            any |= expected;
            let mut restricted = formula.clone();
            for (index, variable) in variables.iter().enumerate() {
                let literal = if mask & (1 << index) != 0 {
                    variable.clone()
                } else {
                    ctx.not(variable, limits).unwrap()
                };
                restricted = ctx.and(&restricted, &literal, limits).unwrap();
            }
            assert_eq!(
                ctx.witness(&restricted, limits).unwrap().is_some(),
                expected
            );
        }
        assert_eq!(
            ctx.witness(&formula, limits).unwrap().is_some(),
            any,
            "an unsatisfiable restricted query must not poison the original formula"
        );
    }
}

struct Current {
    program: GroundProgram,
    keys: denotate_ir::SemanticKeys,
    atoms: BTreeMap<AtomKey, GroundAtom>,
    limits: Limits,
}
impl Current {
    fn new(selected: &[AtomKey], exclusive: bool) -> Self {
        let mut corpus = denotate_ir::Corpus::new();
        let mut keys = denotate_ir::SemanticKeys::default();
        let mut atoms = BTreeMap::new();
        for (i, key) in selected.iter().enumerate() {
            let id = corpus
                .declare_relation(format!("i{i}"), denotate_ir::RelationRole::Input, [])
                .unwrap();
            keys.bind_relation(&corpus, id, key.relation.clone())
                .unwrap();
            atoms.insert(key.clone(), GroundAtom::new(id, []));
        }
        let limits = Limits {
            max_work: usize::MAX,
            timeout: std::time::Duration::from_secs(60),
            ..Limits::default()
        };
        let mut program = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
        program.input_order = Some(atoms.values().cloned().collect());
        if exclusive {
            program.input_groups = vec![atoms.values().cloned().collect()];
        }
        Self {
            program,
            keys,
            atoms,
            limits,
        }
    }
    fn context(&self) -> ConditionContext {
        ConditionContext::build_selected(
            &self.program,
            Some(&self.program.inputs),
            &mut Budget::tracked(&self.limits),
        )
        .unwrap()
    }
    fn evaluate(&self, ctx: &ConditionContext) -> Condition {
        let atoms = self.atoms.values().collect::<Vec<_>>();
        let mut budget = Budget::tracked(&self.limits);
        let mut value = ctx.false_condition();
        for pair in atoms.chunks(2) {
            let left = ctx.input_with_budget(pair[0], &mut budget).unwrap();
            let term = if pair.len() == 2 {
                let right = ctx.input_with_budget(pair[1], &mut budget).unwrap();
                ctx.apply(&left, &right, op_function::and_not, &mut budget)
                    .unwrap()
            } else {
                left
            };
            value = ctx
                .apply(&value, &term, op_function::or, &mut budget)
                .unwrap();
        }
        ctx.restrict(&value, &mut budget).unwrap()
    }
}

#[test]
fn portable_transfer_preserves_worlds_and_canonical_witnesses() {
    let selected: Vec<_> = ["a", "f", "h"]
        .into_iter()
        .map(|name| AtomKey {
            relation: RelationKey::Named(QualifiedKey::new("portable-test", name)),
            arguments: vec![],
        })
        .collect();
    for exclusive in [false, true] {
        let current = Current::new(&selected, exclusive);
        let ctx = current.context();
        let condition = current.evaluate(&ctx);
        let exported = ctx
            .export(
                &condition,
                &current.keys,
                &mut Budget::tracked(&current.limits),
            )
            .unwrap();
        // Rebuild the arena and context: the portable value must not retain IDs.
        let rebuilt = Current::new(&selected, exclusive);
        let target = rebuilt.context();
        let imported = target
            .import(
                &exported,
                &rebuilt.atoms,
                &mut Budget::tracked(&rebuilt.limits),
            )
            .unwrap();
        let mut satisfying = Vec::new();
        for bits in 0u32..8 {
            let world: Vec<_> = (0..3).map(|i| bits & (1 << i) != 0).collect();
            let expected =
                ((world[0] && !world[1]) || world[2]) && (!exclusive || bits.count_ones() <= 1);
            let present: BTreeSet<_> = selected
                .iter()
                .zip(&world)
                .filter(|(_, yes)| **yes)
                .map(|(key, _)| key.clone())
                .collect();
            assert_eq!(exported.value_in(&present).unwrap(), expected);
            let atoms = present.iter().map(|key| rebuilt.atoms[key].clone());
            let evaluated = target.evaluate(&imported, atoms, &rebuilt.limits);
            if exclusive && bits.count_ones() > 1 {
                assert!(matches!(evaluated, Err(CheckError::InvalidInputGroup(_))));
            } else {
                assert_eq!(evaluated.unwrap(), expected);
            }
            if expected {
                satisfying.push(world);
            }
        }
        // The contract is absent-first AtomKey order, not a recorded witness.
        let expected = satisfying.into_iter().min().unwrap();
        for (context, value, keys, limits) in [
            (&ctx, &condition, &current.keys, &current.limits),
            (&target, &imported, &rebuilt.keys, &rebuilt.limits),
        ] {
            let witness = context.witness(value, limits).unwrap().unwrap();
            let present: BTreeSet<_> = witness
                .present
                .iter()
                .map(|a| AtomKey::from_atom(keys, a).unwrap())
                .collect();
            assert_eq!(
                selected
                    .iter()
                    .map(|key| present.contains(key))
                    .collect::<Vec<_>>(),
                expected
            );
        }
    }
}
