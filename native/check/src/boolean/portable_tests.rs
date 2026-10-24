//! Production portable conditions checked against exhaustive Boolean worlds.
use super::*;
use denotate_ir::{QualifiedKey, RelationKey};

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
