//! Dependencies sufficient to reuse one search outcome across input worlds.
use crate::{
    Condition, ConditionContext, GroundAtom, GroundProgram, Observation,
    limits::{Budget, Result},
};
use biodivine_lib_bdd::op_function;
use std::collections::BTreeSet;

pub(crate) struct CertificationDependencies {
    inputs: BTreeSet<GroundAtom>,
}

impl CertificationDependencies {
    pub(crate) fn new(
        program: &GroundProgram,
        targets: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let mut roots = BTreeSet::new();
        for target in targets {
            budget.tick("certification search dependencies")?;
            roots.insert(target);
        }
        // Certification succeeds only if the WHOLE residual program completes.
        // Include every initially blocked component, not just the target's
        // blockers. Pruning only removes rules: later rounds cannot introduce a
        // dependency outside these structural cones. The targets additionally
        // preserve the tuple/group truth after successful certification or replay.
        for component in program.components() {
            budget.tick("certification search dependencies")?;
            if !component.blocked_by.is_empty() {
                for atom in &component.atoms {
                    budget.tick("certification search dependencies")?;
                    roots.insert(atom.clone());
                }
            }
        }
        // This is correctness-critical, unlike the optional diagnostic annotation.
        // Propagate exhaustion; a partial set must never stand for an empty cone.
        let inputs = program.dependency_inputs_with_budget(roots, budget)?;
        Ok(Self { inputs })
    }

    pub(crate) fn exclude(
        &self,
        context: &ConditionContext,
        remaining: &Condition,
        observation: &Observation,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        let mut cube = context.true_condition();
        for input in &self.inputs {
            let literal = context.input_with_budget(input, budget)?;
            cube = context.apply(
                &cube,
                &literal,
                if observation.present.contains(input) {
                    op_function::and
                } else {
                    op_function::and_not
                },
                budget,
            )?;
        }
        // remaining starts inside W. Subtracting a cube cannot introduce an
        // impermitted world, even when W correlates included and omitted inputs.
        context.apply(remaining, &cube, op_function::and_not, budget)
    }
}
