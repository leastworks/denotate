//! Snapshot-local proof targets and their complete provider closure.
use crate::{
    limits::{Budget, Result},
    *,
};
use std::collections::BTreeSet;

pub(crate) struct AdmissionScope {
    pub targets: BTreeSet<GroundRuleId>,
    pub cone: DependencyCone,
}
impl AdmissionScope {
    pub fn build(
        p: &GroundProgram,
        phase: AdmissionPhase,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let mut relevant = BTreeSet::new();
        let mut pending = Vec::new();
        for c in &p.components {
            budget.tick("admission scope")?;
            if c.cycle.is_some() {
                pending.push(c.id);
            }
        }
        while let Some(id) = pending.pop() {
            budget.tick("admission scope")?;
            if relevant.insert(id) {
                pending.extend(&p.components[id.index].dependencies);
            }
        }
        let mut targets = BTreeSet::new();
        let mut roots = BTreeSet::new();
        for c in &p.components {
            let blocked = !c.blocked_by.is_empty();
            let target = match phase {
                AdmissionPhase::Relevant => blocked && relevant.contains(&c.id),
                AdmissionPhase::Downstream => blocked && !relevant.contains(&c.id),
            };
            let input_guards = phase == AdmissionPhase::Downstream
                && !blocked
                && (!p.input_groups.is_empty() || p.assumption_condition.is_some());
            if !target && !input_guards {
                continue;
            }
            for index in &p.component_rules[c.id.index] {
                budget.tick("admission targets")?;
                let rule = &p.rules[*index];
                if target
                    || rule.body.iter().any(|l| {
                        l.polarity == Polarity::Negative && p.inputs.contains(&l.term.atom)
                    })
                {
                    targets.insert(rule.id);
                    roots.insert(c.id);
                }
            }
        }
        let mut cone = DependencyCone {
            roots: BTreeSet::new(),
            facts: BTreeSet::new(),
            rules: BTreeSet::new(),
            components: BTreeSet::new(),
            blocked_by: BTreeSet::new(),
        };
        let mut pending: Vec<_> = roots.into_iter().collect();
        while let Some(id) = pending.pop() {
            budget.tick("admission support")?;
            if !cone.components.insert(id) {
                continue;
            }
            let c = &p.components[id.index];
            cone.blocked_by.extend(&c.blocked_by);
            cone.facts.extend(c.atoms.iter().cloned());
            pending.extend(&c.dependencies);
            for index in &p.component_rules[id.index] {
                let rule = &p.rules[*index];
                budget.charge(1 + rule.body.len(), "admission support")?;
                cone.rules.insert(rule.id);
                // Includes impossible and folded boundary atoms, which do not
                // necessarily have executable components in this graph.
                cone.facts
                    .extend(rule.dependency_literals().map(|l| l.term.atom));
            }
        }
        Ok(Self { targets, cone })
    }
}
