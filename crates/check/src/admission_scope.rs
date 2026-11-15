//! Snapshot-local proof targets and their complete provider closure.
use crate::{
    limits::{Budget, Result},
    *,
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct AdmissionScope {
    pub targets: BTreeSet<GroundRuleId>,
    pub cone: DependencyCone,
}
impl AdmissionScope {
    /// Provider-first levels of target components, with size/order ties. Settled
    /// providers transmit the level but do not add a turn. IDs live only until
    /// this snapshot commits; retries are keyed by a component's representative.
    pub fn ordered_targets(
        &self,
        p: &GroundProgram,
        budget: &mut Budget<'_>,
    ) -> Result<Vec<(ComponentId, BTreeSet<GroundRuleId>)>> {
        let mut groups = BTreeMap::<_, BTreeSet<_>>::new();
        for id in &self.targets {
            budget.tick("component schedule")?;
            let rule = p.rule(*id).expect("live target");
            groups
                .entry(p.component_for(&rule.head.atom)?.id)
                .or_default()
                .insert(*id);
        }
        let mut levels = BTreeMap::new();
        // Graph analysis numbers every provider before its consumers.
        for id in &self.cone.components {
            let c = p.component(*id).expect("scoped component");
            budget.charge(1 + c.dependencies.len(), "component schedule")?;
            let level = c.dependencies.iter().map(|d| levels[d]).max().unwrap_or(0);
            levels.insert(*id, level + usize::from(groups.contains_key(id)));
        }
        let mut groups = groups.into_iter().collect::<Vec<_>>();
        groups.sort_by_key(|(id, _)| (levels[id], p.components[id.index].atoms.len(), *id));
        Ok(groups)
    }

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
