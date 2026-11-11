//! Canonical low-first postorder graph. Equality never performs Boolean solving.
use super::*;
use biodivine_lib_bdd::{BddNode, BddPointer};
use denotate_ir::SemanticKeys;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedCondition {
    inputs: Arc<[AtomKey]>,
    // Terminals are 0/1. Every other link points backward into this vector (+2).
    nodes: Vec<(usize, usize, usize)>,
    root: usize,
}
impl OwnedCondition {
    pub(crate) fn value_in(&self, present: &BTreeSet<AtomKey>) -> Result<bool> {
        let mut node = self.root;
        while node > 1 {
            let (var, low, high) = self.nodes[node - 2];
            node = if present.contains(&self.inputs[var]) {
                high
            } else {
                low
            };
        }
        Ok(node == 1)
    }
    pub fn inputs(&self) -> &[AtomKey] {
        &self.inputs
    }
    /// Allocated graph payload for session retention accounting, excluding Arc keys.
    pub fn retained_node_capacity(&self) -> usize {
        self.nodes.capacity()
    }
    pub fn node_count(&self) -> usize {
        self.nodes.len() + 2
    }
}
impl ConditionContext {
    pub(crate) fn export(
        &self,
        condition: &Condition,
        keys: &SemanticKeys,
        budget: &mut Budget<'_>,
    ) -> Result<OwnedCondition> {
        self.check(condition, budget)?;
        budget.charge(self.inputs.len(), "local condition export")?;
        let mut inputs: Vec<_> = self
            .inputs
            .iter()
            .map(|(a, v)| {
                Ok((
                    v.to_index(),
                    AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?,
                ))
            })
            .collect::<Result<_>>()?;
        inputs.sort_by_key(|(v, _)| *v);
        let inputs: Arc<[AtomKey]> = inputs
            .into_iter()
            .map(|(_, k)| k)
            .collect::<Vec<_>>()
            .into();
        if inputs.windows(2).any(|w| w[0] >= w[1]) {
            return Err(CheckError::Internal(
                "local inputs are not in AtomKey order",
            ));
        }
        let bdd = &condition.bdd;
        let mut assigned = BTreeMap::from([(BddPointer::zero(), 0), (BddPointer::one(), 1)]);
        let mut pending = vec![(bdd.root_pointer(), false)];
        let mut nodes = Vec::new();
        while let Some((node, exit)) = pending.pop() {
            budget.tick("local condition export")?;
            if assigned.contains_key(&node) {
                continue;
            }
            let low = bdd.low_link_of(node);
            let high = bdd.high_link_of(node);
            if exit {
                nodes.push((bdd.var_of(node).to_index(), assigned[&low], assigned[&high]));
                assigned.insert(node, nodes.len() + 1);
            } else {
                pending.push((node, true));
                pending.push((high, false));
                pending.push((low, false));
            }
        }
        Ok(OwnedCondition {
            inputs,
            nodes,
            root: assigned[&bdd.root_pointer()],
        })
    }
    pub(crate) fn import(
        &self,
        value: &OwnedCondition,
        atoms: &BTreeMap<AtomKey, GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        budget.charge(
            value.inputs.len() + value.node_count(),
            "local condition import",
        )?;
        budget.observe("local condition import", "BDD nodes", value.node_count());
        if value.node_count() > budget.limits.max_bdd_nodes {
            return Err(limit(
                "local condition import",
                "BDD nodes",
                budget.limits.max_bdd_nodes,
                Some(value.node_count()),
            ));
        }
        let variables: Vec<_> = value
            .inputs
            .iter()
            .map(|key| {
                atoms
                    .get(key)
                    .and_then(|a| self.inputs.get(a))
                    .copied()
                    .ok_or(CheckError::Internal("missing imported input binding"))
            })
            .collect::<Result<_>>()?;
        if variables.windows(2).any(|w| w[0] >= w[1]) {
            return Err(CheckError::Internal("non-monotone local variable mapping"));
        }
        if value.root == 0 {
            return Ok(self.false_condition());
        }
        if value.root == 1 {
            return Ok(self.true_condition());
        }
        let mut nodes = vec![
            BddNode::mk_zero(self.variables.num_vars()),
            BddNode::mk_one(self.variables.num_vars()),
        ];
        for (var, low, high) in &value.nodes {
            nodes.push(BddNode::mk_node(
                variables[*var],
                BddPointer::from_index(*low),
                BddPointer::from_index(*high),
            ));
        }
        let bdd =
            Bdd::from_nodes(&nodes).map_err(|_| CheckError::Internal("invalid portable BDD"))?;
        Ok(self.wrap(bdd))
    }
}
