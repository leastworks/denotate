//! SAT search over the shared symbolic meaning, with fresh concrete replay by
//! the coverage caller. This encoding does not ask the BDD engine for a verdict.
use super::*;
use crate::local::sat::Encoding;
use biodivine_lib_bdd::BddPointer;
impl ConditionContext {
    pub(crate) fn sat_witness(
        &self,
        condition: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Observation>> {
        let condition = self.restrict(condition, budget)?;
        budget.charge(self.inputs.len(), "coverage SAT inputs")?;
        let mut enc = Encoding::new(&OperationalLimits::from(budget.limits));
        let inputs = self
            .inputs
            .iter()
            .map(|(a, v)| Ok((*v, (a, enc.var()?))))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let no = enc.var()?;
        enc.clause(vec![!no])?;
        let mut nodes = BTreeMap::from([(BddPointer::zero(), no), (BddPointer::one(), !no)]);
        let bdd = &condition.bdd;
        let mut pending = vec![(bdd.root_pointer(), false)];
        while let Some((node, exit)) = pending.pop() {
            budget.charge(6, "coverage SAT encoding")?;
            if nodes.contains_key(&node) {
                continue;
            }
            let low = bdd.low_link_of(node);
            let high = bdd.high_link_of(node);
            if exit {
                let v = inputs[&bdd.var_of(node)].1;
                let n = enc.var()?;
                let (l, h) = (nodes[&low], nodes[&high]);
                enc.clause(vec![!v, !n, h])?;
                enc.clause(vec![!v, n, !h])?;
                enc.clause(vec![v, !n, l])?;
                enc.clause(vec![v, n, !l])?;
                nodes.insert(node, n);
            } else {
                pending.push((node, true));
                pending.push((high, false));
                pending.push((low, false));
            }
        }
        enc.clause(vec![nodes[&bdd.root_pointer()]])?;
        if !enc.solve(&[])? {
            return Ok(None);
        }
        let mut assumptions = Vec::new();
        let mut world = Observation {
            present: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for (atom, lit) in inputs.values() {
            budget.tick("coverage SAT witness")?;
            assumptions.push(!*lit);
            if enc.solve(&assumptions)? {
                world.absent.insert((*atom).clone());
            } else {
                *assumptions.last_mut().unwrap() = *lit;
                world.present.insert((*atom).clone());
            }
        }
        Ok(Some(world))
    }
}
