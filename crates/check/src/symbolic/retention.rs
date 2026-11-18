//! Admission's final readers plus last-use release during symbolic evaluation.
use super::*;

pub(crate) struct Retention {
    releases: BTreeMap<usize, Vec<GroundAtom>>,
    pub nodes: usize,
}
impl Retention {
    pub fn build(
        program: &GroundProgram,
        cone: &DependencyCone,
        keep: &BTreeSet<GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let mut last = BTreeMap::new();
        for id in &cone.components {
            let component = &program.components[id.index];
            for atom in &component.atoms {
                budget.tick("symbolic retention plan")?;
                if !keep.contains(atom) {
                    last.insert(atom.clone(), id.index);
                }
            }
            for index in &program.component_rules[id.index] {
                for literal in program.rules[*index].dependency_literals() {
                    budget.tick("symbolic retention readers")?;
                    let atom = literal.term.atom;
                    if !keep.contains(&atom) {
                        last.entry(atom)
                            .and_modify(|n| *n = (*n).max(id.index))
                            .or_insert(id.index);
                    }
                }
            }
        }
        // Last-use map, release schedule, and released-atom sentinels. Conservatively
        // keep this bookkeeping charge through the snapshot; no BDD is hidden here.
        let nodes = last.len().saturating_mul(3);
        retain(0, 0, nodes, budget)?;
        let mut releases = BTreeMap::<_, Vec<_>>::new();
        for (atom, index) in last {
            budget.tick("symbolic retention schedule")?;
            releases.entry(index).or_default().push(atom);
        }
        Ok(Self { releases, nodes })
    }

    pub fn before<const W: bool>(
        &mut self,
        index: usize,
        meaning: &mut SymbolicMeaning<'_, W>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        while self
            .releases
            .first_key_value()
            .is_some_and(|(last, _)| *last < index)
        {
            let (_, atoms) = self.releases.pop_first().unwrap();
            for atom in atoms {
                budget.tick("symbolic condition release")?;
                if let Some(value) = meaning.conditions.remove(&atom) {
                    *retained -= value.node_count();
                    meaning.released.insert(atom);
                }
            }
        }
        Ok(())
    }
}
