//! Deterministic sparse rounds, preserving producer order within each round.
use super::*;
pub(super) struct Schedule {
    readers: BTreeMap<usize, Vec<usize>>,
    current: BTreeSet<usize>,
    next: BTreeSet<usize>,
    pub nodes: usize,
    rules: usize,
}
impl Schedule {
    pub fn build(
        program: &GroundProgram,
        index: usize,
        retained: usize,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Self>> {
        let rules = &program.component_rules[index];
        // Current/next ready sets and rule slots. This is optional scheduling
        // metadata; an unavailable reservation leaves the original scan usable.
        let mut nodes = rules.len().saturating_mul(3);
        let room = budget.limits.max_condition_nodes.saturating_sub(retained);
        if nodes > room {
            return Ok(None);
        }
        let mut readers = BTreeMap::<usize, Vec<usize>>::new();
        for (local, rule) in rules.iter().enumerate() {
            budget.tick("symbolic scheduling")?;
            for literal in program.rules[*rule].dependency_literals() {
                budget.tick("symbolic scheduling")?;
                let Some(&atom) = program.atom_index.get(&literal.term.atom) else {
                    continue;
                };
                if program.atom_components[atom].index != index {
                    continue;
                }
                nodes = nodes.saturating_add(if readers.contains_key(&atom) { 1 } else { 3 });
                if nodes > room {
                    return Ok(None);
                }
                readers.entry(atom).or_default().push(local);
            }
        }
        budget.charge(rules.len(), "symbolic scheduling")?;
        Ok(Some(Self {
            readers,
            current: (0..rules.len()).collect(),
            next: BTreeSet::new(),
            nodes,
            rules: rules.len(),
        }))
    }
    pub fn pop(&mut self) -> Option<usize> {
        self.current.pop_first()
    }
    pub fn changed(&mut self, atom: usize, position: usize, budget: &mut Budget<'_>) -> Result<()> {
        if let Some(readers) = self.readers.get(&atom) {
            for &reader in readers {
                budget.tick("symbolic scheduling")?;
                if reader > position {
                    self.current.insert(reader);
                } else {
                    self.next.insert(reader);
                }
            }
        }
        Ok(())
    }
    pub fn next_round(&mut self) -> bool {
        std::mem::swap(&mut self.current, &mut self.next);
        !self.current.is_empty()
    }
    pub fn restart(&mut self, budget: &mut Budget<'_>) -> Result<()> {
        budget.charge(self.rules, "symbolic scheduling")?;
        self.current = (0..self.rules).collect();
        self.next.clear();
        Ok(())
    }
}
