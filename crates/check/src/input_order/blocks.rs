//! Declared cardinalities partition inputs; selected assumptions do not.
use super::*;

pub(super) fn scattered(
    program: &GroundProgram,
    ordered: &[GroundAtom],
    budget: &mut Budget<'_>,
) -> Result<usize> {
    if !program.universe_groups.iter().any(|g| g.atoms.len() > 1) {
        return Ok(0);
    }
    budget.charge(ordered.len(), "declared input blocks")?;
    let positions: BTreeMap<_, _> = ordered.iter().enumerate().map(|(i, a)| (a, i)).collect();
    let mut scattered = 0;
    for group in &program.universe_groups {
        budget.charge(1 + group.atoms.len(), "declared input blocks")?;
        if group.atoms.len() > 1 {
            let first = group.atoms.iter().map(|a| positions[a]).min().unwrap();
            let last = group.atoms.iter().map(|a| positions[a]).max().unwrap();
            scattered += usize::from(last - first + 1 != group.atoms.len());
        }
    }
    Ok(scattered)
}

pub(super) struct Blocks {
    pub members: Vec<Vec<usize>>,
    pub input_to_block: Vec<usize>,
    pub declared: usize,
}
impl Blocks {
    pub fn build(
        program: &GroundProgram,
        ordered: &[GroundAtom],
        budget: &mut Budget<'_>,
    ) -> Result<Option<Self>> {
        if !program.universe_groups.iter().any(|g| g.atoms.len() > 1) {
            return Ok(None);
        }
        // This baseline is mandatory for structural order, even if the optional
        // FORCE allowance is zero. Ground/input limits bound its O(inputs) storage.
        let mut membership = BTreeMap::new();
        let mut declared = 0;
        for (i, g) in program.universe_groups.iter().enumerate() {
            budget.tick("declared input blocks")?;
            if g.atoms.len() <= 1 {
                continue;
            }
            declared += 1;
            for atom in &g.atoms {
                budget.tick("declared input blocks")?;
                if membership.insert(atom, i).is_some() {
                    return Err(CheckError::Internal("overlapping declared input groups"));
                }
            }
        }
        let mut groups = BTreeMap::new();
        let mut members: Vec<Vec<usize>> = Vec::new();
        let mut input_to_block = Vec::with_capacity(ordered.len());
        for (i, atom) in ordered.iter().enumerate() {
            budget.tick("declared input blocks")?;
            let block = if let Some(group) = membership.get(atom) {
                *groups.entry(*group).or_insert_with(|| {
                    members.push(Vec::new());
                    members.len() - 1
                })
            } else {
                members.push(Vec::new());
                members.len() - 1
            };
            members[block].push(i);
            input_to_block.push(block);
        }
        // Both block IDs (first/minimum member) and members are in semantic-key
        // order, regardless of declaration/arena order or grouping column order.
        Ok(Some(Self {
            members,
            input_to_block,
            declared,
        }))
    }
    pub fn flatten(&self, order: impl IntoIterator<Item = usize>) -> Vec<usize> {
        order
            .into_iter()
            .flat_map(|i| self.members[i].iter().copied())
            .collect()
    }
}
