use super::*;
#[derive(Clone)]
pub(super) struct Group {
    pub atoms: Vec<usize>,
    pub exact: bool,
    pub assumption: Option<denotate_ir::AssumptionId>,
    pub mapping: Vec<(usize, usize)>,
}
pub(super) fn groups(
    e: &Engine,
    state: &fitting::Bundle,
    b: &mut Budget<'_>,
) -> Result<Vec<Group>> {
    let mut out = vec![];
    for (kind, atoms) in &e.world.groups {
        b.charge(atoms.len() + 1, "completion split groups")?;
        if matches!(kind, Cardinality::AtMostOne | Cardinality::ExactlyOne)
            && atoms.iter().all(|i| e.cone.input[*i])
        {
            out.push(Group {
                atoms: atoms.clone(),
                exact: *kind == Cardinality::ExactlyOne,
                assumption: None,
                mapping: atoms.iter().map(|i| (*i, *i)).collect(),
            });
        }
    }
    for (a, s) in e.assumptions.iter().zip(&state.assumptions) {
        if !matches!(a.kind, Cardinality::AtMostOne | Cardinality::ExactlyOne) {
            continue;
        }
        for (_, members) in &a.groups {
            let mut inputs = BTreeSet::new();
            let mut mapping = vec![];
            let mut valid = true;
            for i in members {
                b.tick("completion split certificate")?;
                if s.value(*i) == Some(false) {
                    continue;
                }
                if s.value(*i) == Some(true) {
                    valid = false;
                    break;
                }
                let input = if s.source().input[*i] {
                    Some(*i)
                } else if let Some(r) = s.producer(*i) {
                    let body = &s.source().rules[r].body;
                    b.charge(body.len(), "completion split certificate")?;
                    let unknown: Vec<_> =
                        body.iter().filter(|(j, _)| s.value(*j).is_none()).collect();
                    if unknown.len() == 1 && unknown[0].1 && s.source().input[unknown[0].0] {
                        Some(unknown[0].0)
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(j) = input {
                    if !inputs.insert(j) {
                        valid = false;
                        break;
                    }
                    mapping.push((*i, j));
                } else {
                    valid = false;
                    break;
                }
            }
            if valid && !inputs.is_empty() {
                out.push(Group {
                    atoms: inputs.into_iter().collect(),
                    exact: a.kind == Cardinality::ExactlyOne,
                    assumption: Some(a.id),
                    mapping,
                });
            }
        }
    }
    Ok(out)
}
#[derive(Clone)]
pub(super) struct Choice {
    pub group: Group,
    pub selected: Vec<usize>,
    pub rest: bool,
    pub score: usize,
    pub binary: bool,
}
impl Choice {
    pub fn children(&self) -> Vec<(Vec<(usize, bool)>, bool)> {
        let mut children = vec![];
        for chosen in &self.selected {
            children.push((
                self.group
                    .atoms
                    .iter()
                    .map(|i| (*i, *i == *chosen))
                    .collect(),
                false,
            ));
        }
        if self.rest {
            children.push((self.selected.iter().map(|i| (*i, false)).collect(), true));
        }
        children
    }
}
