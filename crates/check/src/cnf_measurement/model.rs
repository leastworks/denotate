use super::*;
use denotate_ir::Cardinality;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Binding {
    Atom(usize),
    Constant(bool),
}
#[derive(Clone)]
pub(super) struct Model {
    pub atoms: Vec<GroundAtom>,
    pub inputs: Vec<bool>,
    pub recursive: Vec<bool>,
    pub order: Vec<usize>,
    pub rank: Vec<usize>,
    pub group_for: Vec<Vec<usize>>,
    pub bodies: Vec<Vec<Vec<i32>>>,
    pub groups: Vec<(Cardinality, Vec<usize>, RelationId)>,
    pub binding: Vec<Binding>,
}
pub(super) fn atom(lit: i32) -> usize {
    lit.unsigned_abs() as usize - 1
}
pub(super) fn literal(id: usize) -> i32 {
    (id + 1) as i32
}
impl Model {
    pub fn new(p: &GroundProgram, b: &mut Budget<'_>) -> Result<Self> {
        b.charge(p.core.atoms.len(), "CNF model")?;
        if p.core.atoms.len() >= i32::MAX as usize {
            return Err(CheckError::InvalidRequest("CNF model too large"));
        }
        let atoms = p.core.atoms.clone();
        let index: BTreeMap<_, _> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
        let mut bodies = vec![BTreeSet::new(); atoms.len()];
        for r in &p.core.rules {
            b.tick("CNF model")?;
            let mut body = Vec::new();
            let mut dead = false;
            for l in &r.body {
                b.tick("CNF model")?;
                let positive = l.polarity == Polarity::Positive;
                if let Some(v) = p.fixed_value(&l.term.atom) {
                    if v != positive {
                        dead = true;
                        break;
                    }
                } else if let Some(i) = index.get(&l.term.atom) {
                    body.push(if positive { literal(*i) } else { -literal(*i) });
                } else if positive {
                    dead = true;
                    break;
                }
            }
            if !dead {
                if let Some(body) = normalize(body) {
                    bodies[index[&r.head.atom]].insert(body);
                }
            }
        }
        let order: Vec<usize> = p
            .core
            .components
            .iter()
            .flat_map(|c| c.atoms.iter().map(|a| index[a]))
            .collect();
        let mut rank = vec![0; atoms.len()];
        for (i, a) in order.iter().enumerate() {
            rank[*a] = i;
        }
        let recursive = atoms
            .iter()
            .map(|a| p.component_for(a).map(|c| c.recursive))
            .collect::<Result<_>>()?;
        let inputs = atoms.iter().map(|a| p.inputs.contains(a)).collect();
        let groups: Vec<(Cardinality, Vec<usize>, RelationId)> = p
            .universe_groups
            .iter()
            .map(|g| {
                (
                    g.kind,
                    g.atoms.iter().map(|a| index[a]).collect(),
                    g.relation,
                )
            })
            .collect();
        let mut group_for = vec![vec![]; atoms.len()];
        for (i, (_, group, _)) in groups.iter().enumerate() {
            b.charge(group.len() + 1, "CNF group index")?;
            for a in group {
                group_for[*a].push(i);
            }
        }
        Ok(Self {
            rank,
            group_for,
            binding: (0..atoms.len()).map(Binding::Atom).collect(),
            atoms,
            inputs,
            recursive,
            order,
            bodies: bodies
                .into_iter()
                .map(|x| x.into_iter().collect())
                .collect(),
            groups,
        })
    }
    /// Vector capacities only; excludes map/set scratch, the original graph and allocator overhead.
    pub fn vector_bytes(&self) -> usize {
        use std::mem::size_of;
        self.atoms.capacity() * size_of::<GroundAtom>()
            + self
                .atoms
                .iter()
                .map(|a| a.arguments.capacity() * size_of::<denotate_ir::ConstantId>())
                .sum::<usize>()
            + self.inputs.capacity()
            + self.recursive.capacity()
            + (self.order.capacity() + self.rank.capacity()) * size_of::<usize>()
            + self.binding.capacity() * size_of::<Binding>()
            + self.group_for.capacity() * size_of::<Vec<usize>>()
            + self
                .group_for
                .iter()
                .map(|g| g.capacity() * size_of::<usize>())
                .sum::<usize>()
            + self.groups.capacity()
                * size_of::<(denotate_ir::Cardinality, Vec<usize>, RelationId)>()
            + self
                .groups
                .iter()
                .map(|(_, g, _)| g.capacity() * size_of::<usize>())
                .sum::<usize>()
            + self.bodies.capacity() * size_of::<Vec<Vec<i32>>>()
            + self
                .bodies
                .iter()
                .map(|bs| {
                    bs.capacity() * size_of::<Vec<i32>>()
                        + bs.iter().map(|b| b.capacity() * 4).sum::<usize>()
                })
                .sum::<usize>()
    }
    pub fn resolve(&self, mut id: usize) -> Binding {
        loop {
            match self.binding[id] {
                Binding::Atom(next) if next != id => id = next,
                value => return value,
            }
        }
    }
    pub fn body(&self, body: &[i32], b: &mut Budget<'_>) -> Result<Option<Vec<i32>>> {
        let mut result = Vec::new();
        for l in body {
            b.tick("CNF substitution")?;
            match self.resolve(atom(*l)) {
                Binding::Constant(v) if v != (*l > 0) => return Ok(None),
                Binding::Constant(_) => (),
                Binding::Atom(a) => result.push(if *l > 0 { literal(a) } else { -literal(a) }),
            }
        }
        Ok(normalize(result))
    }
    pub fn definitions(&self, h: usize, b: &mut Budget<'_>) -> Result<Vec<Vec<i32>>> {
        let mut result = BTreeSet::new();
        for body in &self.bodies[h] {
            if let Some(body) = self.body(body, b)? {
                result.insert(body);
            }
        }
        if result.contains(&Vec::new()) {
            return Ok(vec![vec![]]);
        }
        Ok(result.into_iter().collect())
    }
    pub fn eligible(&self, h: usize) -> bool {
        !self.inputs[h] && !self.recursive[h] && self.binding[h] == Binding::Atom(h)
    }
    pub fn encode(&self, b: &mut Budget<'_>) -> Result<(Cnf, Vec<usize>)> {
        let mut cnf = Cnf::default();
        let mut vars = BTreeMap::new();
        for (i, a) in self.atoms.iter().enumerate() {
            b.tick("CNF measurement")?;
            if self.resolve(i) != Binding::Atom(i) {
                continue;
            }
            let l = cnf.var(a.relation, true, b)?;
            if self.inputs[i] || self.recursive[i] {
                cnf.protected.insert(l as usize - 1);
            }
            vars.insert(i, l);
        }
        let mut readers = vec![BTreeSet::new(); self.atoms.len()];
        let mut definitions = vec![Vec::new(); self.atoms.len()];
        for (&h, _) in &vars {
            if self.inputs[h] {
                continue;
            }
            definitions[h] = self.definitions(h, b)?;
            for body in &definitions[h] {
                for l in body {
                    readers[atom(*l)].insert(h);
                }
            }
        }
        let mut candidates = Vec::new();
        for (&h, &head) in &vars {
            b.tick("CNF measurement")?;
            if self.inputs[h] {
                continue;
            }
            let defs = &definitions[h];
            let owner = self.atoms[h].relation;
            if defs.len() == 1 && readers[h].len() == 1 && !readers[h].contains(&h) {
                candidates.push(head as usize - 1);
            }
            let remap = |l: &i32| {
                if *l > 0 {
                    vars[&atom(*l)]
                } else {
                    -vars[&atom(*l)]
                }
            };
            if defs.len() == 1 {
                for l in &defs[0] {
                    cnf.clause(vec![-head, remap(l)], owner, b)?;
                }
                cnf.clause(
                    std::iter::once(head)
                        .chain(defs[0].iter().map(|l| -remap(l)))
                        .collect(),
                    owner,
                    b,
                )?;
                continue;
            }
            let mut producers = Vec::new();
            for body in defs {
                let term = if body.len() == 1 {
                    remap(&body[0])
                } else {
                    let aux = cnf.var(owner, false, b)?;
                    for l in body {
                        cnf.clause(vec![-aux, remap(l)], owner, b)?;
                    }
                    cnf.clause(
                        std::iter::once(aux)
                            .chain(body.iter().map(|l| -remap(l)))
                            .collect(),
                        owner,
                        b,
                    )?;
                    aux
                };
                producers.push(term);
                cnf.clause(vec![-term, head], owner, b)?;
            }
            cnf.clause(std::iter::once(-head).chain(producers).collect(), owner, b)?;
        }
        for (kind, group, owner) in &self.groups {
            let lits: Vec<_> = group.iter().map(|a| vars[a]).collect();
            if kind.has_coverage() {
                cnf.clause(lits.clone(), *owner, b)?;
            }
            if kind.has_uniqueness() {
                // Same size policy as sat_probe::Cnf::at_most_one: pairwise
                // through five, then one-way sequential prefix implications.
                if lits.len() <= 5 {
                    for (i, l) in lits.iter().enumerate() {
                        for r in &lits[i + 1..] {
                            cnf.clause(vec![-l, -r], *owner, b)?;
                        }
                    }
                } else {
                    let mut prev = lits[0];
                    for l in &lits[1..lits.len() - 1] {
                        cnf.clause(vec![-prev, -l], *owner, b)?;
                        let next = cnf.var(*owner, false, b)?;
                        cnf.clause(vec![-prev, next], *owner, b)?;
                        cnf.clause(vec![-l, next], *owner, b)?;
                        prev = next;
                    }
                    cnf.clause(vec![-prev, -lits[lits.len() - 1]], *owner, b)?;
                }
            }
        }
        Ok((cnf, candidates))
    }
}
