use super::*;
use biodivine_lib_bdd::{
    Bdd, BddVariable, BddVariableSet,
    op_function::{and, and_not, or},
};

#[derive(Clone, Copy)]
pub(super) enum Question<'a> {
    Constant(usize),
    Dead(&'a [i32]),
    Implied(&'a [i32], i32),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Answer {
    No,
    Yes,
    Constant(bool),
}
fn cutoff(resource: &'static str, limit: usize) -> CheckError {
    CheckError::limit("CNF local proof", resource, limit, None)
}
#[derive(Debug, Default)]
pub struct ProofShape {
    pub cone_atoms: usize,
    pub definitions: usize,
    pub cut_points: usize,
    pub groups: usize,
    pub omitted_groups: usize,
    pub bdd_nodes_created: usize,
}
struct Ops<'a, 'b> {
    shape: &'a mut ProofShape,
    b: &'a mut Budget<'b>,
    nodes: usize,
    max: usize,
}
impl Ops<'_, '_> {
    fn own(&mut self, x: Bdd) -> Result<Bdd> {
        self.nodes = self.nodes.saturating_add(x.size());
        self.shape.bdd_nodes_created = self.nodes;
        if self.nodes > self.max {
            return Err(cutoff("BDD nodes created", self.max));
        }
        self.b.charge(x.size(), "CNF local BDD")?;
        Ok(x)
    }
    fn apply(
        &mut self,
        a: &Bdd,
        b: &Bdd,
        op: fn(Option<bool>, Option<bool>) -> Option<bool>,
    ) -> Result<Bdd> {
        let allowance = (self.b.remaining() / 2).min(self.max.saturating_sub(self.nodes) / 4);
        let Some((_, tasks)) = Bdd::check_binary_op(allowance, a, b, op) else {
            self.b
                .charge(allowance.saturating_add(1), "CNF local BDD preflight")?;
            return Err(cutoff("BDD tasks", allowance));
        };
        self.b
            .charge(tasks.saturating_mul(2) + 1, "CNF local BDD")?;
        let Some(result) =
            Bdd::binary_op_with_limit(self.max.saturating_sub(self.nodes + 3 * tasks), a, b, op)
        else {
            return Err(cutoff("BDD nodes created", self.max));
        };
        self.own(result)
    }
    fn value(&mut self, values: &BTreeMap<usize, Bdd>, lit: i32) -> Result<Bdd> {
        let v = values
            .get(&atom(lit))
            .ok_or(CheckError::Internal("missing local proof value"))?;
        self.own(if lit > 0 { v.clone() } else { v.not() })
    }
    fn body(
        &mut self,
        values: &BTreeMap<usize, Bdd>,
        body: &[i32],
        vars: &BddVariableSet,
    ) -> Result<Bdd> {
        let mut value = self.own(vars.mk_true())?;
        for lit in body {
            let l = self.value(values, *lit)?;
            value = self.apply(&value, &l, and)?;
        }
        Ok(value)
    }
}
pub(super) fn prove(
    m: &Model,
    q: Question<'_>,
    limits: &SimplificationLimits,
    b: &mut Budget<'_>,
) -> Result<Answer> {
    prove_observed(m, q, limits, b, &mut ProofShape::default())
}
pub(super) fn prove_observed(
    m: &Model,
    q: Question<'_>,
    limits: &SimplificationLimits,
    b: &mut Budget<'_>,
    shape: &mut ProofShape,
) -> Result<Answer> {
    b.tick("CNF cone")?;
    let roots: Vec<_> = match q {
        Question::Constant(h) => vec![super::super::model::literal(h)],
        Question::Dead(body) | Question::Implied(body, _) => body.to_vec(),
    };
    let mut nodes = BTreeSet::new();
    let mut pending = BTreeSet::new();
    for l in &roots {
        if let Binding::Atom(a) = m.resolve(atom(*l)) {
            nodes.insert(a);
            pending.insert(a);
        }
    }
    if nodes.len() > limits.max_cone_atoms {
        return Err(cutoff("cone atoms", limits.max_cone_atoms));
    }
    let mut definitions = BTreeMap::new();
    while let Some(h) = pending.pop_first() {
        b.tick("CNF cone")?;
        if !m.eligible(h) {
            continue;
        }
        let defs = m.definitions(h, b)?;
        let deps: BTreeSet<_> = defs.iter().flatten().map(|l| atom(*l)).collect();
        if nodes.len() + deps.difference(&nodes).count() > limits.max_cone_atoms {
            continue;
        }
        for a in deps {
            if nodes.insert(a) {
                pending.insert(a);
            }
        }
        definitions.insert(h, defs);
    }
    let mut terminals: BTreeSet<_> = nodes
        .iter()
        .filter(|a| !definitions.contains_key(a))
        .copied()
        .collect();
    let mut groups = Vec::new();
    let relevant: BTreeSet<_> = terminals
        .iter()
        .flat_map(|a| m.group_for[*a].iter().copied())
        .collect();
    for index in relevant {
        b.tick("CNF local groups")?;
        let (kind, group, _) = &m.groups[index];
        if group.len() > limits.max_cone_atoms {
            shape.omitted_groups += 1;
            continue;
        }
        b.charge(group.len() + 1, "CNF local groups")?;
        // Whole group or no constraint. Dropping a large group weakens U safely;
        // truncating exactly-one would instead assert an unsound at-least-one.
        let extra = group.iter().filter(|a| !nodes.contains(a)).count();
        if nodes.len() + extra > limits.max_cone_atoms {
            shape.omitted_groups += 1;
            continue;
        }
        nodes.extend(group);
        terminals.extend(group);
        groups.push((*kind, group));
    }
    shape.cone_atoms = nodes.len();
    shape.definitions = definitions.len();
    shape.cut_points = terminals.len();
    shape.groups = groups.len();
    if terminals.len() >= u16::MAX as usize - 1 {
        return Err(cutoff("BDD variables", u16::MAX as usize - 2));
    }
    let variables = BddVariableSet::new_anonymous(terminals.len() as u16);
    let mut ops = Ops {
        shape,
        b,
        nodes: 0,
        max: limits.max_bdd_nodes,
    };
    let mut values = BTreeMap::new();
    for (i, a) in terminals.iter().enumerate() {
        values.insert(*a, ops.own(variables.mk_var(BddVariable::from_index(i)))?);
    }
    let mut u = ops.own(variables.mk_true())?;
    for (kind, group) in groups {
        let mut seen = ops.own(variables.mk_false())?;
        for a in group {
            let value = ops.value(&values, super::super::model::literal(*a))?;
            if kind.has_uniqueness() {
                let conflict = ops.apply(&seen, &value, and)?;
                u = ops.apply(&u, &conflict, and_not)?;
            }
            seen = ops.apply(&seen, &value, or)?;
        }
        if kind.has_coverage() {
            u = ops.apply(&u, &seen, and)?;
        }
    }
    // No vacuous constants if this local context is empty.
    if u.is_false() {
        return Ok(Answer::No);
    }
    let mut ordered: Vec<_> = definitions.keys().copied().collect();
    ordered.sort_by_key(|h| m.rank[*h]);
    for h in ordered {
        let defs = &definitions[&h];
        let mut value = ops.own(variables.mk_false())?;
        for body in defs {
            let term = ops.body(&values, body, &variables)?;
            value = ops.apply(&value, &term, or)?;
        }
        values.insert(h, value);
    }
    let resolved = |l: i32| match m.resolve(atom(l)) {
        Binding::Atom(a) => Some(if l > 0 {
            super::super::model::literal(a)
        } else {
            -super::super::model::literal(a)
        }),
        Binding::Constant(_) => None,
    };
    match q {
        Question::Constant(h) => {
            let f = &values[&h];
            if ops.apply(&u, f, and)?.is_false() {
                Ok(Answer::Constant(false))
            } else if ops.apply(&u, f, and_not)?.is_false() {
                Ok(Answer::Constant(true))
            } else {
                Ok(Answer::No)
            }
        }
        Question::Dead(body) => {
            let Some(body) = m.body(body, ops.b)? else {
                return Ok(Answer::Yes);
            };
            let f = ops.body(&values, &body, &variables)?;
            Ok(if ops.apply(&u, &f, and)?.is_false() {
                Answer::Yes
            } else {
                Answer::No
            })
        }
        Question::Implied(body, premise) => {
            let others: Vec<_> = body.iter().copied().filter(|l| *l != premise).collect();
            let Some(others) = m.body(&others, ops.b)? else {
                return Ok(Answer::Yes);
            };
            let premise = if let Some(l) = resolved(premise) {
                ops.value(&values, l)?
            } else {
                match m.resolve(atom(premise)) {
                    Binding::Constant(v) => ops.own(if v == (premise > 0) {
                        variables.mk_true()
                    } else {
                        variables.mk_false()
                    })?,
                    _ => unreachable!(),
                }
            };
            let guard = ops.body(&values, &others, &variables)?;
            let guard = ops.apply(&u, &guard, and)?;
            Ok(if ops.apply(&guard, &premise, and_not)?.is_false() {
                Answer::Yes
            } else {
                Answer::No
            })
        }
    }
}
