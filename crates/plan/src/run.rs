use super::*;

/// Scheduling policy is separate from the plan's dependency partial order.
#[derive(Debug, Clone, Copy)]
pub enum Order {
    Semantic,
    ReverseSemantic,
    OutputPriority,
}
#[derive(Debug, PartialEq, Eq)]
pub enum ExecutionError {
    MissingInput(AtomKey),
    WorkLimit,
    InvalidPlan,
}
#[derive(Debug)]
pub struct Execution {
    pub outputs: BTreeMap<AtomKey, bool>,
    pub trace: Vec<AtomKey>,
}
struct Work {
    left: usize,
}
impl Work {
    fn tick(&mut self) -> Result<(), ExecutionError> {
        self.left = self.left.checked_sub(1).ok_or(ExecutionError::WorkLimit)?;
        Ok(())
    }
}
impl Plan {
    /// Execute a complete input snapshot already validated against this plan's
    /// verification assumptions and input-domain/cardinality contracts. This is
    /// a low-level interpreter, NOT an input admission or run-and-log API.
    /// Every referenced input needs an explicit Boolean value; missing != absent.
    pub fn execute_permitted(
        &self,
        inputs: &BTreeMap<AtomKey, bool>,
        order: Order,
        max_work: usize,
    ) -> Result<Execution, ExecutionError> {
        let mut work = Work { left: max_work };
        let mut values = BTreeMap::new();
        for k in &self.inputs {
            work.tick()?;
            values.insert(
                k.clone(),
                *inputs
                    .get(k)
                    .ok_or_else(|| ExecutionError::MissingInput(k.clone()))?,
            );
        }
        let mut remaining: BTreeMap<_, _> = self.nodes.iter().collect();
        let priorities = self.priorities(&mut work)?;
        let mut trace = Vec::new();
        while !remaining.is_empty() {
            let mut ready = Vec::new();
            for (id, n) in &remaining {
                work.tick()?;
                let mut available = true;
                for k in &n.inputs {
                    work.tick()?;
                    available &= values.contains_key(k);
                }
                if available {
                    ready.push((*id).clone());
                }
            }
            match order {
                Order::Semantic => {}
                Order::ReverseSemantic => ready.reverse(),
                Order::OutputPriority => ready.sort_by_key(|id| {
                    (priorities.get(id).copied().unwrap_or(u32::MAX), id.clone())
                }),
            }
            let id = ready
                .into_iter()
                .next()
                .ok_or(ExecutionError::InvalidPlan)?;
            let node = remaining.remove(&id).unwrap();
            match &node.operation {
                Operation::Compute { output, expression } => {
                    let value = evaluate(&expression, &values, &mut work)?;
                    values.insert(output.clone(), value);
                }
                Operation::Fixpoint { outputs, rules } => {
                    for k in outputs {
                        work.tick()?;
                        values.insert(k.clone(), false);
                    }
                    loop {
                        let mut changed = false;
                        for r in rules {
                            work.tick()?;
                            let mut holds = true;
                            for (k, positive) in &r.body {
                                work.tick()?;
                                holds &=
                                    values.get(k).ok_or(ExecutionError::InvalidPlan)? == positive;
                            }
                            if holds && !values[&r.head] {
                                values.insert(r.head.clone(), true);
                                changed = true;
                            }
                        }
                        if !changed {
                            break;
                        }
                    }
                }
            }
            trace.push(id);
        }
        let outputs = self
            .outputs
            .keys()
            .map(|k| {
                Ok((
                    k.clone(),
                    *values.get(k).ok_or(ExecutionError::InvalidPlan)?,
                ))
            })
            .collect::<Result<_, _>>()?;
        Ok(Execution { outputs, trace })
    }
    fn priorities(&self, work: &mut Work) -> Result<BTreeMap<AtomKey, u32>, ExecutionError> {
        let providers: BTreeMap<_, _> = self
            .nodes
            .iter()
            .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id.clone())))
            .collect();
        let mut result = BTreeMap::new();
        let mut pending: Vec<_> = self.outputs.iter().map(|(k, p)| (k.clone(), *p)).collect();
        while let Some((k, p)) = pending.pop() {
            work.tick()?;
            if let Some(id) = providers.get(&k) {
                if result.get(id).is_none_or(|old| p < *old) {
                    result.insert(id.clone(), p);
                    pending.extend(self.nodes[id].inputs.iter().cloned().map(|k| (k, p)));
                }
            }
        }
        Ok(result)
    }
}
fn evaluate(
    expr: &Expression,
    values: &BTreeMap<AtomKey, bool>,
    work: &mut Work,
) -> Result<bool, ExecutionError> {
    let mut computed: Vec<bool> = Vec::new();
    for n in &expr.nodes {
        work.tick()?;
        let value = match n {
            Term::Constant(v) => *v,
            Term::Read(k) => *values.get(k).ok_or(ExecutionError::InvalidPlan)?,
            Term::Not(i) => !computed[*i],
            Term::And(xs) => {
                let mut v = true;
                for i in xs {
                    work.tick()?;
                    v &= computed[*i];
                }
                v
            }
            Term::Or(xs) => {
                let mut v = false;
                for i in xs {
                    work.tick()?;
                    v |= computed[*i];
                }
                v
            }
            Term::If {
                atom,
                when_true,
                when_false,
            } => {
                computed[if *values.get(atom).ok_or(ExecutionError::InvalidPlan)? {
                    *when_true
                } else {
                    *when_false
                }]
            }
        };
        computed.push(value);
    }
    computed
        .get(expr.root)
        .copied()
        .ok_or(ExecutionError::InvalidPlan)
}
