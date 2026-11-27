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
    ProducedInputAtEntry(AtomKey),
    TaskCallbackRequired,
    TaskFailed(denotate_ir::QualifiedKey, String),
    InvalidTaskResults(denotate_ir::QualifiedKey),
    WorkLimit,
    InvalidPlan,
    InfeasiblePath,
}
#[derive(Debug)]
pub struct Execution {
    pub outputs: BTreeMap<AtomKey, bool>,
    pub trace: Vec<AtomKey>,
    pub branches: Vec<(AtomKey, bool)>,
    pub tasks: Vec<TaskEvent>,
}
pub(crate) struct Work {
    pub(crate) left: usize,
}
impl Work {
    pub(crate) fn tick(&mut self) -> Result<(), ExecutionError> {
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
        if !self.produced_inputs.is_empty() {
            return Err(ExecutionError::TaskCallbackRequired);
        }
        self.execute_with_tasks(inputs, order, max_work, &mut |_| unreachable!())
    }
    /// Execute with pure callbacks. The completed observation (entry inputs plus
    /// task results, false for skipped calls) must satisfy W. No runtime contract
    /// validation or permission policy is implemented here.
    pub fn execute_with_tasks(
        &self,
        inputs: &BTreeMap<AtomKey, bool>,
        order: Order,
        max_work: usize,
        callback: &mut dyn FnMut(&Invocation) -> Result<BTreeMap<AtomKey, bool>, String>,
    ) -> Result<Execution, ExecutionError> {
        let mut work = Work { left: max_work };
        for k in &self.produced_inputs {
            work.tick()?;
            if inputs.contains_key(k) {
                return Err(ExecutionError::ProducedInputAtEntry(k.clone()));
            }
        }
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
        let mut trace = Vec::new();
        let mut branches = Vec::new();
        let mut tasks = Vec::new();
        let mut executed = BTreeSet::new();
        execute_region(
            &self.nodes,
            &self.outputs,
            &mut values,
            order,
            &mut work,
            &mut trace,
            &mut branches,
            callback,
            &mut tasks,
            &mut executed,
        )?;
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
        Ok(Execution {
            outputs,
            trace,
            branches,
            tasks,
        })
    }
}

pub(crate) fn evaluate(
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

fn priorities(
    nodes: &BTreeMap<AtomKey, Node>,
    outputs: &BTreeMap<AtomKey, u32>,
    work: &mut Work,
) -> Result<BTreeMap<AtomKey, u32>, ExecutionError> {
    let providers: BTreeMap<_, _> = nodes
        .iter()
        .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id.clone())))
        .collect();
    let mut result = BTreeMap::new();
    let mut pending: Vec<_> = outputs.iter().map(|(k, p)| (k.clone(), *p)).collect();
    while let Some((k, p)) = pending.pop() {
        work.tick()?;
        if let Some(id) = providers.get(&k) {
            if result.get(id).is_none_or(|old| p < *old) {
                result.insert(id.clone(), p);
                pending.extend(nodes[id].inputs.iter().cloned().map(|k| (k, p)));
            }
        }
    }
    Ok(result)
}

pub(crate) fn execute_region(
    nodes: &BTreeMap<AtomKey, Node>,
    outputs: &BTreeMap<AtomKey, u32>,
    values: &mut BTreeMap<AtomKey, bool>,
    order: Order,
    work: &mut Work,
    trace: &mut Vec<AtomKey>,
    branches: &mut Vec<(AtomKey, bool)>,
    callback: &mut dyn FnMut(&Invocation) -> Result<BTreeMap<AtomKey, bool>, String>,
    tasks: &mut Vec<TaskEvent>,
    executed: &mut BTreeSet<denotate_ir::QualifiedKey>,
) -> Result<(), ExecutionError> {
    let mut remaining: BTreeMap<_, _> = nodes.iter().collect();
    let priorities = priorities(nodes, outputs, work)?;

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
            Order::OutputPriority => ready
                .sort_by_key(|id| (priorities.get(id).copied().unwrap_or(u32::MAX), id.clone())),
        }
        let id = ready
            .into_iter()
            .next()
            .ok_or(ExecutionError::InvalidPlan)?;
        let node = remaining.remove(&id).unwrap();
        match &node.operation {
            Operation::Call { call, inactive } => {
                work.tick()?;
                if !executed.insert(call.task.clone()) {
                    return Err(ExecutionError::InvalidPlan);
                }
                let active = !inactive
                    && match &call.when {
                        None => true,
                        Some(k) => *values.get(k).ok_or(ExecutionError::InvalidPlan)?,
                    };
                let result = if active {
                    let arguments = call
                        .arguments
                        .iter()
                        .map(|k| {
                            work.tick()?;
                            Ok((
                                k.clone(),
                                *values.get(k).ok_or(ExecutionError::InvalidPlan)?,
                            ))
                        })
                        .collect::<Result<_, ExecutionError>>()?;
                    for _ in &call.results {
                        work.tick()?;
                    }
                    callback(&Invocation {
                        task: call.task.clone(),
                        arguments,
                        results: call.results.clone(),
                    })
                    .map_err(|e| ExecutionError::TaskFailed(call.task.clone(), e))?
                } else {
                    call.results.iter().map(|k| (k.clone(), false)).collect()
                };
                for _ in &result {
                    work.tick()?;
                }
                if result.len() != call.results.len()
                    || result.keys().any(|k| !call.results.contains(k))
                {
                    return Err(ExecutionError::InvalidTaskResults(call.task.clone()));
                }
                values.extend(result.iter().map(|(k, v)| (k.clone(), *v)));
                tasks.push(TaskEvent {
                    task: call.task.clone(),
                    invoked: active,
                    results: result,
                });
            }
            Operation::Compute { output, expression } => {
                let value = evaluate(expression, values, work)?;
                values.insert(output.clone(), value);
            }
            Operation::Split {
                on,
                outputs: joined,
                when_true,
                when_false,
            } => {
                let choice = *values.get(on).ok_or(ExecutionError::InvalidPlan)?;
                branches.push((on.clone(), choice));
                let arm = if choice { when_true } else { when_false };
                let arm = arm.as_ref().ok_or(ExecutionError::InfeasiblePath)?;
                let mut local = BTreeMap::new();
                for (k, v) in values.iter() {
                    work.tick()?;
                    local.insert(k.clone(), *v);
                }
                let targets = joined
                    .iter()
                    .map(|k| (k.clone(), priorities.get(&id).copied().unwrap_or(u32::MAX)))
                    .collect();
                execute_region(
                    &arm.nodes, &targets, &mut local, order, work, trace, branches, callback,
                    tasks, executed,
                )?;
                for k in joined {
                    work.tick()?;
                    values.insert(k.clone(), *local.get(k).ok_or(ExecutionError::InvalidPlan)?);
                }
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
                            holds &= values.get(k).ok_or(ExecutionError::InvalidPlan)? == positive;
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

    Ok(())
}
