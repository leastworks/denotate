use super::*;
use crate::{ExecutionError, Order};

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Accepted { outputs: BTreeMap<AtomKey, bool> },
    Rejected,
}
#[derive(Debug)]
pub struct Execution {
    pub outcome: Outcome,
    /// Actual computations only. Rejected runs never enter the accepted region.
    pub trace: Vec<AtomKey>,
    /// Splits taken, in order: the input and its actual value.
    pub branches: Vec<(AtomKey, bool)>,
}
impl Plan {
    /// Caller certifies W for the full observation. No runtime solver or contract
    /// validator is invoked. Message inputs are entry-available; missing != false.
    pub fn execute_permitted(
        &self,
        inputs: &BTreeMap<AtomKey, bool>,
        order: Order,
        max_work: usize,
    ) -> std::result::Result<Execution, ExecutionError> {
        let mut work = crate::run::Work { left: max_work };
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
        let mut callback =
            |_: &crate::Invocation| Err("completion task scheduling is not implemented".into());
        let mut run = |nodes: &BTreeMap<AtomKey, Node>,
                       values: &mut BTreeMap<AtomKey, bool>,
                       work: &mut crate::run::Work,
                       trace: &mut Vec<AtomKey>,
                       branches: &mut Vec<(AtomKey, bool)>| {
            crate::run::execute_region(
                nodes,
                &self.outputs,
                values,
                order,
                work,
                trace,
                branches,
                &mut callback,
                &mut tasks,
                &mut executed,
            )
        };
        let mut region = &self.root;
        let accepted = loop {
            run(
                &region.nodes,
                &mut values,
                &mut work,
                &mut trace,
                &mut branches,
            )?;
            match &region.next {
                Next::Split {
                    on,
                    then,
                    otherwise,
                } => {
                    work.tick()?;
                    let value = *values.get(on).ok_or(ExecutionError::InvalidPlan)?;
                    branches.push((on.clone(), value));
                    region = if value { then } else { otherwise };
                }
                Next::Leaf {
                    checks,
                    terminal,
                    accepted,
                } => {
                    let mut accept = true;
                    for c in checks {
                        if crate::run::evaluate(&c.definition, &values, &mut work)? != c.value {
                            accept = false;
                            break;
                        }
                    }
                    work.tick()?;
                    accept &= match terminal {
                        Terminal::Accept => true,
                        Terminal::Reject => false,
                        Terminal::Test(h) => *values.get(h).ok_or(ExecutionError::InvalidPlan)?,
                    };
                    if !accept {
                        return Ok(Execution {
                            outcome: Outcome::Rejected,
                            trace,
                            branches,
                        });
                    }
                    break accepted.as_deref().ok_or(ExecutionError::InvalidPlan)?;
                }
            }
        };
        let mut part = accepted;
        loop {
            run(
                &part.nodes,
                &mut values,
                &mut work,
                &mut trace,
                &mut branches,
            )?;
            match &part.next {
                AcceptedNext::Return => break,
                // An accepted message on an arm proved unreachable: W was violated.
                AcceptedNext::Unreachable => return Err(ExecutionError::InvalidPlan),
                AcceptedNext::Split {
                    on,
                    then,
                    otherwise,
                } => {
                    work.tick()?;
                    let value = *values.get(on).ok_or(ExecutionError::InvalidPlan)?;
                    branches.push((on.clone(), value));
                    part = if value { then } else { otherwise };
                }
            }
        }
        let mut outputs = BTreeMap::new();
        for k in self.outputs.keys() {
            work.tick()?;
            outputs.insert(
                k.clone(),
                *values.get(k).ok_or(ExecutionError::InvalidPlan)?,
            );
        }
        Ok(Execution {
            outcome: Outcome::Accepted { outputs },
            trace,
            branches,
        })
    }
}
