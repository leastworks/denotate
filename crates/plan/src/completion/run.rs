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
        crate::run::execute_region(
            &self.classification,
            &self.outputs,
            &mut values,
            order,
            &mut work,
            &mut trace,
            &mut branches,
            &mut callback,
            &mut tasks,
            &mut executed,
        )?;
        work.tick()?;
        let accept = match &self.terminal {
            Terminal::Accept => true,
            Terminal::Reject => false,
            Terminal::Test(h) => *values.get(h).ok_or(ExecutionError::InvalidPlan)?,
        };
        if !accept {
            return Ok(Execution {
                outcome: Outcome::Rejected,
                trace,
            });
        }
        crate::run::execute_region(
            &self.accepted,
            &self.outputs,
            &mut values,
            order,
            &mut work,
            &mut trace,
            &mut branches,
            &mut callback,
            &mut tasks,
            &mut executed,
        )?;
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
        })
    }
}
