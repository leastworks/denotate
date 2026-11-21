//! Experimental, pure Boolean execution plans. Construction is verification
//! specific; interpretation requires an independently validated permitted input.
//! Pure tasks use explicit scheduling descriptors and caller-supplied callbacks.
//! No IO or execution permission policy lives here.
mod build;
mod export;
mod run;
mod search;
mod task;
pub use build::{Build, Options, Output, Planner, Problem};
use denotate_check::{AtomKey, stable_query};
use denotate_ir::{AssumptionKey, RuleKey, VerificationKey};
pub use export::{atom as atom_json, scope_json};
pub use run::{Execution, ExecutionError, Order};
use std::collections::{BTreeMap, BTreeSet};
pub use task::{Call, Invocation, Task, TaskEvent};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Constant(bool),
    Read(AtomKey),
    Not(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
    If {
        atom: AtomKey,
        when_true: usize,
        when_false: usize,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression {
    pub nodes: Vec<Term>,
    pub root: usize,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub head: AtomKey,
    pub body: Vec<(AtomKey, bool)>,
    pub source: RuleKey,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operation {
    Call {
        call: Call,
        inactive: bool,
    },
    Compute {
        output: AtomKey,
        expression: Expression,
    },
    /// Internal premises are positive. External negations are settled before
    /// entering the kernel. Start all outputs false, then grow to the least model.
    Fixpoint {
        outputs: BTreeSet<AtomKey>,
        rules: Vec<Rule>,
    },
    /// Both feasible arms deliver these bindings. The outer dependency graph is
    /// the shared continuation; no arm's truth pins escape this join.
    Split {
        on: AtomKey,
        outputs: BTreeSet<AtomKey>,
        when_true: Option<Box<Region>>,
        when_false: Option<Box<Region>>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Region {
    pub nodes: BTreeMap<AtomKey, Node>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    /// Smallest output semantic key; no arena or allocation identity.
    pub id: AtomKey,
    pub inputs: BTreeSet<AtomKey>,
    pub operation: Operation,
    /// Direct defining rules, also the frontend's lookup keys for loc origins.
    /// For an extracted expression these are targets, not a full proof trace.
    pub sources: BTreeSet<RuleKey>,
}
impl Node {
    pub fn outputs(&self) -> BTreeSet<AtomKey> {
        match &self.operation {
            Operation::Call { call, .. } => call.results.clone(),
            Operation::Compute { output, .. } => BTreeSet::from([output.clone()]),
            Operation::Fixpoint { outputs, .. } | Operation::Split { outputs, .. } => {
                outputs.clone()
            }
        }
    }
}
/// Immutable complete plan; incomplete construction never exposes a partial Plan.
/// Edges are value dependencies, not a baked-in execution order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    scope: stable_query::ScopeSummary,
    verification: VerificationKey,
    assumptions: BTreeSet<AssumptionKey>,
    inputs: BTreeSet<AtomKey>,
    produced_inputs: BTreeSet<AtomKey>,
    outputs: BTreeMap<AtomKey, u32>,
    nodes: BTreeMap<AtomKey, Node>,
}
impl Plan {
    pub fn scope(&self) -> &stable_query::ScopeSummary {
        &self.scope
    }
    pub fn verification(&self) -> &VerificationKey {
        &self.verification
    }
    pub fn assumptions(&self) -> &BTreeSet<AssumptionKey> {
        &self.assumptions
    }
    pub fn inputs(&self) -> &BTreeSet<AtomKey> {
        &self.inputs
    }
    pub fn produced_inputs(&self) -> &BTreeSet<AtomKey> {
        &self.produced_inputs
    }
    pub fn outputs(&self) -> &BTreeMap<AtomKey, u32> {
        &self.outputs
    }
    pub fn nodes(&self) -> &BTreeMap<AtomKey, Node> {
        &self.nodes
    }
}

#[cfg(test)]
mod tests;
