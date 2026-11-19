//! Experimental, pure Boolean execution plans. Construction is verification
//! specific; interpretation requires an independently validated permitted input.
//! No IO, tasks, produced inputs, or execution permission policy lives here.
mod build;
mod export;
mod run;
pub use build::{Build, Options, Output, Planner, Problem};
use denotate_check::{AtomKey, stable_query};
use denotate_ir::{AssumptionKey, RuleKey, VerificationKey};
pub use export::atom as atom_json;
pub use run::{Execution, ExecutionError, Order};
use std::collections::{BTreeMap, BTreeSet};

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
            Operation::Compute { output, .. } => BTreeSet::from([output.clone()]),
            Operation::Fixpoint { outputs, .. } => outputs.clone(),
        }
    }
}
/// Immutable complete plan; incomplete construction never exposes a partial Plan.
/// Edges are value dependencies, not a baked-in execution order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    verification: VerificationKey,
    assumptions: BTreeSet<AssumptionKey>,
    inputs: BTreeSet<AtomKey>,
    outputs: BTreeMap<AtomKey, u32>,
    nodes: BTreeMap<AtomKey, Node>,
}
impl Plan {
    pub fn verification(&self) -> &VerificationKey {
        &self.verification
    }
    pub fn assumptions(&self) -> &BTreeSet<AssumptionKey> {
        &self.assumptions
    }
    pub fn inputs(&self) -> &BTreeSet<AtomKey> {
        &self.inputs
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
