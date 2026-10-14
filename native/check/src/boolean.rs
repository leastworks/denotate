use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable, BddVariableSet, op_function};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

/// A complete Boolean assignment: every ground input fact is present or absent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observation {
    pub present: BTreeSet<GroundAtom>,
    pub absent: BTreeSet<GroundAtom>,
}

/// An opaque Boolean function in one immutable ground program's input universe.
/// Cloning shares storage; callers cannot inject BDDs from another universe.
/// Compare meanings with ConditionContext::equivalent, not storage equality.
#[derive(Debug, Clone)]
pub struct Condition {
    universe: u64,
    bdd: Arc<Bdd>,
}
impl Condition {
    pub fn is_false(&self) -> bool {
        self.bdd.is_false()
    }
    pub fn is_true(&self) -> bool {
        self.bdd.is_true()
    }
    pub fn node_count(&self) -> usize {
        self.bdd.size()
    }
    pub fn can_hold(&self) -> bool {
        !self.is_false()
    }
    pub fn can_fail(&self) -> bool {
        !self.is_true()
    }
}

/// Boolean conditions over ground input facts.
/// Every input assignment is permitted; assumptions are not supported yet.
/// Creating this context does not require evaluating the rules. Conditions for
/// derived facts come from SymbolicMeaning.
#[derive(Debug)]
pub struct ConditionContext {
    universe: u64,
    inputs: BTreeMap<GroundAtom, BddVariable>,
    variables: BddVariableSet,
    no: Condition,
    yes: Condition,
}

impl GroundProgram {
    pub fn condition_context(&self, limits: &Limits) -> Result<ConditionContext> {
        ConditionContext::build(self, &mut Budget::new(limits))
    }
}

impl ConditionContext {
    pub(crate) fn build(program: &GroundProgram, budget: &mut Budget<'_>) -> Result<Self> {
        budget.tick("BDD inputs")?;
        let count = program.inputs.len();
        // new_anonymous rejects >= u16::MAX - 1. Check before its panicking API.
        if count > budget.limits.max_bdd_variables || count >= usize::from(u16::MAX - 1) {
            return Err(limit("BDD inputs", "BDD variables"));
        }
        if budget.limits.max_bdd_nodes < 2 {
            return Err(limit("BDD inputs", "BDD nodes"));
        }
        budget.charge(count, "BDD inputs")?;
        let variables = BddVariableSet::new_anonymous(count as u16);
        let mut inputs = BTreeMap::new();
        for (atom, variable) in program.inputs.iter().zip(variables.variables()) {
            budget.tick("BDD inputs")?;
            inputs.insert(atom.clone(), variable);
        }
        let wrap = |bdd| Condition {
            universe: program.preparation,
            bdd: Arc::new(bdd),
        };
        Ok(Self {
            universe: program.preparation,
            no: wrap(variables.mk_false()),
            yes: wrap(variables.mk_true()),
            inputs,
            variables,
        })
    }

    pub fn false_condition(&self) -> Condition {
        self.no.clone()
    }
    pub fn true_condition(&self) -> Condition {
        self.yes.clone()
    }
    pub fn inputs(&self) -> impl Iterator<Item = &GroundAtom> {
        self.inputs.keys()
    }

    pub fn input(&self, atom: &GroundAtom, limits: &Limits) -> Result<Condition> {
        self.input_with_budget(atom, &mut Budget::new(limits))
    }
    pub(crate) fn input_with_budget(
        &self,
        atom: &GroundAtom,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        budget.charge(3, "BDD inputs")?;
        let variable = self
            .inputs
            .get(atom)
            .ok_or_else(|| CheckError::InvalidObservation(atom.clone()))?;
        if budget.limits.max_bdd_nodes < 3 {
            return Err(limit("BDD inputs", "BDD nodes"));
        }
        Ok(self.wrap(self.variables.mk_var(*variable)))
    }

    pub fn and(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<Condition> {
        self.apply(a, b, op_function::and, &mut Budget::new(limits))
    }
    pub fn or(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<Condition> {
        self.apply(a, b, op_function::or, &mut Budget::new(limits))
    }
    pub fn not(&self, a: &Condition, limits: &Limits) -> Result<Condition> {
        self.complement(a, &mut Budget::new(limits))
    }
    pub fn may_overlap(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<bool> {
        Ok(self.and(a, b, limits)?.can_hold())
    }
    pub fn implies(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<bool> {
        Ok(self
            .apply(a, b, op_function::and_not, &mut Budget::new(limits))?
            .is_false())
    }
    pub fn equivalent(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<bool> {
        Ok(self
            .apply(a, b, op_function::xor, &mut Budget::new(limits))?
            .is_false())
    }

    /// Select a satisfying assignment, preferring false branches and leaving
    /// unused inputs absent. This is deterministic completion, not minimization.
    pub fn witness(&self, condition: &Condition, limits: &Limits) -> Result<Option<Observation>> {
        self.witness_with_budget(condition, &mut Budget::new(limits))
    }
    pub(crate) fn witness_with_budget(
        &self,
        condition: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Observation>> {
        self.check(condition, budget)?;
        if condition.is_false() {
            return Ok(None);
        }
        budget.charge(self.inputs.len(), "witness")?;
        let mut valuation = BddValuation::all_false(self.inputs.len() as u16);
        // Traverse links, not node-vector order: semantic correctness must not
        // depend on the BDD library's preferred serialization order.
        let mut node = condition.bdd.root_pointer();
        while !node.is_one() {
            budget.tick("witness")?;
            let low = condition.bdd.low_link_of(node);
            if !low.is_zero() {
                node = low;
            } else {
                valuation.set_value(condition.bdd.var_of(node), true);
                node = condition.bdd.high_link_of(node);
            }
        }
        let mut observation = Observation {
            present: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for (atom, variable) in &self.inputs {
            budget.tick("witness")?;
            if valuation.value(*variable) {
                observation.present.insert(atom.clone());
            } else {
                observation.absent.insert(atom.clone());
            }
        }
        Ok(Some(observation))
    }

    /// Test a complete observation (omitted inputs are absent). This is Boolean
    /// evaluation, not concrete relational replay or a counterexample certificate.
    pub fn evaluate(
        &self,
        condition: &Condition,
        present: impl IntoIterator<Item = GroundAtom>,
        limits: &Limits,
    ) -> Result<bool> {
        let mut budget = Budget::new(limits);
        self.check(condition, &mut budget)?;
        budget.charge(
            self.inputs.len() + condition.node_count(),
            "BDD observation",
        )?;
        let mut valuation = BddValuation::all_false(self.inputs.len() as u16);
        for atom in present {
            budget.tick("BDD observation")?;
            let variable = self
                .inputs
                .get(&atom)
                .ok_or(CheckError::InvalidObservation(atom))?;
            valuation.set_value(*variable, true);
        }
        let result = condition.bdd.eval_in(&valuation);
        budget.charge(0, "BDD observation")?;
        Ok(result)
    }

    fn wrap(&self, bdd: Bdd) -> Condition {
        Condition {
            universe: self.universe,
            bdd: Arc::new(bdd),
        }
    }
    fn check(&self, condition: &Condition, budget: &mut Budget<'_>) -> Result<()> {
        budget.tick("BDD operation")?;
        if condition.universe != self.universe {
            return Err(CheckError::ForeignCondition);
        }
        if condition.node_count() > budget.limits.max_bdd_nodes {
            return Err(limit("BDD operation", "BDD nodes"));
        }
        Ok(())
    }
    pub(crate) fn complement(&self, a: &Condition, budget: &mut Budget<'_>) -> Result<Condition> {
        self.check(a, budget)?;
        budget.charge(a.node_count(), "BDD complement")?;
        let result = self.wrap(a.bdd.not());
        self.check(&result, budget)?;
        Ok(result)
    }
    pub(crate) fn apply(
        &self,
        a: &Condition,
        b: &Condition,
        op: fn(Option<bool>, Option<bool>) -> Option<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        self.check(a, budget)?;
        self.check(b, budget)?;
        // The library's result-node bound alone does not bound a large apply
        // cache for a small result. Preflight the task graph before building it.
        let allowed = budget.limits.max_bdd_tasks.min(budget.remaining() / 2);
        let (_, tasks) = Bdd::check_binary_op(allowed, &a.bdd, &b.bdd, op)
            .ok_or_else(|| limit("BDD preflight", "BDD tasks"))?;
        budget.charge(2 * tasks + 1, "BDD operation")?;
        let bdd = Bdd::binary_op_with_limit(budget.limits.max_bdd_nodes, &a.bdd, &b.bdd, op)
            .ok_or_else(|| limit("BDD operation", "BDD nodes"))?;
        budget.charge(0, "BDD operation")?;
        Ok(self.wrap(bdd))
    }
}

pub(crate) fn limit(phase: &'static str, resource: &'static str) -> CheckError {
    CheckError::LimitExceeded { phase, resource }
}

#[cfg(test)]
mod tests {
    use super::*;
    use biodivine_lib_bdd::{BddNode, BddPointer};
    use denotate_ir::{Corpus, RelationRole};

    #[test]
    fn equivalent_meanings_do_not_require_equal_node_vectors() {
        let limits = Limits::default();
        let mut corpus = Corpus::new();
        for name in ["x", "y"] {
            corpus
                .declare_relation(name, RelationRole::Input, [])
                .unwrap();
        }
        let program = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
        let ctx = program.condition_context(&limits).unwrap();
        let vars = ctx.variables.variables();
        let y = BddNode::mk_node(vars[1], BddPointer::zero(), BddPointer::one());
        let not_y = BddNode::mk_node(vars[1], BddPointer::one(), BddPointer::zero());
        let root = |low, high| {
            BddNode::mk_node(
                vars[0],
                BddPointer::from_index(low),
                BddPointer::from_index(high),
            )
        };
        // Both reduced, ordered graphs denote x XOR y. Swapping the two child
        // nodes and fixing the root links changes storage, not the function.
        let a = Bdd::from_nodes(&[
            BddNode::mk_zero(2),
            BddNode::mk_one(2),
            y,
            not_y,
            root(2, 3),
        ])
        .unwrap();
        let b = Bdd::from_nodes(&[
            BddNode::mk_zero(2),
            BddNode::mk_one(2),
            not_y,
            y,
            root(3, 2),
        ])
        .unwrap();
        a.validate().unwrap();
        b.validate().unwrap();
        assert_ne!(a, b, "The regression must exercise distinct node vectors");
        for x in [false, true] {
            for y in [false, true] {
                let valuation = BddValuation::new(vec![x, y]);
                assert_eq!(a.eval_in(&valuation), x ^ y);
                assert_eq!(b.eval_in(&valuation), x ^ y);
            }
        }
        let (a, b) = (ctx.wrap(a), ctx.wrap(b));
        assert!(ctx.equivalent(&a, &b, &limits).unwrap());
        assert!(ctx.equivalent(&b, &a, &limits).unwrap());
        assert!(
            !ctx.equivalent(&a, &ctx.not(&b, &limits).unwrap(), &limits)
                .unwrap()
        );
        // The fixed-point delta test must also recognize that neither adds
        // worlds to the other, regardless of their internal node ordering.
        assert!(
            ctx.apply(&a, &b, op_function::and_not, &mut Budget::new(&limits))
                .unwrap()
                .is_false()
        );
        assert!(
            ctx.apply(&b, &a, op_function::and_not, &mut Budget::new(&limits))
                .unwrap()
                .is_false()
        );
    }
}
