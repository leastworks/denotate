use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable, BddVariableSet, op_function};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

mod equations;
pub(crate) use equations::{EquationContext, Formula};

// Historical-order probes. Thread-local scope and RAII restoration isolate
// parallel tests/panics; production request preparation uses AtomKey order.
#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static TEST_INPUT_ORDER: std::cell::RefCell<Option<BTreeMap<GroundAtom, usize>>> = const { std::cell::RefCell::new(None) };
}
#[cfg(any(test, feature = "test-support"))]
pub fn with_test_input_order<T>(order: Vec<GroundAtom>, run: impl FnOnce() -> T) -> T {
    struct Restore(Option<BTreeMap<GroundAtom, usize>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TEST_INPUT_ORDER.with(|v| *v.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(TEST_INPUT_ORDER.with(|v| {
        v.replace(Some(
            order.into_iter().enumerate().map(|(i, a)| (a, i)).collect(),
        ))
    }));
    run()
}

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
    /// Raw Boolean falsity, without restricting to permitted input worlds.
    pub fn is_false(&self) -> bool {
        self.bdd.is_false()
    }
    /// Raw Boolean truth. Use ConditionContext queries for W-relative judgments.
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
/// Raw Boolean algebra is unrestricted; semantic queries and witnesses respect
/// the preparation's input-only at-most-one constraints.
/// Creating this context does not require evaluating the rules. Conditions for
/// derived facts come from SymbolicMeaning.
#[derive(Debug)]
pub struct ConditionContext {
    universe: u64,
    inputs: BTreeMap<GroundAtom, BddVariable>,
    variables: BddVariableSet,
    no: Condition,
    yes: Condition,
    permitted: Condition,
}

impl GroundProgram {
    fn bdd_inputs(&self) -> Vec<&GroundAtom> {
        #[allow(unused_mut)]
        let mut inputs = self.ordered_inputs();
        #[cfg(any(test, feature = "test-support"))]
        TEST_INPUT_ORDER.with(|v| {
            if let Some(order) = v.borrow().as_ref() {
                assert_eq!(inputs.len(), order.len());
                inputs.sort_by_key(|a| order[*a]);
            }
        });
        inputs
    }

    pub fn condition_context(&self, limits: &Limits) -> Result<ConditionContext> {
        ConditionContext::build(self, &mut Budget::new(limits))
    }

    /// Return the exact conjunction of input literals, if this condition is one.
    /// Values say whether each fact must be present or absent; unmentioned facts
    /// are unconstrained. True gives an empty map; false and non-conjunctions
    /// give None. This is not a satisfying assignment or a DNF expansion.
    pub fn input_conjunction(
        &self,
        condition: &Condition,
        limits: &Limits,
    ) -> Result<Option<BTreeMap<GroundAtom, bool>>> {
        let mut budget = Budget::new(limits);
        budget.tick("condition summary")?;
        if condition.universe != self.preparation
            || usize::from(condition.bdd.num_vars()) != self.inputs.len()
        {
            return Err(CheckError::ForeignCondition);
        }
        if condition.node_count() > limits.max_bdd_nodes {
            return Err(limit("condition summary", "BDD nodes"));
        }
        if condition.is_false() {
            return Ok(None);
        }
        // A conjunction's reduced BDD has one continuing branch at each node;
        // its other branch is false. Follow links, not serialization order.
        let mut literals = BTreeMap::new();
        let mut node = condition.bdd.root_pointer();
        while !node.is_one() {
            budget.tick("condition summary")?;
            let low = condition.bdd.low_link_of(node);
            let high = condition.bdd.high_link_of(node);
            let (value, next) = match (low.is_zero(), high.is_zero()) {
                (true, false) => (true, high),
                (false, true) => (false, low),
                _ => return Ok(None),
            };
            literals.insert(condition.bdd.var_of(node).to_index(), value);
            node = next;
        }
        let mut result = BTreeMap::new();
        for (index, atom) in self.bdd_inputs().into_iter().enumerate() {
            budget.tick("condition summary")?;
            if let Some(value) = literals.get(&index) {
                result.insert(atom.clone(), *value);
            }
        }
        Ok(Some(result))
    }
}

impl ConditionContext {
    pub(crate) fn build(program: &GroundProgram, budget: &mut Budget<'_>) -> Result<Self> {
        budget.tick("BDD inputs")?;
        let count = program.inputs.len();
        // new_anonymous rejects >= u16::MAX - 1. Check before its panicking API.
        budget.observe("BDD inputs", "BDD variables", count);
        budget.observe("BDD inputs", "BDD nodes", 2);
        if count > budget.limits.max_bdd_variables || count >= usize::from(u16::MAX - 1) {
            return Err(limit("BDD inputs", "BDD variables"));
        }
        if budget.limits.max_bdd_nodes < 2 {
            return Err(limit("BDD inputs", "BDD nodes"));
        }
        budget.charge(count, "BDD inputs")?;
        let variables = BddVariableSet::new_anonymous(count as u16);
        let mut inputs = BTreeMap::new();
        let input_order = program.bdd_inputs().into_iter();
        for (atom, variable) in input_order.zip(variables.variables()) {
            budget.tick("BDD inputs")?;
            inputs.insert(atom.clone(), variable);
        }
        let wrap = |bdd| Condition {
            universe: program.preparation,
            bdd: Arc::new(bdd),
        };
        let mut context = Self {
            universe: program.preparation,
            no: wrap(variables.mk_false()),
            yes: wrap(variables.mk_true()),
            permitted: wrap(variables.mk_true()),
            inputs,
            variables,
        };
        // Linear prefix scheme: each next choice excludes all previous choices.
        for group in &program.input_groups {
            let mut seen = context.false_condition();
            for atom in group {
                let value = context.input_with_budget(atom, budget)?;
                let conflict = context.apply(&seen, &value, op_function::and, budget)?;
                context.permitted =
                    context.apply(&context.permitted, &conflict, op_function::and_not, budget)?;
                seen = context.apply(&seen, &value, op_function::or, budget)?;
            }
        }
        crate::symbolic::retain(0, 0, context.permitted.node_count(), budget)?;
        Ok(context)
    }

    /// W, independent of the rules; the all-absent world is always permitted.
    pub fn permitted_worlds(&self) -> Condition {
        self.permitted.clone()
    }

    pub(crate) fn restrict(
        &self,
        condition: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        if self.permitted.is_true() {
            self.check(condition, budget)?;
            return Ok(condition.clone());
        }
        self.apply(&self.permitted, condition, op_function::and, budget)
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
        budget.observe("BDD input", "BDD nodes", 3);
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
        let mut budget = Budget::new(limits);
        Ok(self
            .restrict(
                &self.apply(a, b, op_function::and, &mut budget)?,
                &mut budget,
            )?
            .can_hold())
    }
    pub fn implies(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<bool> {
        let mut budget = Budget::new(limits);
        Ok(self
            .restrict(
                &self.apply(a, b, op_function::and_not, &mut budget)?,
                &mut budget,
            )?
            .is_false())
    }
    pub fn equivalent(&self, a: &Condition, b: &Condition, limits: &Limits) -> Result<bool> {
        let mut budget = Budget::new(limits);
        Ok(self
            .restrict(
                &self.apply(a, b, op_function::xor, &mut budget)?,
                &mut budget,
            )?
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
        let condition = self.restrict(condition, budget)?;
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

    /// Complete only inputs outside the function's full Boolean support as
    /// present. Variables skipped on one satisfying path are not don't-cares.
    pub(crate) fn present_dont_cares(
        &self,
        condition: &Condition,
        observation: &Observation,
        budget: &mut Budget<'_>,
    ) -> Result<Observation> {
        // W participates in support: completing only true don't-cares preserves
        // both the finding and exclusivity. Grouped choices may stay absent.
        let condition = self.restrict(condition, budget)?;
        let mut pending = vec![condition.bdd.root_pointer()];
        let mut visited = BTreeSet::new();
        let mut support = BTreeSet::new();
        while let Some(node) = pending.pop() {
            budget.tick("witness support")?;
            if node.is_zero() || node.is_one() || !visited.insert(node) {
                continue;
            }
            support.insert(condition.bdd.var_of(node));
            pending.push(condition.bdd.low_link_of(node));
            pending.push(condition.bdd.high_link_of(node));
        }
        budget.charge(self.inputs.len(), "witness completion")?;
        let mut next = observation.clone();
        for (atom, variable) in &self.inputs {
            budget.tick("witness completion")?;
            if !support.contains(variable) {
                next.absent.remove(atom);
                next.present.insert(atom.clone());
            }
        }
        Ok(next)
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
        self.evaluate_with_budget(condition, present, &mut budget)
    }
    pub(crate) fn evaluate_with_budget(
        &self,
        condition: &Condition,
        present: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        self.check(condition, budget)?;
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
        budget.charge(self.permitted.node_count(), "permitted observation")?;
        if !self.permitted.bdd.eval_in(&valuation) {
            return Err(CheckError::InvalidInputGroup(
                "observation violates input exclusivity",
            ));
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
        if condition.universe != self.universe
            || condition.bdd.num_vars() != self.variables.num_vars()
        {
            return Err(CheckError::ForeignCondition);
        }
        budget.observe("BDD operation", "BDD nodes", condition.node_count());
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
        let Some((_, tasks)) = Bdd::check_binary_op(allowed, &a.bdd, &b.bdd, op) else {
            budget.observe("BDD preflight", "BDD tasks", allowed.saturating_add(1));
            return Err(limit("BDD preflight", "BDD tasks"));
        };
        budget.observe("BDD operation", "BDD tasks", tasks);
        budget.charge(2 * tasks + 1, "BDD operation")?;
        let Some(bdd) = Bdd::binary_op_with_limit(budget.limits.max_bdd_nodes, &a.bdd, &b.bdd, op)
        else {
            budget.observe(
                "BDD operation",
                "BDD nodes",
                budget.limits.max_bdd_nodes.saturating_add(1),
            );
            return Err(limit("BDD operation", "BDD nodes"));
        };
        budget.observe("BDD operation", "BDD nodes", bdd.size());
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
    fn input_conjunction_is_exact_and_omits_dont_care_inputs() {
        let limits = Limits::default();
        let mut corpus = Corpus::new();
        let atoms: Vec<_> = ["x", "y", "z"]
            .into_iter()
            .map(|name| {
                GroundAtom::new(
                    corpus
                        .declare_relation(name, RelationRole::Input, [])
                        .unwrap(),
                    [],
                )
            })
            .collect();
        let program = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
        let ctx = program.condition_context(&limits).unwrap();
        let x = ctx.input(&atoms[0], &limits).unwrap();
        let y = ctx.input(&atoms[1], &limits).unwrap();
        let not_z = ctx
            .not(&ctx.input(&atoms[2], &limits).unwrap(), &limits)
            .unwrap();
        let conjunction = ctx.and(&x, &not_z, &limits).unwrap();
        // Two authored alternatives can simplify to one exact conjunction.
        let simplified = ctx
            .or(
                &ctx.and(&conjunction, &y, &limits).unwrap(),
                &ctx.and(&conjunction, &ctx.not(&y, &limits).unwrap(), &limits)
                    .unwrap(),
                &limits,
            )
            .unwrap();
        for (condition, expected) in [
            (ctx.true_condition(), BTreeMap::new()),
            (x.clone(), BTreeMap::from([(atoms[0].clone(), true)])),
            (not_z, BTreeMap::from([(atoms[2].clone(), false)])),
            (
                conjunction,
                BTreeMap::from([(atoms[0].clone(), true), (atoms[2].clone(), false)]),
            ),
            (
                simplified,
                BTreeMap::from([(atoms[0].clone(), true), (atoms[2].clone(), false)]),
            ),
        ] {
            let literals = program
                .input_conjunction(&condition, &limits)
                .unwrap()
                .unwrap();
            assert_eq!(literals, expected);
            for bits in 0..8 {
                let present: BTreeSet<_> = atoms
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits & (1 << i) != 0)
                    .map(|(_, a)| a.clone())
                    .collect();
                assert_eq!(
                    ctx.evaluate(&condition, present.iter().cloned(), &limits)
                        .unwrap(),
                    literals
                        .iter()
                        .all(|(atom, value)| present.contains(atom) == *value),
                );
            }
        }
        assert_eq!(
            program
                .input_conjunction(&ctx.false_condition(), &limits)
                .unwrap(),
            None
        );
        assert_eq!(
            program
                .input_conjunction(&ctx.or(&x, &y, &limits).unwrap(), &limits)
                .unwrap(),
            None
        );
        let foreign = GroundProgram::prepare(&corpus, &Domains::new(), &limits).unwrap();
        assert_eq!(
            foreign.input_conjunction(&x, &limits),
            Err(CheckError::ForeignCondition)
        );
        for limited in [
            Limits {
                max_work: 0,
                ..limits.clone()
            },
            Limits {
                max_bdd_nodes: 2,
                ..limits.clone()
            },
        ] {
            assert!(matches!(
                program.input_conjunction(&x, &limited),
                Err(CheckError::LimitExceeded { .. })
            ));
        }
    }

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
