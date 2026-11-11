//! Private, budgeted input-prefix + temporary-suffix BDD universe. No Formula
//! can become a public Condition until every temporary variable is eliminated.
use super::*;
use std::{cell::Cell, rc::Rc};

pub(crate) struct Formula {
    bdd: Option<Bdd>,
    live: Rc<Cell<usize>>,
}
impl Formula {
    fn bdd(&self) -> &Bdd {
        self.bdd.as_ref().expect("live equation formula")
    }
    pub(crate) fn is_false(&self) -> bool {
        self.bdd().is_false()
    }
}
impl Drop for Formula {
    fn drop(&mut self) {
        if let Some(bdd) = &self.bdd {
            self.live.set(self.live.get() - bdd.size());
        }
    }
}

pub(crate) struct EquationContext<'a> {
    inputs: &'a ConditionContext,
    variables: BddVariableSet,
    live: Rc<Cell<usize>>,
    reserved: usize,
}
impl<'a> EquationContext<'a> {
    pub(crate) fn new(
        inputs: &'a ConditionContext,
        temporary: usize,
        reserved: usize,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let count = inputs.inputs.len().checked_add(temporary).ok_or_else(|| {
            limit(
                "completion universe",
                "BDD variables",
                budget
                    .limits
                    .max_bdd_variables
                    .min(usize::from(u16::MAX - 2)),
                None,
            )
        })?;
        budget.observe("completion universe", "BDD variables", count);
        if count > budget.limits.max_bdd_variables || count >= usize::from(u16::MAX - 1) {
            return Err(limit(
                "completion universe",
                "BDD variables",
                budget
                    .limits
                    .max_bdd_variables
                    .min(usize::from(u16::MAX - 2)),
                Some(count),
            ));
        }
        budget.charge(count, "completion universe")?;
        let result = Self {
            inputs,
            variables: BddVariableSet::new_anonymous(count as u16),
            live: Rc::new(Cell::new(0)),
            reserved,
        };
        result.room(2, budget)?;
        Ok(result)
    }
    fn room(&self, extra: usize, budget: &mut Budget<'_>) -> Result<()> {
        budget.tick("completion storage")?;
        crate::symbolic::retain(
            self.reserved,
            0,
            self.live.get().saturating_add(extra),
            budget,
        )?;
        Ok(())
    }
    fn available(&self, budget: &Budget<'_>) -> usize {
        budget
            .limits
            .max_condition_nodes
            .saturating_sub(self.reserved)
            .saturating_sub(self.live.get())
    }
    fn own(&self, bdd: Bdd, budget: &mut Budget<'_>) -> Result<Formula> {
        self.room(bdd.size(), budget)?;
        budget.observe("completion BDD", "BDD nodes", bdd.size());
        if bdd.size() > budget.limits.max_bdd_nodes {
            return Err(limit(
                "completion BDD",
                "BDD nodes",
                budget.limits.max_bdd_nodes,
                Some(bdd.size()),
            ));
        }
        self.live.set(self.live.get() + bdd.size());
        Ok(Formula {
            bdd: Some(bdd),
            live: Rc::clone(&self.live),
        })
    }
    fn check(&self, f: &Formula) -> Result<()> {
        if !Rc::ptr_eq(&self.live, &f.live) || f.bdd().num_vars() != self.variables.num_vars() {
            return Err(CheckError::Internal("foreign equation formula"));
        }
        Ok(())
    }
    pub(crate) fn constant(&self, value: bool, budget: &mut Budget<'_>) -> Result<Formula> {
        self.room(2, budget)?;
        self.own(
            if value {
                self.variables.mk_true()
            } else {
                self.variables.mk_false()
            },
            budget,
        )
    }
    pub(crate) fn variable(&self, index: usize, budget: &mut Budget<'_>) -> Result<Formula> {
        let index = self.inputs.inputs.len() + index;
        if index >= usize::from(self.variables.num_vars()) {
            return Err(CheckError::Internal("unknown equation variable"));
        }
        self.room(3, budget)?;
        if budget.limits.max_bdd_nodes < 3 {
            return Err(limit(
                "completion BDD",
                "BDD nodes",
                budget.limits.max_bdd_nodes,
                Some(3),
            ));
        }
        self.own(
            self.variables.mk_var(BddVariable::from_index(index)),
            budget,
        )
    }
    pub(crate) fn lift(&self, condition: &Condition, budget: &mut Budget<'_>) -> Result<Formula> {
        self.inputs.check(condition, budget)?;
        self.room(condition.node_count(), budget)?;
        budget.charge(condition.node_count(), "completion import")?;
        let mut bdd = (*condition.bdd).clone();
        resize(&mut bdd, self.variables.num_vars(), budget)?;
        self.own(bdd, budget)
    }
    pub(crate) fn not(&self, f: &Formula, budget: &mut Budget<'_>) -> Result<Formula> {
        self.check(f)?;
        self.room(f.bdd().size().max(2), budget)?;
        budget.charge(f.bdd().size(), "completion complement")?;
        self.own(f.bdd().not(), budget)
    }
    pub(crate) fn apply(
        &self,
        a: &Formula,
        b: &Formula,
        op: fn(Option<bool>, Option<bool>) -> Option<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<Formula> {
        self.check(a)?;
        self.check(b)?;
        budget.tick("completion apply")?;
        // Bound preflight cache/stack as well as the construction's cache and
        // output. These are conservative node/task units, not exact heap bytes.
        let available = self.available(budget);
        let allowed = budget
            .limits
            .max_bdd_tasks
            .min(budget.remaining() / 2)
            .min(available / 4);
        let Some((_, tasks)) = Bdd::check_binary_op(allowed, a.bdd(), b.bdd(), op) else {
            budget.observe(
                "completion preflight",
                "BDD tasks",
                allowed.saturating_add(1),
            );
            return Err(limit("completion preflight", "BDD tasks", allowed, None));
        };
        budget.observe("completion apply", "BDD tasks", tasks);
        budget.charge(2 * tasks + 1, "completion apply")?;
        let node_limit = budget
            .limits
            .max_bdd_nodes
            .min(available.saturating_sub(3 * tasks));
        let Some(bdd) = Bdd::binary_op_with_limit(node_limit, a.bdd(), b.bdd(), op) else {
            budget.observe(
                "completion apply",
                "BDD nodes",
                node_limit.saturating_add(1),
            );
            return Err(limit("completion apply", "BDD nodes", node_limit, None));
        };
        self.own(bdd, budget)
    }
    fn restrict(
        &self,
        f: &Formula,
        variable: BddVariable,
        value: bool,
        budget: &mut Budget<'_>,
    ) -> Result<Formula> {
        self.check(f)?;
        let size = f.bdd().size();
        let vars = usize::from(self.variables.num_vars());
        self.room(6 * size + vars, budget)?; // output, remap/cache/stack, valuation
        budget.charge(size + vars, "completion restriction")?;
        self.own(f.bdd().var_restrict(variable, value), budget)
    }
    pub(crate) fn eliminate(&self, mut f: Formula, budget: &mut Budget<'_>) -> Result<Formula> {
        self.check(&f)?;
        // Temporary variables follow all inputs. Eliminate deepest first;
        // upstream conditions keep their variable identities and structure.
        for index in (self.inputs.inputs.len()..usize::from(self.variables.num_vars())).rev() {
            budget.tick("completion elimination")?;
            let v = BddVariable::from_index(index);
            let low = self.restrict(&f, v, false, budget)?;
            let high = self.restrict(&f, v, true, budget)?;
            f = self.apply(&low, &high, op_function::or, budget)?;
        }
        Ok(f)
    }
    pub(crate) fn finish(&self, mut f: Formula, budget: &mut Budget<'_>) -> Result<Condition> {
        self.check(&f)?;
        let bdd = f
            .bdd
            .as_mut()
            .ok_or(CheckError::Internal("missing equation formula"))?;
        resize(bdd, self.inputs.variables.num_vars(), budget)?;
        // Transfer ownership; Drop must not subtract the storage twice.
        let bdd = f
            .bdd
            .take()
            .ok_or(CheckError::Internal("missing equation formula"))?;
        self.live.set(self.live.get() - bdd.size());
        Ok(self.inputs.wrap(bdd, budget))
    }
}

fn resize(bdd: &mut Bdd, count: u16, budget: &mut Budget<'_>) -> Result<()> {
    budget.charge(2 * bdd.size(), "completion universe conversion")?;
    if bdd
        .pointers()
        .skip(2)
        .any(|p| bdd.var_of(p).to_index() >= usize::from(count))
    {
        return Err(CheckError::Internal("temporary equation variable escaped"));
    }
    // SAFETY: all decision variables are in range; increasing the count only
    // changes terminal metadata. Inputs retain their original indices. A
    // narrowed result is wrapped only by its original ConditionContext.
    unsafe {
        bdd.set_num_vars(count);
    }
    budget.charge(0, "completion universe conversion")
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_ir::{Corpus, RelationRole};

    fn program(n: usize) -> GroundProgram {
        let mut c = Corpus::new();
        for i in 0..n {
            c.declare_relation(format!("i{i}"), RelationRole::Input, [])
                .unwrap();
        }
        GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap()
    }
    #[test]
    fn conversion_roundtrips_constants_and_conditions_without_changing_input_nodes() {
        let limits = Limits::default();
        for n in 0..4 {
            let p = program(n);
            let ctx = p.condition_context(&limits).unwrap();
            let mut conditions = vec![ctx.false_condition(), ctx.true_condition()];
            for atom in ctx.inputs() {
                conditions.push(ctx.input(atom, &limits).unwrap());
            }
            for k in 0..4 {
                let mut budget = Budget::new(&limits);
                let eq = EquationContext::new(&ctx, k, 0, &mut budget).unwrap();
                for condition in &conditions {
                    let lifted = eq.lift(condition, &mut budget).unwrap();
                    assert_eq!(lifted.bdd().num_vars(), (n + k) as u16);
                    let nodes = |b: &Bdd| {
                        b.pointers()
                            .skip(2)
                            .map(|p| (b.var_of(p), b.low_link_of(p), b.high_link_of(p)))
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(nodes(lifted.bdd()), nodes(&condition.bdd));
                    let narrowed = eq.finish(lifted, &mut budget).unwrap();
                    assert_eq!(narrowed.bdd.num_vars(), n as u16);
                    assert!(ctx.equivalent(condition, &narrowed, &limits).unwrap());
                    assert_eq!(eq.live.get(), 0);
                }
            }
        }
    }
    #[test]
    fn elimination_removes_the_suffix_and_rejects_uneliminated_or_foreign_formulas() {
        let limits = Limits::default();
        let p = program(1);
        let ctx = p.condition_context(&limits).unwrap();
        let mut budget = Budget::new(&limits);
        let eq = EquationContext::new(&ctx, 2, 0, &mut budget).unwrap();
        let x = ctx.input(ctx.inputs().next().unwrap(), &limits).unwrap();
        let v = eq.variable(1, &mut budget).unwrap();
        assert!(matches!(
            eq.finish(v, &mut budget),
            Err(CheckError::Internal("temporary equation variable escaped"))
        ));
        assert_eq!(eq.live.get(), 0);
        let lifted = eq.lift(&x, &mut budget).unwrap();
        let v = eq.variable(0, &mut budget).unwrap();
        let f = eq
            .apply(&lifted, &v, op_function::and, &mut budget)
            .unwrap();
        drop(lifted);
        drop(v);
        let f = eq.eliminate(f, &mut budget).unwrap();
        let answer = eq.finish(f, &mut budget).unwrap();
        assert!(ctx.equivalent(&answer, &x, &limits).unwrap());
        assert_eq!(eq.live.get(), 0);
        let other = EquationContext::new(&ctx, 2, 0, &mut budget).unwrap();
        assert!(
            eq.finish(other.constant(true, &mut budget).unwrap(), &mut budget)
                .is_err()
        );
        let foreign = program(1)
            .condition_context(&limits)
            .unwrap()
            .true_condition();
        assert!(matches!(
            eq.lift(&foreign, &mut budget),
            Err(CheckError::ForeignCondition)
        ));
        let forged = ctx.wrap(BddVariableSet::new_anonymous(3).mk_true(), &budget);
        assert!(matches!(
            ctx.witness(&forged, &limits),
            Err(CheckError::ForeignCondition)
        ));
    }
    #[test]
    fn universe_work_and_live_buffer_limits_are_enforced_before_export() {
        let limits = Limits::default();
        let p = program(1);
        let ctx = p.condition_context(&limits).unwrap();
        let small = Limits {
            max_bdd_variables: 2,
            ..limits.clone()
        };
        assert!(EquationContext::new(&ctx, 2, 0, &mut Budget::new(&small)).is_err());
        let small = Limits {
            max_condition_nodes: 4,
            ..limits.clone()
        };
        let mut budget = Budget::new(&small);
        let eq = EquationContext::new(&ctx, 1, 0, &mut budget).unwrap();
        let v = eq.variable(0, &mut budget).unwrap();
        assert!(eq.constant(true, &mut budget).is_err());
        drop(v);
        assert!(eq.constant(true, &mut budget).is_ok());
        let mut budget = Budget::new(&limits);
        let eq = EquationContext::new(&ctx, 1, 0, &mut budget).unwrap();
        let v = eq.variable(0, &mut budget).unwrap();
        let exhausted = Limits {
            max_work: 0,
            ..limits
        };
        assert!(matches!(
            eq.eliminate(v, &mut Budget::new(&exhausted)),
            Err(CheckError::LimitExceeded { .. })
        ));
        assert_eq!(eq.live.get(), 0);
    }
}
