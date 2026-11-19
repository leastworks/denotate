//! Bounded, verification-local queries for a future execution driver.
use super::*;
mod expression;
pub use expression::{Expression, ExpressionNode};

/// Allowances per compound oracle call, in addition to the engine's query/CNF caps.
#[derive(Debug, Clone)]
pub struct OracleLimits {
    pub max_queries: usize,
    pub max_branches: usize,
    pub max_expression_nodes: usize,
    pub max_available: usize,
}
impl Default for OracleLimits {
    fn default() -> Self {
        Self {
            max_queries: 256,
            max_branches: 128,
            max_expression_nodes: 1024,
            max_available: 64,
        }
    }
}
#[derive(Debug, Clone)]
pub enum ConstantAnswer {
    Constant(bool),
    Varying {
        when_true: Model,
        when_false: Model,
    },
    /// No full-program stable model satisfies the context; not a no-permitted-world claim.
    Infeasible,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Clone)]
pub enum EquivalenceAnswer {
    Equivalent,
    Counterexample(Model),
    Infeasible,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Clone)]
pub enum SynthesisAnswer {
    Expression(Expression),
    /// Two stable models agree on every available value but disagree on the target.
    /// They may belong to different input worlds.
    NotDetermined {
        when_true: Model,
        when_false: Model,
    },
    Infeasible,
    Inconclusive(Inconclusive),
}
struct Work<'a> {
    b: Budget<'a>,
    limits: &'a OracleLimits,
    queries: usize,
    branches: usize,
}
impl Work<'_> {
    fn query(&mut self) -> Result<()> {
        self.b.room(
            self.queries,
            self.limits.max_queries,
            "SAT oracle",
            "queries",
        )?;
        self.queries += 1;
        Ok(())
    }
    fn context(&mut self, q: &Query) -> Result<Query> {
        // Charge before cloning caller-owned contexts, including exclusions.
        self.b.tick("SAT oracle context")?;
        for (a, _) in q.pins.iter().chain(q.exclude.iter().flatten()) {
            self.b.charge(a.arguments.len() + 1, "SAT oracle context")?;
        }
        self.b.charge(q.exclude.len(), "SAT oracle context")?;
        Ok(q.clone())
    }
}
impl Engine {
    /// Feasibility among stable interpretations. Use `worlds` instead to ask about
    /// permitted inputs independently of whether the program has a meaning there.
    pub fn feasible(&mut self, context: &Query) -> Result<Answer> {
        self.models(context)
    }
    /// Prove a constant under a context, or return interpretations of both values.
    /// A proof says nothing about meaning existence/uniqueness in every input world.
    pub fn constant(
        &mut self,
        context: &Query,
        target: &GroundAtom,
        allowance: &OracleLimits,
    ) -> Result<ConstantAnswer> {
        let limits = self.limits.clone();
        let mut w = Work {
            b: Budget::new(&limits),
            limits: allowance,
            queries: 0,
            branches: 0,
        };
        match self.constant_using(context, target, &mut w) {
            Ok(a) => Ok(a),
            Err(e) => Ok(ConstantAnswer::Inconclusive(query_inconclusive(e)?)),
        }
    }
    fn constant_using(
        &mut self,
        context: &Query,
        target: &GroundAtom,
        w: &mut Work<'_>,
    ) -> Result<ConstantAnswer> {
        w.b.charge(target.arguments.len() + 1, "SAT oracle target")?;
        resolve(&self.program, target)?;
        w.query()?;
        let first = match self.phase_query(Mode::Program, context, &mut w.b)? {
            Answer::Model(m) => m,
            Answer::NoModel => return Ok(ConstantAnswer::Infeasible),
            Answer::Inconclusive(c) => return Ok(ConstantAnswer::Inconclusive(c)),
        };
        let value = first.value(target).expect("validated target");
        let mut opposite = w.context(context)?;
        opposite.pins.push((target.clone(), !value));
        w.query()?;
        Ok(
            match self.phase_query(Mode::Program, &opposite, &mut w.b)? {
                Answer::NoModel => ConstantAnswer::Constant(value),
                Answer::Inconclusive(c) => ConstantAnswer::Inconclusive(c),
                Answer::Model(second) => {
                    let (when_true, when_false) = if value {
                        (first, second)
                    } else {
                        (second, first)
                    };
                    ConstantAnswer::Varying {
                        when_true,
                        when_false,
                    }
                }
            },
        )
    }
    fn available(&self, atoms: &[GroundAtom], w: &mut Work<'_>) -> Result<Vec<GroundAtom>> {
        let mut seen = BTreeSet::new();
        let mut ordered = Vec::new();
        for a in atoms {
            w.b.charge(a.arguments.len() + 1, "SAT oracle available values")?;
            resolve(&self.program, a)?;
            if !seen.contains(a) {
                w.b.room(
                    ordered.len(),
                    w.limits.max_available,
                    "SAT oracle",
                    "available values",
                )?;
                seen.insert(a.clone());
                ordered.push(a.clone());
            }
        }
        Ok(ordered)
    }
    /// Check x = E in every stable model of C. Every expression leaf must be in K;
    /// K carries availability, not truth. Empty contexts are reported separately.
    pub fn equivalent(
        &mut self,
        context: &Query,
        target: &GroundAtom,
        available: &[GroundAtom],
        expression: &Expression,
        allowance: &OracleLimits,
    ) -> Result<EquivalenceAnswer> {
        let limits = self.limits.clone();
        let mut w = Work {
            b: Budget::new(&limits),
            limits: allowance,
            queries: 0,
            branches: 0,
        };
        let result = (|| {
            let available = self
                .available(available, &mut w)?
                .into_iter()
                .collect::<BTreeSet<_>>();
            w.b.charge(target.arguments.len() + 1, "SAT oracle target")?;
            resolve(&self.program, target)?;
            self.validate_expression(expression, &available, &mut w)?;
            w.query()?;
            match self.phase_query(Mode::Program, context, &mut w.b)? {
                Answer::NoModel => return Ok(EquivalenceAnswer::Infeasible),
                Answer::Inconclusive(c) => return Ok(EquivalenceAnswer::Inconclusive(c)),
                Answer::Model(_) => (),
            }
            w.query()?;
            Ok(
                match self.mismatch(context, target, expression, &mut w.b)? {
                    Answer::NoModel => EquivalenceAnswer::Equivalent,
                    Answer::Model(m) => EquivalenceAnswer::Counterexample(m),
                    Answer::Inconclusive(c) => EquivalenceAnswer::Inconclusive(c),
                },
            )
        })();
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(EquivalenceAnswer::Inconclusive(query_inconclusive(e)?)),
        }
    }
    fn validate_expression(
        &self,
        expression: &Expression,
        available: &BTreeSet<GroundAtom>,
        w: &mut Work<'_>,
    ) -> Result<()> {
        if expression.root >= expression.nodes.len() {
            return Err(CheckError::InvalidRequest(
                "expression root is out of range",
            ));
        }
        for (i, n) in expression.nodes.iter().enumerate() {
            w.b.room(
                i,
                w.limits.max_expression_nodes,
                "SAT oracle",
                "expression nodes",
            )?;
            w.b.charge(n.children().len() + 1, "SAT oracle expression")?;
            if !n.valid_at(i) {
                return Err(CheckError::InvalidRequest(
                    "expression children must precede their parent",
                ));
            }
            if let Some(a) = n.atom() {
                w.b.charge(a.arguments.len() + 1, "SAT oracle expression")?;
                if !available.contains(a) {
                    return Err(CheckError::InvalidRequest(
                        "expression uses an unavailable value",
                    ));
                }
            }
        }
        Ok(())
    }
    fn mismatch(
        &mut self,
        context: &Query,
        target: &GroundAtom,
        expression: &Expression,
        b: &mut Budget<'_>,
    ) -> Result<Answer> {
        if let Some(e) = &self.append_failed {
            return Ok(Answer::Inconclusive(query_inconclusive(e.clone())?));
        }
        self.stats = Stats::default();
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let timeout = self.cnf.solver.cb().timeout;
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.timeout = timeout.min(b.remaining_time());
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result = (|| {
            let key = self.key(Mode::Program, context, b)?;
            let gate = self.append_query(&key, b)?;
            let appended = (|| {
                let atom = |a: &GroundAtom| -> Result<Lit> {
                    Ok(match resolve(&self.program, a)? {
                        Resolved::Fixed(v) => {
                            if v {
                                self.truth
                            } else {
                                !self.truth
                            }
                        }
                        Resolved::Atom(i) => self.program_encoding.vars[i],
                    })
                };
                let mut nodes = Vec::<Lit>::new();
                for n in &expression.nodes {
                    b.tick("SAT oracle expression encoding")?;
                    nodes.push(match n {
                        ExpressionNode::Constant(v) => {
                            if *v {
                                self.truth
                            } else {
                                !self.truth
                            }
                        }
                        ExpressionNode::Atom(a) => atom(a)?,
                        ExpressionNode::Not(i) => !nodes[*i],
                        ExpressionNode::And(js) => self
                            .cnf
                            .and(&js.iter().map(|j| nodes[*j]).collect::<Vec<_>>(), b)?,
                        ExpressionNode::Or(js) => self
                            .cnf
                            .or(&js.iter().map(|j| nodes[*j]).collect::<Vec<_>>(), b)?,
                        ExpressionNode::If {
                            atom: a,
                            when_true,
                            when_false,
                        } => {
                            let l = atom(a)?;
                            let yes = self.cnf.and(&[l, nodes[*when_true]], b)?;
                            let no = self.cnf.and(&[!l, nodes[*when_false]], b)?;
                            self.cnf.or(&[yes, no], b)?
                        }
                    });
                }
                let x = atom(target)?;
                let e = nodes[expression.root];
                // x XOR E, under this query's selector only.
                self.cnf.clause(vec![x, e], b)?;
                self.cnf.clause(vec![!x, !e], b)
            })();
            if let Err(e) = appended {
                self.append_failed = Some(e.clone());
                return Err(e);
            }
            self.search(
                Mode::Program,
                &[self.active, gate],
                conflicts,
                propagations,
                b,
            )
        })();
        self.cnf.solver.cb_mut().timeout = timeout;
        self.stats.variables = self.cnf.solver.num_vars() as usize;
        self.stats.clauses = self.cnf.clauses;
        self.stats.literals = self.cnf.literals;
        self.stats.conflicts = self.cnf.solver.num_conflicts() - conflicts;
        self.stats.propagations = self.cnf.solver.num_propagations() - propagations;
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(Answer::Inconclusive(query_inconclusive(
                e.in_phase("SAT oracle equivalence", None),
            )?)),
        }
    }
    /// Bounded Shannon synthesis in caller-supplied available-value order. Equal
    /// branches and repeated nodes are shared. Only stable-feasible branches matter;
    /// other branches are don't-cares, not a proof of totality or runtime readiness.
    pub fn synthesize(
        &mut self,
        context: &Query,
        target: &GroundAtom,
        available: &[GroundAtom],
        allowance: &OracleLimits,
    ) -> Result<SynthesisAnswer> {
        let limits = self.limits.clone();
        let mut w = Work {
            b: Budget::new(&limits),
            limits: allowance,
            queries: 0,
            branches: 0,
        };
        let result = (|| {
            let available = self.available(available, &mut w)?;
            enum Task {
                Visit(Query, usize),
                Join(GroundAtom),
            }
            let mut tasks = vec![Task::Visit(w.context(context)?, 0)];
            let mut results = Vec::<Option<usize>>::new();
            let mut nodes = Vec::new();
            let mut intern = BTreeMap::new();
            while let Some(task) = tasks.pop() {
                w.b.tick("SAT oracle synthesis")?;
                let node = match task {
                    Task::Visit(q, index) => match self.constant_using(&q, target, &mut w)? {
                        ConstantAnswer::Infeasible => {
                            results.push(None);
                            continue;
                        }
                        ConstantAnswer::Inconclusive(c) => {
                            return Ok(SynthesisAnswer::Inconclusive(c));
                        }
                        ConstantAnswer::Constant(v) => ExpressionNode::Constant(v),
                        ConstantAnswer::Varying {
                            when_true,
                            when_false,
                        } => {
                            let Some(a) = available.get(index) else {
                                return Ok(SynthesisAnswer::NotDetermined {
                                    when_true,
                                    when_false,
                                });
                            };
                            w.b.room(w.branches, w.limits.max_branches, "SAT oracle", "branches")?;
                            w.branches += 1;
                            let mut no = w.context(&q)?;
                            let mut yes = q;
                            no.pins.push((a.clone(), false));
                            yes.pins.push((a.clone(), true));
                            tasks.push(Task::Join(a.clone()));
                            tasks.push(Task::Visit(yes, index + 1));
                            tasks.push(Task::Visit(no, index + 1));
                            continue;
                        }
                    },
                    Task::Join(atom) => {
                        let yes = results.pop().unwrap();
                        let no = results.pop().unwrap();
                        match (yes, no) {
                            (None, other) | (other, None) => {
                                results.push(other);
                                continue;
                            }
                            (Some(y), Some(n)) if y == n => {
                                results.push(Some(y));
                                continue;
                            }
                            (Some(when_true), Some(when_false)) => ExpressionNode::If {
                                atom,
                                when_true,
                                when_false,
                            },
                        }
                    }
                };
                let id = if let Some(id) = intern.get(&node) {
                    *id
                } else {
                    w.b.room(
                        nodes.len(),
                        w.limits.max_expression_nodes,
                        "SAT oracle",
                        "expression nodes",
                    )?;
                    let id = nodes.len();
                    intern.insert(node.clone(), id);
                    nodes.push(node);
                    id
                };
                results.push(Some(id));
            }
            match results.pop().unwrap() {
                None => Ok(SynthesisAnswer::Infeasible),
                Some(root) => {
                    w.b.charge(nodes.len(), "SAT oracle expression compaction")?;
                    Ok(SynthesisAnswer::Expression(
                        Expression { nodes, root }.compact(),
                    ))
                }
            }
        })();
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(SynthesisAnswer::Inconclusive(query_inconclusive(e)?)),
        }
    }
}
#[cfg(test)]
mod tests;
