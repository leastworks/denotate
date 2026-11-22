//! Bounded planning under sound path pins. A split returns exactly its declared
//! bindings; its parent resumes under the parent's context, never one child's.
use super::*;
use crate::build::{Work, convert, dependencies, room};
use denotate_check::{CheckError, GroundAtom, Inconclusive, stable_query::*};
use denotate_ir::SemanticKeys;
use std::cmp::Reverse;

type Rules = BTreeMap<AtomKey, Vec<Rule>>;
type Facts = BTreeMap<AtomKey, bool>;
type Set = BTreeSet<AtomKey>;
#[derive(Debug)]
pub(super) enum Failure {
    Check(CheckError),
    Oracle(Inconclusive),
    Problem(Problem),
}
impl From<CheckError> for Failure {
    fn from(e: CheckError) -> Self {
        Self::Check(e)
    }
}
type Result<T> = std::result::Result<T, Failure>;
pub(super) struct Search<'a, 'b> {
    engine: &'a mut Engine,
    keys: &'a SemanticKeys,
    atoms: &'a BTreeMap<AtomKey, GroundAtom>,
    rules: &'a Rules,
    fixed: &'a Facts,
    tasks: &'a crate::task::Tasks,
    options: &'a Options,
    budget: &'a mut Work<'b>,
    nodes: usize,
    calls: usize,
    splits: usize,
    trials: usize,
}
impl<'a, 'b> Search<'a, 'b> {
    pub fn new(
        engine: &'a mut Engine,
        keys: &'a SemanticKeys,
        atoms: &'a BTreeMap<AtomKey, GroundAtom>,
        rules: &'a Rules,
        fixed: &'a Facts,
        tasks: &'a crate::task::Tasks,
        options: &'a Options,
        budget: &'a mut Work<'b>,
    ) -> Self {
        Self {
            engine,
            keys,
            atoms,
            rules,
            fixed,
            tasks,
            options,
            budget,
            nodes: 0,
            calls: 0,
            splits: 0,
            trials: 0,
        }
    }
    fn query(&self, facts: &Facts) -> Query {
        Query {
            pins: facts
                .iter()
                .filter_map(|(k, v)| self.atoms.get(k).map(|a| (a.clone(), *v)))
                .collect(),
            ..Query::default()
        }
    }
    fn call(&mut self) -> Result<()> {
        room(self.calls, self.options.max_oracle_calls, "oracle calls")?;
        self.calls += 1;
        self.budget.tick(1)?;
        Ok(())
    }
    fn synthesize(
        &mut self,
        key: &AtomKey,
        available: &Set,
        facts: &Facts,
    ) -> Result<SynthesisAnswer> {
        self.call()?;
        let q = self.query(facts);
        let values = available
            .iter()
            .map(|k| self.atoms[k].clone())
            .collect::<Vec<_>>();
        let answer = self
            .engine
            .synthesize(&q, &self.atoms[key], &values, &self.options.oracle)?;
        self.budget.tick(1)?;
        Ok(answer)
    }
    fn support(&mut self, key: &AtomKey, available: &Set) -> Result<Set> {
        // The original cone is conservative even after branch specialization.
        let mut seen = Set::new();
        let mut todo = vec![key.clone()];
        while let Some(k) = todo.pop() {
            self.budget.tick(1)?;
            if !seen.insert(k.clone()) {
                continue;
            }
            if let Some(call) = self.tasks.by_result.get(&k) {
                self.budget.tick(call.arguments.len() + 1)?;
                todo.extend(call.arguments.iter().chain(call.when.iter()).cloned());
            }
            for r in self.rules.get(&k).into_iter().flatten() {
                self.budget.tick(r.body.len() + 1)?;
                todo.extend(r.body.iter().map(|(k, _)| k.clone()));
            }
        }
        seen.remove(key);
        Ok(seen.intersection(available).cloned().collect())
    }
    fn minimize(
        &mut self,
        key: &AtomKey,
        mut expr: stable_query::Expression,
        facts: &Facts,
    ) -> Result<super::Expression> {
        let mut support: Set = expr
            .dependencies()
            .expect("oracle expression")
            .iter()
            .map(|a| AtomKey::from_atom(self.keys, a).map_err(CheckError::from))
            .collect::<std::result::Result<_, _>>()?;
        // Removing a support value needs a new proof. Unknown keeps the previous
        // proven expression. This is deterministic greedy minimization, not minimum size.
        for k in support.clone() {
            if self.trials >= self.options.max_support_trials
                || self.calls >= self.options.max_oracle_calls
            {
                break;
            }
            self.trials += 1;
            let candidate = support.iter().filter(|a| **a != k).cloned().collect();
            if let SynthesisAnswer::Expression(e) = self.synthesize(key, &candidate, facts)? {
                support = e
                    .dependencies()
                    .unwrap()
                    .iter()
                    .map(|a| AtomKey::from_atom(self.keys, a).map_err(CheckError::from))
                    .collect::<std::result::Result<_, _>>()?;
                expr = e;
            }
        }
        let mut converted = convert(expr, self.keys)?;
        if let Term::If {
            atom,
            when_true,
            when_false,
        } = &converted.nodes[converted.root]
        {
            if let (Term::Constant(t), Term::Constant(f)) =
                (&converted.nodes[*when_true], &converted.nodes[*when_false])
            {
                if t != f {
                    let positive = *t;
                    let a = atom.clone();
                    converted = super::Expression {
                        nodes: vec![Term::Read(a)],
                        root: 0,
                    };
                    if !positive {
                        converted.nodes.push(Term::Not(0));
                        converted.root = 1;
                    }
                }
            }
        }
        Ok(converted)
    }
    fn insert(
        &mut self,
        nodes: &mut BTreeMap<AtomKey, Node>,
        available: &mut Set,
        node: Node,
    ) -> Result<()> {
        room(self.nodes, self.options.max_nodes, "plan nodes")?;
        self.nodes += 1;
        self.budget
            .tick(node.inputs.len() + node.outputs().len() + 1)?;
        if !node.inputs.is_subset(available) {
            return Err(CheckError::Internal("plan reads unavailable values").into());
        }
        available.extend(node.outputs());
        nodes.insert(node.id.clone(), node);
        Ok(())
    }
    fn specialize(&mut self, facts: &Facts) -> Result<Rules> {
        let mut result = Rules::new();
        for (k, rs) in self.rules {
            let mut out = Vec::new();
            if !self.fixed.contains_key(k) {
                for r in rs {
                    self.budget.tick(r.body.len() + 1)?;
                    let value = |a: &AtomKey| facts.get(a).or_else(|| self.fixed.get(a));
                    if r.body.iter().any(|(a, p)| value(a).is_some_and(|v| v != p)) {
                        continue;
                    }
                    out.push(Rule {
                        head: k.clone(),
                        source: r.source.clone(),
                        body: r
                            .body
                            .iter()
                            .filter(|(a, _)| value(a).is_none())
                            .cloned()
                            .collect(),
                    });
                }
            }
            if let Some(call) = self.tasks.by_result.get(k) {
                self.budget.tick(call.arguments.len() + 1)?;
                let inactive = call
                    .when
                    .as_ref()
                    .is_some_and(|g| facts.get(g).or_else(|| self.fixed.get(g)) == Some(&false));
                // Scheduling edges only. Never evaluate this as a truth equation
                // or let a one-shot producer enter a relational kernel.
                out = vec![Rule {
                    head: k.clone(),
                    source: denotate_ir::RuleKey::Library(call.task.clone()),
                    body: call
                        .dependencies(inactive)
                        .into_iter()
                        .map(|a| (a, true))
                        .collect(),
                }];
            }
            result.insert(k.clone(), out);
        }
        Ok(result)
    }
    fn needed(&mut self, goals: &Set, available: &Set, rules: &Rules) -> Result<Set> {
        let mut needed = Set::new();
        let mut todo: Vec<_> = goals.iter().cloned().collect();
        while let Some(k) = todo.pop() {
            self.budget.tick(1)?;
            if available.contains(&k) || !needed.insert(k.clone()) {
                continue;
            }
            for r in rules.get(&k).into_iter().flatten() {
                self.budget.tick(r.body.len() + 1)?;
                todo.extend(r.body.iter().map(|(a, _)| a.clone()));
            }
        }
        Ok(needed)
    }
    pub fn region(
        &mut self,
        goals: &Set,
        entry: &Set,
        path: &Facts,
        depth: usize,
    ) -> Result<Region> {
        let mut available = entry.clone();
        let mut nodes = BTreeMap::new();
        let rules = self.specialize(path)?;
        while !goals.is_subset(&available) {
            let needed = self.needed(goals, &available, &rules)?;
            let mut progress = false;
            for k in &needed {
                self.budget.tick(1)?;
                if available.contains(k) {
                    continue;
                }
                if let Some(call) = self.tasks.by_result.get(k) {
                    let inactive = call
                        .when
                        .as_ref()
                        .is_some_and(|g| path.get(g).or_else(|| self.fixed.get(g)) == Some(&false));
                    let inputs = call.dependencies(inactive);
                    if inputs.is_subset(&available) {
                        self.insert(
                            &mut nodes,
                            &mut available,
                            Node {
                                id: call.results.first().unwrap().clone(),
                                inputs,
                                sources: self.tasks.sources[k].clone(),
                                operation: Operation::Call {
                                    call: call.clone(),
                                    inactive,
                                },
                            },
                        )?;
                        progress = true;
                    }
                    continue;
                }
                let rs = rules.get(k).map(Vec::as_slice).unwrap_or(&[]);
                let expr = if let Some(v) = self.fixed.get(k) {
                    Some(super::Expression {
                        nodes: vec![Term::Constant(*v)],
                        root: 0,
                    })
                } else {
                    expression(rs, &available, self.budget)?
                };
                if let Some(expression) = expr {
                    let inputs = dependencies(&expression);
                    let sources = self
                        .rules
                        .get(k)
                        .into_iter()
                        .flatten()
                        .map(|r| r.source.clone())
                        .collect();
                    self.insert(
                        &mut nodes,
                        &mut available,
                        Node {
                            id: k.clone(),
                            inputs,
                            sources,
                            operation: Operation::Compute {
                                output: k.clone(),
                                expression,
                            },
                        },
                    )?;
                    progress = true;
                }
            }
            if progress {
                continue;
            }
            let components = components(&needed, &rules, self.budget)?;
            // Only provider-ready SCCs can be units. Recompute after path pruning,
            // not from the original components: one branch can break several cycles.
            let mut blocked = Vec::new();
            for members in components {
                let rs: Vec<_> = members
                    .iter()
                    .flat_map(|k| rules.get(k).into_iter().flatten().cloned())
                    .collect();
                let external: Set = rs
                    .iter()
                    .flat_map(|r| r.body.iter().map(|(k, _)| k))
                    .filter(|k| !members.contains(*k))
                    .cloned()
                    .collect();
                self.budget
                    .tick(rs.iter().map(|r| r.body.len() + 1).sum())?;
                if !external.is_subset(&available) {
                    continue;
                }
                if !members.iter().any(|k| self.tasks.by_result.contains_key(k))
                    && rs
                        .iter()
                        .all(|r| r.body.iter().all(|(k, p)| *p || !members.contains(k)))
                {
                    let id = members.first().unwrap().clone();
                    let sources = rs.iter().map(|r| r.source.clone()).collect();
                    self.insert(
                        &mut nodes,
                        &mut available,
                        Node {
                            id,
                            inputs: external,
                            sources,
                            operation: Operation::Fixpoint {
                                outputs: members,
                                rules: rs,
                            },
                        },
                    )?;
                    progress = true;
                } else {
                    blocked.push(members);
                }
            }
            if progress {
                continue;
            }
            let mut last = None;
            let mut exhausted = None;
            for k in blocked.iter().flatten() {
                if self.tasks.by_result.contains_key(k) {
                    continue;
                }
                if self.calls >= self.options.max_oracle_calls {
                    break;
                }
                let support = self.support(k, &available)?;
                match self.synthesize(k, &support, path)? {
                    SynthesisAnswer::Expression(e) => {
                        let expression = self.minimize(k, e, path)?;
                        let sources = self.rules[k].iter().map(|r| r.source.clone()).collect();
                        self.insert(
                            &mut nodes,
                            &mut available,
                            Node {
                                id: k.clone(),
                                inputs: dependencies(&expression),
                                sources,
                                operation: Operation::Compute {
                                    output: k.clone(),
                                    expression,
                                },
                            },
                        )?;
                        progress = true;
                        break;
                    }
                    SynthesisAnswer::Inconclusive(e) => exhausted = Some(e),
                    SynthesisAnswer::Infeasible => {
                        return Err(CheckError::Internal(
                            "feasible planning context became infeasible",
                        )
                        .into());
                    }
                    other => last = Some(other),
                }
            }
            if progress {
                continue;
            }
            let mut candidates = Vec::new();
            for (component, members) in blocked.iter().enumerate() {
                let mut scores = BTreeMap::<AtomKey, [usize; 2]>::new();
                for k in members {
                    for r in &rules[k] {
                        self.budget.tick(r.body.len() + 1)?;
                        let edges = r.body.iter().filter(|(a, _)| members.contains(a)).count();
                        if edges == 0 {
                            continue;
                        }
                        for (guard, positive) in &r.body {
                            if available.contains(guard) && !path.contains_key(guard) {
                                if !scores.contains_key(guard) {
                                    room(
                                        candidates.len() + scores.len(),
                                        self.options.max_split_candidates,
                                        "split candidates",
                                    )?;
                                }
                                scores.entry(guard.clone()).or_default()[usize::from(!positive)] +=
                                    edges;
                            }
                        }
                    }
                }
                for k in members {
                    if let Some(call) = self.tasks.by_result.get(k) {
                        if let Some(g) = &call.when {
                            if available.contains(g) && !path.contains_key(g) {
                                if !scores.contains_key(g) {
                                    room(
                                        candidates.len() + scores.len(),
                                        self.options.max_split_candidates,
                                        "split candidates",
                                    )?;
                                }
                                scores.entry(g.clone()).or_default()[0] += call
                                    .arguments
                                    .iter()
                                    .filter(|a| members.contains(*a))
                                    .count();
                            }
                        }
                    }
                }
                for (k, s) in scores {
                    candidates.push((Reverse(s[0].min(s[1])), Reverse(s[0] + s[1]), k, component));
                }
            }
            self.budget.tick(candidates.len())?;
            candidates.sort();
            if let Some((_, _, guard, component)) = candidates.first() {
                let members = &blocked[*component];
                // A task branch owns the remaining continuation. No private
                // producer state can disappear at a join and trigger a second call.
                let joined = if !self
                    .tasks
                    .by_result
                    .keys()
                    .any(|k| self.atoms.contains_key(k))
                {
                    members.clone()
                } else {
                    goals.difference(&available).cloned().collect()
                };
                // Hard ceiling also bounds native recursion and recursive artifact
                // drop/serialization. No arbitrarily deep user-supplied cap.
                room(depth, self.options.max_split_depth.min(64), "split depth")?;
                room(self.splits, self.options.max_splits, "splits")?;
                self.splits += 1;
                let mut arms = Vec::new();
                for value in [true, false] {
                    let mut facts = path.clone();
                    facts.insert(guard.clone(), value);
                    // Unique scoped meaning was established before search.
                    // Thus absence of a stable model here means an infeasible path,
                    // not a lost permitted world. Unknown never removes an arm.
                    self.call()?;
                    let answer = self.engine.feasible(&self.query(&facts))?;
                    self.budget.tick(1)?;
                    arms.push(match answer {
                        Answer::NoModel => None,
                        Answer::Inconclusive(e) => return Err(Failure::Oracle(e)),
                        Answer::Model(_) => Some(Box::new(self.region(
                            &joined,
                            &available,
                            &facts,
                            depth + 1,
                        )?)),
                    });
                }
                if arms.iter().all(Option::is_none) {
                    return Err(CheckError::Internal("split removed every feasible world").into());
                }
                if arms.iter().any(Option::is_none) {
                    // The surviving arm's pin is implied by the parent context.
                    // Inline its work instead of emitting a pointless branch.
                    let arm = arms.into_iter().flatten().next().unwrap();
                    for (id, node) in arm.nodes {
                        self.budget.tick(node.outputs().len() + 1)?;
                        if node.outputs().iter().any(|k| available.contains(k)) {
                            return Err(
                                CheckError::Internal("inlined arm redefines a binding").into()
                            );
                        }
                        available.extend(node.outputs());
                        nodes.insert(id, node);
                    }
                    continue;
                }
                let mut inputs = Set::from([guard.clone()]);
                let mut sources = BTreeSet::new();
                for arm in arms.iter().flatten() {
                    inputs.extend(external(&arm.nodes, &joined));
                    sources.extend(arm.nodes.values().flat_map(|n| n.sources.iter().cloned()));
                }
                let when_false = arms.pop().unwrap();
                let when_true = arms.pop().unwrap();
                self.insert(
                    &mut nodes,
                    &mut available,
                    Node {
                        id: joined.first().unwrap().clone(),
                        inputs,
                        sources,
                        operation: Operation::Split {
                            on: guard.clone(),
                            outputs: joined,
                            when_true,
                            when_false,
                        },
                    },
                )?;
                continue;
            }
            if let Some(e) = exhausted {
                return Err(Failure::Oracle(e));
            }
            if self.calls >= self.options.max_oracle_calls {
                return Err(CheckError::limit(
                    "plan construction",
                    "oracle calls",
                    self.options.max_oracle_calls,
                    Some(self.calls + 1),
                )
                .into());
            }
            self.call()?;
            let witness = self.engine.feasible(&self.query(path))?;
            self.budget.tick(1)?;
            let world = match witness {
                Answer::Model(m) => Some(m),
                Answer::Inconclusive(e) => return Err(Failure::Oracle(e)),
                Answer::NoModel => None,
            };
            let dependencies = needed
                .iter()
                .flat_map(|k| {
                    rules
                        .get(k)
                        .into_iter()
                        .flatten()
                        .flat_map(|r| r.body.iter().map(|(a, p)| (k.clone(), a.clone(), *p)))
                })
                .collect();
            return Err(Failure::Problem(Problem::Unresolved {
                atoms: needed.into_iter().collect(),
                answer: last,
                path: path.clone(),
                dependencies,
                world,
            }));
        }
        // Keep the join's declared bindings and all of their providers, not unused
        // temporary values generated while making progress elsewhere.
        let providers: BTreeMap<_, _> = nodes
            .iter()
            .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id.clone())))
            .collect();
        let mut keep = Set::new();
        let mut todo: Vec<_> = goals.iter().cloned().collect();
        while let Some(k) = todo.pop() {
            self.budget.tick(1)?;
            if let Some(id) = providers.get(&k) {
                if keep.insert(id.clone()) {
                    todo.extend(nodes[id].inputs.iter().cloned());
                }
            }
        }
        nodes.retain(|k, _| keep.contains(k));
        Ok(Region { nodes })
    }
}
// External reads include passthrough goal bindings. A child's private temporaries
// never become a parent's available values merely because one arm computed them.
pub(super) fn external(nodes: &BTreeMap<AtomKey, Node>, goals: &Set) -> Set {
    let produced: Set = nodes.values().flat_map(Node::outputs).collect();
    goals
        .iter()
        .chain(nodes.values().flat_map(|n| n.inputs.iter()))
        .filter(|k| !produced.contains(*k))
        .cloned()
        .collect()
}
pub(super) fn expression(
    rules: &[Rule],
    available: &Set,
    budget: &mut Work<'_>,
) -> std::result::Result<Option<super::Expression>, CheckError> {
    let mut bodies = Vec::new();
    let mut unavailable = false;
    for r in rules {
        budget.tick(r.body.len() + 1)?;
        // One unconditional producer settles truth even if another producer is
        // still cyclic. Specialization commonly exposes this after a split.
        if r.body.is_empty() {
            return Ok(Some(super::Expression {
                nodes: vec![Term::Constant(true)],
                root: 0,
            }));
        }
        unavailable |= r.body.iter().any(|(k, _)| !available.contains(k));
        bodies.push(r.body.clone());
    }
    if unavailable {
        return Ok(None);
    }
    bodies.sort();
    bodies.dedup();
    let mut nodes = Vec::new();
    let mut alternatives = Vec::new();
    for body in bodies {
        let mut terms = Vec::new();
        for (k, p) in body {
            nodes.push(Term::Read(k));
            if !p {
                nodes.push(Term::Not(nodes.len() - 1));
            }
            terms.push(nodes.len() - 1);
        }
        nodes.push(Term::And(terms));
        alternatives.push(nodes.len() - 1);
    }
    nodes.push(Term::Or(alternatives));
    budget.tick(nodes.len())?;
    Ok(Some(super::Expression {
        root: nodes.len() - 1,
        nodes,
    }))
}
// Iterative Kosaraju, over residual unavailable dependencies only. No recursive
// graph walk, and no relation-level approximation of a ground cycle.
fn components(needed: &Set, rules: &Rules, budget: &mut Work<'_>) -> Result<Vec<Set>> {
    let mut adjacent = BTreeMap::<AtomKey, Set>::new();
    let mut reverse = BTreeMap::<AtomKey, Set>::new();
    for k in needed {
        for r in rules.get(k).into_iter().flatten() {
            for (a, _) in &r.body {
                budget.tick(1)?;
                if needed.contains(a) {
                    adjacent.entry(k.clone()).or_default().insert(a.clone());
                    reverse.entry(a.clone()).or_default().insert(k.clone());
                }
            }
        }
    }
    let mut seen = Set::new();
    let mut finish = Vec::new();
    for root in needed {
        let mut stack = vec![(root.clone(), false)];
        while let Some((k, exit)) = stack.pop() {
            budget.tick(1)?;
            if exit {
                finish.push(k);
                continue;
            }
            if !seen.insert(k.clone()) {
                continue;
            }
            stack.push((k.clone(), true));
            if let Some(next) = adjacent.get(&k) {
                stack.extend(next.iter().rev().map(|a| (a.clone(), false)));
            }
        }
    }
    seen.clear();
    let mut out = Vec::new();
    for root in finish.into_iter().rev() {
        if seen.contains(&root) {
            continue;
        }
        let mut members = Set::new();
        let mut stack = vec![root];
        while let Some(k) = stack.pop() {
            budget.tick(1)?;
            if !seen.insert(k.clone()) {
                continue;
            }
            members.insert(k.clone());
            if let Some(next) = reverse.get(&k) {
                stack.extend(next.iter().cloned());
            }
        }
        out.push(members);
    }
    out.sort_by(|a, b| a.first().cmp(&b.first()));
    Ok(out)
}
