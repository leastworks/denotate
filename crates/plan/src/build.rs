use super::*;
use denotate_check::{CheckError, Domains, GroundAtom, GroundRule, Limits, Polarity};
use denotate_ir::{Corpus, SemanticKeys, VerificationId};
use stable_query::{
    Answer, CheckOptions, Meaning, OracleLimits, Query, QueryLimits, SynthesisAnswer,
};
use std::time::Instant;
type Result<T> = std::result::Result<T, CheckError>;

#[derive(Debug, Clone)]
pub struct Output {
    pub atom: GroundAtom,
    /// Lower numbers are scheduled first among ready work. Never a truth assumption.
    pub priority: u32,
}
#[derive(Debug, Clone)]
pub struct Options {
    pub max_nodes: usize,
    pub max_oracle_calls: usize,
    pub oracle: OracleLimits,
    pub meaning: CheckOptions,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            max_nodes: 100_000,
            max_oracle_calls: 256,
            oracle: OracleLimits::default(),
            meaning: CheckOptions::default(),
        }
    }
}
#[derive(Debug)]
pub enum Problem {
    /// Includes replayable no-meaning or ambiguity observations when established.
    Meaning(Meaning),
    /// Only bounded strategies were tried. This is not an impossibility proof.
    Unresolved {
        atoms: Vec<AtomKey>,
        answer: SynthesisAnswer,
    },
}
#[derive(Debug)]
pub enum Build {
    Ready(Plan),
    NoPermittedWorlds,
    Problem(Problem),
    Inconclusive(CheckError),
    OracleInconclusive(denotate_check::Inconclusive),
}

/// Owns one immutable verification engine. Repeated builds may reuse its query
/// cache; program/domain/selection edits require a new Planner.
pub struct Planner<'a> {
    corpus: &'a Corpus,
    keys: &'a SemanticKeys,
    verification: VerificationId,
    limits: Limits,
    engine: stable_query::Engine,
}
impl<'a> Planner<'a> {
    /// Expand a declared output relation over the resolved finite domains,
    /// including legal tuples that have no producer (and therefore are false).
    pub fn relation_outputs(
        &self,
        relation: denotate_ir::RelationId,
        priority: u32,
    ) -> Result<Vec<Output>> {
        let r = self
            .corpus
            .relation(relation)
            .ok_or(CheckError::InvalidRequest("unknown output relation"))?;
        let mut budget = Work {
            limits: &self.limits,
            start: Instant::now(),
            work: 0,
        };
        let mut tuples = vec![vec![]];
        for parameter in &r.parameters {
            let domain = self
                .engine
                .program()
                .domain(parameter.sort)
                .ok_or(CheckError::InvalidRequest("missing output domain"))?;
            let mut next = Vec::new();
            for tuple in &tuples {
                for value in domain {
                    budget.tick(tuple.len() + 1)?;
                    room(next.len(), self.limits.max_atoms, "output atoms")?;
                    let mut t = tuple.clone();
                    t.push(*value);
                    next.push(t);
                }
            }
            tuples = next;
        }
        Ok(tuples
            .into_iter()
            .map(|t| Output {
                atom: GroundAtom::new(relation, t),
                priority,
            })
            .collect())
    }
    pub fn prepare(
        corpus: &'a Corpus,
        domains: &Domains,
        keys: &'a SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        queries: QueryLimits,
    ) -> Result<Self> {
        Ok(Self {
            corpus,
            keys,
            verification,
            limits: limits.clone(),
            engine: stable_query::Engine::prepare(
                corpus,
                domains,
                keys,
                verification,
                limits,
                queries,
            )?,
        })
    }
    pub fn build(&mut self, outputs: &[Output], options: &Options) -> Result<Build> {
        match self.build_inner(outputs, options) {
            Err(e @ (CheckError::LimitExceeded { .. } | CheckError::Deadline { .. })) => {
                Ok(Build::Inconclusive(e))
            }
            other => other,
        }
    }
    fn build_inner(&mut self, outputs: &[Output], options: &Options) -> Result<Build> {
        if outputs.is_empty() {
            return Err(CheckError::InvalidRequest("plan requires explicit outputs"));
        }
        if options.meaning.meaning != stable_query::MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "plan requires full existence and uniqueness checking",
            ));
        }
        let limits = self.limits.clone();
        let mut budget = Work {
            limits: &limits,
            start: Instant::now(),
            work: 0,
        };
        let mut requested = BTreeMap::new();
        for output in outputs {
            budget.tick(1)?;
            self.engine.prepared_value(&output.atom)?; // validate even with an empty context
            let key = AtomKey::from_atom(self.keys, &output.atom)?;
            requested
                .entry(key)
                .and_modify(|p: &mut u32| *p = (*p).min(output.priority))
                .or_insert(output.priority);
        }
        if self.engine.program().input_universe_is_empty() {
            return Ok(Build::NoPermittedWorlds);
        }
        match self.engine.worlds(&Query::default())? {
            Answer::NoModel => return Ok(Build::NoPermittedWorlds),
            Answer::Inconclusive(e) => return Ok(Build::OracleInconclusive(e)),
            Answer::Model(_) => {}
        }
        budget.tick(1)?;
        let meaning = self.engine.meaning(&options.meaning)?;
        budget.tick(1)?;
        if !meaning.unique_everywhere() {
            use stable_query::{Existence, Uniqueness};
            // Preserve a known semantic failure even if the other phase exhausted.
            if matches!(meaning.existence, Existence::NoMeaning(_))
                || matches!(meaning.uniqueness, Uniqueness::Multiple { .. })
            {
                return Ok(Build::Problem(Problem::Meaning(meaning)));
            }
            if let Existence::Inconclusive(e) = meaning.existence {
                return Ok(Build::OracleInconclusive(e));
            }
            if let Uniqueness::Inconclusive(e) = meaning.uniqueness {
                return Ok(Build::OracleInconclusive(e));
            }
            return Err(CheckError::Internal("full meaning check omitted a phase"));
        }

        // Index the existing grounded graph once. Do not copy its rules or build
        // whole-program structural semantic keys just to plan a small output cone.
        let graph = self.engine.program().clone();
        let mut producers = BTreeMap::<GroundAtom, Vec<&GroundRule>>::new();
        for rule in graph.rules() {
            budget.tick(rule.body.len() + 1)?;
            producers
                .entry(rule.head.atom.clone())
                .or_default()
                .push(rule);
        }
        let input_atoms: BTreeSet<_> = graph.input_atoms().cloned().collect();
        let mut atoms = BTreeMap::new();
        let mut pending: Vec<_> = outputs.iter().map(|o| o.atom.clone()).collect();
        while let Some(atom) = pending.pop() {
            budget.tick(1)?;
            let key = AtomKey::from_atom(self.keys, &atom)?;
            if atoms.contains_key(&key) {
                continue;
            }
            if !input_atoms.contains(&atom) && self.engine.prepared_value(&atom)?.is_none() {
                for rule in producers.get(&atom).into_iter().flatten() {
                    budget.tick(rule.body.len())?;
                    pending.extend(rule.body.iter().map(|l| l.term.atom.clone()));
                }
            }
            atoms.insert(key, atom);
        }
        let mut available = BTreeSet::new();
        let mut nodes = BTreeMap::new();
        for (key, atom) in &atoms {
            if input_atoms.contains(atom) {
                available.insert(key.clone());
            }
        }
        let inputs = available.clone();
        let needed_atoms: BTreeSet<_> = atoms.values().collect();
        let mut oracle_calls = 0usize;
        while requested.keys().any(|k| !available.contains(k)) {
            let mut progress = false;
            for (key, atom) in &atoms {
                budget.tick(1)?;
                if available.contains(key) {
                    continue;
                }
                let source_rules = producers.get(atom).map(Vec::as_slice).unwrap_or(&[]);
                let sources = source_rules
                    .iter()
                    .map(|r| self.keys.rule(r.source).cloned())
                    .collect::<std::result::Result<_, _>>()?;
                let expr = if let Some(value) = self.engine.prepared_value(atom)? {
                    Some(Expression {
                        nodes: vec![Term::Constant(value)],
                        root: 0,
                    })
                } else {
                    rule_expression(source_rules, self.keys, &available, &mut budget)?
                };
                if let Some(expr) = expr {
                    insert_compute(
                        &mut nodes,
                        &mut available,
                        key,
                        expr,
                        sources,
                        options,
                        &mut budget,
                    )?;
                    progress = true;
                }
            }
            if progress {
                continue;
            }
            // A pure positive SCC with settled external premises is directly
            // executable; it does not need an input formula or SAT proof.
            for component in graph.components() {
                budget.tick(component.atoms.len() + 1)?;
                if !component.recursive || component.cycle.is_some() {
                    continue;
                }
                if component.atoms.iter().all(|a| !needed_atoms.contains(a)) {
                    continue;
                }
                let members: BTreeSet<_> = component
                    .atoms
                    .iter()
                    .map(|a| AtomKey::from_atom(self.keys, a))
                    .collect::<std::result::Result<_, _>>()?;
                if members
                    .iter()
                    .all(|k| !atoms.contains_key(k) || available.contains(k))
                {
                    continue;
                }
                if members.iter().any(|k| available.contains(k)) {
                    continue;
                }
                let mut rules = Vec::new();
                let mut external = BTreeSet::new();
                let mut ready = true;
                for a in &component.atoms {
                    for r in producers.get(a).into_iter().flatten() {
                        budget.tick(r.body.len() + 1)?;
                        let mut body = Vec::new();
                        for l in &r.body {
                            let k = AtomKey::from_atom(self.keys, &l.term.atom)?;
                            let positive = l.polarity == Polarity::Positive;
                            if members.contains(&k) {
                                ready &= positive;
                            } else {
                                ready &= available.contains(&k);
                                external.insert(k.clone());
                            }
                            body.push((k, positive));
                        }
                        body.sort();
                        body.dedup();
                        rules.push(Rule {
                            head: AtomKey::from_atom(self.keys, a)?,
                            body,
                            source: self.keys.rule(r.source)?.clone(),
                        });
                    }
                }
                if ready {
                    room(nodes.len(), options.max_nodes, "plan nodes")?;
                    rules.sort_by(|a, b| {
                        (&a.head, &a.source, &a.body).cmp(&(&b.head, &b.source, &b.body))
                    });
                    let id = members.first().unwrap().clone();
                    let sources = rules.iter().map(|r| r.source.clone()).collect();
                    nodes.insert(
                        id.clone(),
                        Node {
                            id,
                            inputs: external,
                            sources,
                            operation: Operation::Fixpoint {
                                outputs: members.clone(),
                                rules,
                            },
                        },
                    );
                    available.extend(members);
                    progress = true;
                }
            }
            if progress {
                continue;
            }
            // Only still-needed values are queried. Availability supplies values,
            // never truth pins. Semantic-key order makes synthesis reproducible.
            let values: Vec<_> = available
                .iter()
                .filter_map(|k| atoms.get(k).cloned())
                .collect();
            let remaining: Vec<_> = atoms
                .keys()
                .filter(|k| !available.contains(*k))
                .cloned()
                .collect();
            let mut last = None;
            let mut exhausted = None;
            for key in &remaining {
                room(oracle_calls, options.max_oracle_calls, "oracle calls")?;
                oracle_calls += 1;
                let answer = self.engine.synthesize(
                    &Query::default(),
                    &atoms[key],
                    &values,
                    &options.oracle,
                )?;
                budget.tick(1)?;
                if let SynthesisAnswer::Expression(expr) = answer {
                    let expr = convert(expr, self.keys)?;
                    let sources = producers
                        .get(&atoms[key])
                        .into_iter()
                        .flatten()
                        .map(|r| self.keys.rule(r.source).cloned())
                        .collect::<std::result::Result<_, _>>()?;
                    insert_compute(
                        &mut nodes,
                        &mut available,
                        key,
                        expr,
                        sources,
                        options,
                        &mut budget,
                    )?;
                    progress = true;
                    break;
                }
                match answer {
                    SynthesisAnswer::Inconclusive(e) => exhausted = Some(e),
                    SynthesisAnswer::Infeasible => {
                        return Err(CheckError::Internal(
                            "meaning proved but synthesis context infeasible",
                        ));
                    }
                    other => last = Some(other),
                }
            }
            if !progress {
                if let Some(e) = exhausted {
                    return Ok(Build::OracleInconclusive(e));
                }
                return Ok(Build::Problem(Problem::Unresolved {
                    atoms: remaining,
                    answer: last.unwrap(),
                }));
            }
        }
        // Expressions can bypass producers. Remove work no requested output uses.
        let providers: BTreeMap<_, _> = nodes
            .iter()
            .flat_map(|(id, n)| n.outputs().into_iter().map(move |k| (k, id.clone())))
            .collect();
        let mut retained = BTreeSet::new();
        let mut required_inputs = BTreeSet::new();
        let mut pending: Vec<_> = requested.keys().cloned().collect();
        while let Some(key) = pending.pop() {
            budget.tick(1)?;
            if inputs.contains(&key) {
                required_inputs.insert(key);
            } else if let Some(id) = providers.get(&key) {
                if retained.insert(id.clone()) {
                    pending.extend(nodes[id].inputs.iter().cloned());
                }
            }
        }
        nodes.retain(|k, _| retained.contains(k));
        budget.tick(nodes.len() + requested.len())?;
        let declaration = self.corpus.verification(self.verification).unwrap();
        Ok(Build::Ready(Plan {
            verification: self.keys.verification(self.verification)?.clone(),
            assumptions: declaration
                .assumptions
                .iter()
                .map(|a| self.keys.assumption(*a).cloned())
                .collect::<std::result::Result<_, _>>()?,
            inputs: required_inputs,
            outputs: requested,
            nodes,
        }))
    }
}
struct Work<'a> {
    limits: &'a Limits,
    start: Instant,
    work: usize,
}
impl Work<'_> {
    fn tick(&mut self, n: usize) -> Result<()> {
        self.limits.cancellation.check()?;
        self.work = self.work.saturating_add(n);
        if self.work > self.limits.max_work {
            return Err(CheckError::limit(
                "plan construction",
                "work",
                self.limits.max_work,
                Some(self.work),
            ));
        }
        if self.start.elapsed() >= self.limits.timeout {
            return Err(CheckError::deadline(
                "plan construction",
                self.limits.timeout,
            ));
        }
        Ok(())
    }
}
fn room(n: usize, max: usize, resource: &'static str) -> Result<()> {
    if n >= max {
        Err(CheckError::limit(
            "plan construction",
            resource,
            max,
            Some(n.saturating_add(1)),
        ))
    } else {
        Ok(())
    }
}
fn rule_expression(
    rules: &[&GroundRule],
    keys: &SemanticKeys,
    available: &BTreeSet<AtomKey>,
    budget: &mut Work<'_>,
) -> Result<Option<Expression>> {
    let mut bodies = Vec::new();
    for r in rules {
        let mut body = Vec::new();
        for l in &r.body {
            budget.tick(1)?;
            let k = AtomKey::from_atom(keys, &l.term.atom)?;
            if !available.contains(&k) {
                return Ok(None);
            }
            body.push((k, l.polarity == Polarity::Positive));
        }
        body.sort();
        body.dedup();
        bodies.push(body);
    }
    bodies.sort();
    bodies.dedup();
    let mut nodes = Vec::new();
    let mut alternatives = Vec::new();
    for body in bodies {
        let mut terms = Vec::new();
        for (k, positive) in body {
            nodes.push(Term::Read(k));
            if !positive {
                nodes.push(Term::Not(nodes.len() - 1));
            }
            terms.push(nodes.len() - 1);
        }
        nodes.push(Term::And(terms));
        alternatives.push(nodes.len() - 1);
    }
    nodes.push(Term::Or(alternatives));
    Ok(Some(Expression {
        root: nodes.len() - 1,
        nodes,
    }))
}
fn dependencies(expr: &Expression) -> BTreeSet<AtomKey> {
    expr.nodes
        .iter()
        .filter_map(|n| match n {
            Term::Read(k) | Term::If { atom: k, .. } => Some(k.clone()),
            _ => None,
        })
        .collect()
}
fn insert_compute(
    nodes: &mut BTreeMap<AtomKey, Node>,
    available: &mut BTreeSet<AtomKey>,
    key: &AtomKey,
    expr: Expression,
    sources: BTreeSet<RuleKey>,
    options: &Options,
    budget: &mut Work<'_>,
) -> Result<()> {
    budget.tick(expr.nodes.len() + 1)?;
    room(nodes.len(), options.max_nodes, "plan nodes")?;
    let inputs = dependencies(&expr);
    if !inputs.is_subset(available) {
        return Err(CheckError::Internal(
            "plan expression reads unavailable value",
        ));
    }
    nodes.insert(
        key.clone(),
        Node {
            id: key.clone(),
            inputs,
            sources,
            operation: Operation::Compute {
                output: key.clone(),
                expression: expr,
            },
        },
    );
    available.insert(key.clone());
    Ok(())
}
fn convert(expr: stable_query::Expression, keys: &SemanticKeys) -> Result<Expression> {
    use stable_query::ExpressionNode as N;
    Ok(Expression {
        root: expr.root,
        nodes: expr
            .nodes
            .into_iter()
            .map(|n| {
                Ok(match n {
                    N::Constant(v) => Term::Constant(v),
                    N::Atom(a) => Term::Read(AtomKey::from_atom(keys, &a)?),
                    N::Not(i) => Term::Not(i),
                    N::And(v) => Term::And(v),
                    N::Or(v) => Term::Or(v),
                    N::If {
                        atom,
                        when_true,
                        when_false,
                    } => Term::If {
                        atom: AtomKey::from_atom(keys, &atom)?,
                        when_true,
                        when_false,
                    },
                })
            })
            .collect::<Result<_>>()?,
    })
}
