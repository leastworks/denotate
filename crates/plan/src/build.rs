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
    pub max_split_depth: usize,
    pub max_splits: usize,
    pub max_split_candidates: usize,
    pub max_support_trials: usize,
    pub oracle: OracleLimits,
    pub meaning: CheckOptions,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            max_nodes: 100_000,
            max_oracle_calls: 256,
            max_split_depth: 16,
            max_splits: 128,
            max_split_candidates: 256,
            max_support_trials: 64,
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
        answer: Option<SynthesisAnswer>,
        path: BTreeMap<AtomKey, bool>,
        dependencies: Vec<(AtomKey, AtomKey, bool)>,
        world: Option<stable_query::Model>,
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

/// Owns one immutable program/verification and the latest output-scoped engine.
/// Equal output sets reuse its query cache; changed outputs prepare a fresh engine.
/// Program/domain/selection edits require a new Planner.
pub struct Planner<'a> {
    corpus: &'a Corpus,
    keys: &'a SemanticKeys,
    verification: VerificationId,
    limits: Limits,
    domains: Domains,
    queries: QueryLimits,
    roots: BTreeSet<AtomKey>,
    engine: Option<stable_query::Engine>,
    reported_scope: Option<stable_query::ScopeSummary>,
    task_configuration: Vec<Task>,
}
impl<'a> Planner<'a> {
    /// Expand a declared output relation over the resolved finite domains,
    /// including legal tuples that have no producer (and therefore are false).
    pub fn relation_outputs(
        &self,
        relation: denotate_ir::RelationId,
        priority: u32,
    ) -> Result<Vec<Output>> {
        relation_outputs(self.corpus, &self.domains, &self.limits, relation, priority)
    }

    pub fn prepare(
        corpus: &'a Corpus,
        domains: &Domains,
        keys: &'a SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        queries: QueryLimits,
    ) -> Result<Self> {
        limits.cancellation.check()?;
        if corpus.verification(verification).is_none() {
            return Err(CheckError::InvalidRequest("unknown plan verification"));
        }
        denotate_check::require_stable_verification(corpus, verification)?;
        // Outputs are supplied to build. Do not first encode a whole program
        // whose meaning and query cache would have the wrong scope.
        Ok(Self {
            corpus,
            keys,
            verification,
            limits: limits.clone(),
            domains: domains.clone(),
            queries,
            roots: BTreeSet::new(),
            engine: None,
            reported_scope: None,
            task_configuration: Vec::new(),
        })
    }
    /// Scope prepared for the latest build attempt, if any. The checker calls
    /// explicit output atom scopes "root-cones". Failures before preparation have
    /// no measured scope, even if a previous engine remains cached.
    pub fn scope(&self) -> Option<&stable_query::ScopeSummary> {
        self.reported_scope.as_ref()
    }
    pub fn build(&mut self, outputs: &[Output], options: &Options) -> Result<Build> {
        self.build_with_tasks(outputs, &[], options)
    }
    /// Task results are logical inputs, supplied only by their scheduled producer.
    /// This low-level API does not validate runtime callback contracts.
    pub fn build_with_tasks(
        &mut self,
        outputs: &[Output],
        tasks: &[Task],
        options: &Options,
    ) -> Result<Build> {
        self.reported_scope = None;
        match self.build_inner(outputs, tasks, options) {
            Err(e @ (CheckError::LimitExceeded { .. } | CheckError::Deadline { .. })) => {
                Ok(Build::Inconclusive(e))
            }
            other => other,
        }
    }
    fn build_inner(
        &mut self,
        outputs: &[Output],
        task_declarations: &[Task],
        options: &Options,
    ) -> Result<Build> {
        if outputs.is_empty() {
            return Err(CheckError::InvalidRequest("plan requires explicit outputs"));
        }
        if options.meaning.meaning != stable_query::MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "plan requires both existence and uniqueness in its output cone",
            ));
        }
        let limits = self.limits.clone();
        let mut budget = Work {
            limits: &limits,
            start: Instant::now(),
            work: 0,
        };
        let tasks =
            crate::task::Tasks::prepare(self.corpus, self.keys, task_declarations, &mut budget)?;
        let mut configuration = task_declarations.to_vec();
        configuration.sort_by(|a, b| a.key.cmp(&b.key));
        let mut requested = BTreeMap::new();
        let mut roots = BTreeMap::new();
        for output in outputs {
            budget.tick(1)?;
            let key = AtomKey::from_atom(self.keys, &output.atom)?;
            roots.insert(key.clone(), output.atom.clone());
            requested
                .entry(key)
                .and_modify(|p: &mut u32| *p = (*p).min(output.priority))
                .or_insert(output.priority);
        }
        let root_keys = roots.keys().cloned().collect::<BTreeSet<_>>();
        if self.engine.is_none()
            || self.roots != root_keys
            || self.task_configuration != configuration
        {
            self.engine = None; // Drop old clauses before a fallible scope switch.
            self.roots.clear();
            let preparation_start = Instant::now();
            let engine = stable_query::Engine::prepare_scoped(
                self.corpus,
                &self.domains,
                self.keys,
                self.verification,
                &self.limits,
                self.queries.clone(),
                if tasks.edges.is_empty() {
                    stable_query::PreparationScope::Roots(roots.into_values().collect())
                } else {
                    stable_query::PreparationScope::RootsWithDependencies {
                        roots: roots.into_values().collect(),
                        dependencies: tasks.edges.clone(),
                    }
                },
            )?;
            // Preparation retains its own checker phase deadlines, as when it
            // happened in prepare(). Do not also charge it to driver elapsed time.
            budget.start += preparation_start.elapsed();
            self.engine = Some(engine);
            self.roots = root_keys;
            self.task_configuration = configuration;
        }
        let engine = self.engine.as_mut().unwrap();
        for atom in tasks.atoms.values() {
            budget.tick(atom.arguments.len() + 1)?;
            engine.program().is_possible(atom)?; // Validate even unused descriptor atoms.
        }
        for output in outputs {
            engine.prepared_value(&output.atom)?; // Also validate before empty-context results.
        }
        self.reported_scope = Some(engine.scope().clone());
        budget.tick(1)?;
        if engine.program().input_universe_is_empty() {
            return Ok(Build::NoPermittedWorlds);
        }
        match engine.worlds(&Query::default())? {
            Answer::NoModel => return Ok(Build::NoPermittedWorlds),
            Answer::Inconclusive(e) => return Ok(Build::OracleInconclusive(e)),
            Answer::Model(_) => {}
        }
        budget.tick(1)?;
        let meaning = engine.meaning(&options.meaning)?;
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
        let graph = engine.program().clone();
        let mut producers = BTreeMap::<GroundAtom, Vec<&GroundRule>>::new();
        for rule in graph.rules() {
            budget.tick(rule.body.len() + 1)?;
            producers
                .entry(rule.head.atom.clone())
                .or_default()
                .push(rule);
        }
        let input_atoms: BTreeSet<_> = graph.input_atoms().cloned().collect();
        for k in tasks.by_result.keys() {
            budget.tick(1)?;
            if !input_atoms.contains(&tasks.atoms[k]) {
                return Err(CheckError::InvalidRequest(
                    "task result is outside the eligible input universe",
                ));
            }
        }
        let mut atoms = BTreeMap::new();
        let mut pending: Vec<_> = outputs.iter().map(|o| o.atom.clone()).collect();
        while let Some(atom) = pending.pop() {
            budget.tick(1)?;
            let key = AtomKey::from_atom(self.keys, &atom)?;
            if atoms.contains_key(&key) {
                continue;
            }
            if let Some(call) = tasks.by_result.get(&key) {
                pending.extend(
                    call.results
                        .iter()
                        .chain(call.arguments.iter())
                        .chain(call.when.iter())
                        .map(|k| tasks.atoms[k].clone()),
                );
            }
            if !input_atoms.contains(&atom) && engine.prepared_value(&atom)?.is_none() {
                for rule in producers.get(&atom).into_iter().flatten() {
                    budget.tick(rule.body.len())?;
                    pending.extend(rule.body.iter().map(|l| l.term.atom.clone()));
                }
            }
            atoms.insert(key, atom);
        }
        let mut rules = BTreeMap::new();
        let mut fixed = BTreeMap::new();
        let mut inputs = BTreeSet::new();
        for (key, atom) in &atoms {
            if input_atoms.contains(atom) && !tasks.by_result.contains_key(key) {
                inputs.insert(key.clone());
            }
            if !tasks.by_result.contains_key(key) {
                if let Some(v) = engine.prepared_value(atom)? {
                    fixed.insert(key.clone(), v);
                }
            }
            let mut rs = Vec::new();
            for r in producers.get(atom).into_iter().flatten() {
                budget.tick(r.body.len() + 1)?;
                let mut body = r
                    .body
                    .iter()
                    .map(|l| {
                        Ok((
                            AtomKey::from_atom(self.keys, &l.term.atom)?,
                            l.polarity == Polarity::Positive,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                body.sort();
                body.dedup();
                rs.push(Rule {
                    head: key.clone(),
                    body,
                    source: self.keys.rule(r.source)?.clone(),
                });
            }
            rs.sort_by(|a, b| (&a.source, &a.body).cmp(&(&b.source, &b.body)));
            rules.insert(key.clone(), rs);
        }
        let mut search = crate::search::Search::new(
            engine,
            self.keys,
            &atoms,
            &rules,
            &fixed,
            &tasks,
            options,
            &mut budget,
        );
        let region = match search.region(
            &requested.keys().cloned().collect(),
            &inputs,
            &BTreeMap::new(),
            0,
        ) {
            Ok(r) => r,
            Err(crate::search::Failure::Check(e)) => return Err(e),
            Err(crate::search::Failure::Oracle(e)) => return Ok(Build::OracleInconclusive(e)),
            Err(crate::search::Failure::Problem(p)) => return Ok(Build::Problem(p)),
        };
        let nodes = region.nodes;
        let required_inputs = crate::search::external(&nodes, &requested.keys().cloned().collect());
        if !required_inputs.is_subset(&inputs) {
            return Err(CheckError::Internal("plan has unscheduled inputs"));
        }
        budget.tick(nodes.len() + requested.len())?;
        let declaration = self.corpus.verification(self.verification).unwrap();
        Ok(Build::Ready(Plan {
            scope: engine.scope().clone(),
            verification: self.keys.verification(self.verification)?.clone(),
            assumptions: declaration
                .assumptions
                .iter()
                .map(|a| self.keys.assumption(*a).cloned())
                .collect::<std::result::Result<_, _>>()?,
            inputs: required_inputs,
            produced_inputs: atoms
                .keys()
                .filter(|k| tasks.by_result.contains_key(*k))
                .cloned()
                .collect(),
            outputs: requested,
            nodes,
        }))
    }
}
pub(super) struct Work<'a> {
    pub(super) limits: &'a Limits,
    pub(super) start: Instant,
    pub(super) work: usize,
}
impl Work<'_> {
    pub(super) fn tick(&mut self, n: usize) -> Result<()> {
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
pub(super) fn room(n: usize, max: usize, resource: &'static str) -> Result<()> {
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
pub(super) fn dependencies(expr: &Expression) -> BTreeSet<AtomKey> {
    expr.nodes
        .iter()
        .filter_map(|n| match n {
            Term::Read(k) | Term::If { atom: k, .. } => Some(k.clone()),
            _ => None,
        })
        .collect()
}
pub(super) fn convert(expr: stable_query::Expression, keys: &SemanticKeys) -> Result<Expression> {
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

/// Expand output tuples with the same resolved-domain and resource rules for both planners.
pub fn relation_outputs(
    corpus: &Corpus,
    domains: &Domains,
    limits: &Limits,
    relation: denotate_ir::RelationId,
    priority: u32,
) -> Result<Vec<Output>> {
    let r = corpus
        .relation(relation)
        .ok_or(CheckError::InvalidRequest("unknown output relation"))?;
    let mut budget = Work {
        limits: limits,
        start: Instant::now(),
        work: 0,
    };
    let mut tuples = vec![vec![]];
    for parameter in &r.parameters {
        let domain = domains
            .get(&parameter.sort)
            .ok_or(CheckError::InvalidRequest("missing output domain"))?;
        let mut next = Vec::new();
        for tuple in &tuples {
            for value in domain {
                budget.tick(tuple.len() + 1)?;
                room(next.len(), limits.max_atoms, "output atoms")?;
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
