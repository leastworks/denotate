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
        let mut rules = BTreeMap::new();
        let mut fixed = BTreeMap::new();
        let mut inputs = BTreeSet::new();
        for (key, atom) in &atoms {
            if input_atoms.contains(atom) {
                inputs.insert(key.clone());
            }
            if let Some(v) = self.engine.prepared_value(atom)? {
                fixed.insert(key.clone(), v);
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
            &mut self.engine,
            self.keys,
            &atoms,
            &rules,
            &fixed,
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
pub(super) struct Work<'a> {
    limits: &'a Limits,
    start: Instant,
    work: usize,
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
