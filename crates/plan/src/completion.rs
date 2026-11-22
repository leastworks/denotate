//! Completion plans keep runtime classification separate from H-conditional values.
//! This increment emits two straight-line regions separated by a rejection barrier.
use crate::build::{Work, dependencies, room};
use crate::{AtomKey, Expression, Node, Operation, Options, Output, Rule, Term};
use denotate_check::{CheckError, Domains, GroundAtom, Limits, Polarity, completion_query as q};
use denotate_ir::{Corpus, SemanticKeys, Semantics, VerificationId};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};
mod export;
mod run;
pub use run::{Execution, Outcome};
type Result<T> = std::result::Result<T, CheckError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminal {
    Accept,
    Reject,
    /// The actual equation value, computed without H-based substitutions.
    Test(AtomKey),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    verification: denotate_ir::VerificationKey,
    assumptions: BTreeSet<denotate_ir::AssumptionKey>,
    hypothesis: Option<AtomKey>,
    decisions: Option<BTreeSet<denotate_ir::RelationKey>>,
    classification_scope: usize,
    output_scope: usize,
    conditional_constants: BTreeMap<AtomKey, bool>,
    inputs: BTreeSet<AtomKey>,
    outputs: BTreeMap<AtomKey, u32>,
    classification: BTreeMap<AtomKey, Node>,
    accepted: BTreeMap<AtomKey, Node>,
    terminal: Terminal,
}
impl Plan {
    pub fn inputs(&self) -> &BTreeSet<AtomKey> {
        &self.inputs
    }
    pub fn outputs(&self) -> &BTreeMap<AtomKey, u32> {
        &self.outputs
    }
    pub fn classification(&self) -> &BTreeMap<AtomKey, Node> {
        &self.classification
    }
    pub fn accepted(&self) -> &BTreeMap<AtomKey, Node> {
        &self.accepted
    }
    pub fn terminal(&self) -> &Terminal {
        &self.terminal
    }
}
#[derive(Debug)]
pub enum Problem {
    InputDomains(Vec<q::InputDomainIssue>),
    Context(q::PlanningContext),
    Outputs(q::PlanningOutputs),
    Unresolved {
        phase: &'static str,
        atoms: Vec<AtomKey>,
        dependencies: Vec<(AtomKey, AtomKey, bool)>,
    },
}
#[derive(Debug)]
pub enum Build {
    Ready(Plan),
    NoPermittedWorlds,
    Problem(Box<Problem>),
    Inconclusive(CheckError),
    OracleInconclusive(denotate_check::Inconclusive),
}
pub struct Planner<'a> {
    corpus: &'a Corpus,
    domains: Domains,
    keys: &'a SemanticKeys,
    verification: VerificationId,
    limits: Limits,
    queries: q::QueryLimits,
}
impl<'a> Planner<'a> {
    pub fn prepare(
        corpus: &'a Corpus,
        domains: &Domains,
        keys: &'a SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        queries: q::QueryLimits,
    ) -> Result<Self> {
        let v = corpus
            .verification(verification)
            .ok_or(CheckError::InvalidRequest("unknown plan verification"))?;
        if v.options.semantics != Semantics::Completion {
            return Err(CheckError::InvalidRequest(
                "completion planner requires completion semantics",
            ));
        }
        Ok(Self {
            corpus,
            domains: domains.clone(),
            keys,
            verification,
            limits: limits.clone(),
            queries,
        })
    }
    pub fn relation_outputs(
        &self,
        relation: denotate_ir::RelationId,
        priority: u32,
    ) -> Result<Vec<Output>> {
        crate::relation_outputs(self.corpus, &self.domains, &self.limits, relation, priority)
    }
    pub fn build(&self, outputs: &[Output], options: &Options) -> Result<Build> {
        match self.build_inner(outputs, options) {
            Err(e @ (CheckError::LimitExceeded { .. } | CheckError::Deadline { .. })) => {
                Ok(Build::Inconclusive(e))
            }
            other => other,
        }
    }
    fn build_inner(&self, outputs: &[Output], options: &Options) -> Result<Build> {
        if outputs.is_empty() {
            return Err(CheckError::InvalidRequest("plan requires explicit outputs"));
        }
        if options.meaning.meaning != denotate_check::stable_query::MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "completion planning requires full meaning checks",
            ));
        }
        let engine = match q::Engine::prepare_for_planning(
            self.corpus,
            &self.domains,
            self.keys,
            self.verification,
            &self.limits,
            self.queries.clone(),
            &outputs.iter().map(|o| o.atom.clone()).collect::<Vec<_>>(),
        )? {
            q::Preparation::Ready(e) => e,
            q::Preparation::InputDomains(issues) => {
                return Ok(Build::Problem(Box::new(Problem::InputDomains(issues))));
            }
            q::Preparation::Inconclusive(c) => return Ok(Build::OracleInconclusive(c)),
        };
        let mut work = Work {
            limits: &self.limits,
            start: Instant::now(),
            work: 0,
        };
        let mut calls = 0;
        let mut call = || -> Result<()> {
            room(calls, options.max_oracle_calls, "oracle calls")?;
            calls += 1;
            Ok(())
        };
        let opts = q::CheckOptions {
            max_worlds: options.meaning.max_worlds,
            ..Default::default()
        };
        let path = q::RuntimePath::new();
        call()?;
        let context = engine.planning_context(&path, &opts)?;
        work.tick(1)?;
        match context.outcome {
            q::PathOutcome::NoPermittedInputs => return Ok(Build::NoPermittedWorlds),
            q::PathOutcome::Invalid | q::PathOutcome::Inconclusive => {
                return Ok(Build::Problem(Box::new(Problem::Context(context))));
            }
            _ => (),
        }
        let g = engine.original_program();
        let v = self.corpus.verification(self.verification).unwrap();
        let hypothesis = v.options.hypothesis.map(|r| GroundAtom::new(r, []));
        let mut requested = BTreeMap::<AtomKey, u32>::new();
        let mut roots = BTreeSet::new();
        for o in outputs {
            work.tick(1)?;
            g.is_possible(&o.atom)?;
            roots.insert(o.atom.clone());
            requested
                .entry(AtomKey::from_atom(self.keys, &o.atom)?)
                .and_modify(|p| *p = (*p).min(o.priority))
                .or_insert(o.priority);
        }
        let output_scope = if context.outcome != q::PathOutcome::Reject {
            call()?;
            let answer = engine.planning_outputs(&path, &roots, &opts)?;
            work.tick(1)?;
            if !answer.certified() {
                return Ok(Build::Problem(Box::new(Problem::Outputs(answer))));
            }
            answer.members
        } else {
            BTreeSet::new()
        };
        let classification_scope = match &hypothesis {
            Some(h) => g.dependency_cone([h.clone()], &self.limits)?.facts,
            None => BTreeSet::new(),
        };
        let mut atoms = BTreeMap::new();
        for a in output_scope
            .iter()
            .chain(classification_scope.iter())
            .chain(roots.iter())
            .chain(hypothesis.iter())
        {
            work.tick(1)?;
            atoms.insert(AtomKey::from_atom(self.keys, a)?, a.clone());
        }
        let inputs = g
            .input_atoms()
            .map(|a| Ok(AtomKey::from_atom(self.keys, a)?))
            .collect::<Result<BTreeSet<_>>>()?;
        let mut rules = BTreeMap::<AtomKey, Vec<Rule>>::new();
        for r in g.rules() {
            work.tick(1)?;
            if !output_scope.contains(&r.head.atom) && !classification_scope.contains(&r.head.atom)
            {
                continue;
            }
            work.tick(r.body.len())?;
            let head = AtomKey::from_atom(self.keys, &r.head.atom)?;
            rules.entry(head.clone()).or_default().push(Rule {
                head,
                source: self.keys.rule(r.source)?.clone(),
                body: r
                    .body
                    .iter()
                    .map(|l| {
                        Ok((
                            AtomKey::from_atom(self.keys, &l.term.atom)?,
                            l.polarity == Polarity::Positive,
                        ))
                    })
                    .collect::<Result<_>>()?,
            });
        }
        let mut plan = Plan {
            verification: self.keys.verification(self.verification)?.clone(),
            assumptions: v
                .assumptions
                .iter()
                .map(|a| Ok(self.keys.assumption(*a)?.clone()))
                .collect::<Result<_>>()?,
            hypothesis: hypothesis
                .as_ref()
                .map(|a| AtomKey::from_atom(self.keys, a))
                .transpose()?,
            decisions: v
                .options
                .decisions
                .as_ref()
                .map(|rs| {
                    rs.iter()
                        .map(|r| Ok(self.keys.relation(*r)?.clone()))
                        .collect::<Result<_>>()
                })
                .transpose()?,
            classification_scope: classification_scope.len(),
            output_scope: output_scope.len(),
            conditional_constants: BTreeMap::new(),
            inputs: inputs.clone(),
            outputs: requested,
            classification: BTreeMap::new(),
            accepted: BTreeMap::new(),
            terminal: Terminal::Accept,
        };
        if context.outcome == q::PathOutcome::Reject {
            plan.terminal = Terminal::Reject;
            return Ok(Build::Ready(plan));
        }
        let mut available = inputs;
        let mut nodes = 0;
        let mut conditional_constants = BTreeMap::new();
        let mut construct =
            |targets: &BTreeSet<AtomKey>,
             accepted: bool,
             available: &mut BTreeSet<AtomKey>|
             -> Result<std::result::Result<BTreeMap<AtomKey, Node>, Problem>> {
                let mut emitted = BTreeMap::new();
                // Only ancestors still needed by an unavailable target are candidates.
                loop {
                    let mut pending: Vec<_> = targets
                        .iter()
                        .filter(|k| !available.contains(*k))
                        .cloned()
                        .collect();
                    if pending.is_empty() {
                        return Ok(Ok(emitted));
                    }
                    let mut needed = BTreeSet::new();
                    while let Some(k) = pending.pop() {
                        work.tick(1)?;
                        if available.contains(&k) || !needed.insert(k.clone()) {
                            continue;
                        }
                        for r in rules.get(&k).into_iter().flatten() {
                            work.tick(r.body.len() + 1)?;
                            pending.extend(r.body.iter().map(|(a, _)| a.clone()));
                        }
                    }
                    let mut progress = false;
                    for k in &needed {
                        let rs = rules.get(k).map(Vec::as_slice).unwrap_or(&[]);
                        if let Some(expression) =
                            crate::search::expression(rs, available, &mut work)?
                        {
                            room(nodes, options.max_nodes, "nodes")?;
                            nodes += 1;
                            let node = Node {
                                id: k.clone(),
                                inputs: dependencies(&expression),
                                sources: rs.iter().map(|r| r.source.clone()).collect(),
                                operation: Operation::Compute {
                                    output: k.clone(),
                                    expression,
                                },
                            };
                            emitted.insert(k.clone(), node);
                            available.insert(k.clone());
                            progress = true;
                        }
                    }
                    if progress {
                        continue;
                    }
                    if accepted {
                        for k in targets
                            .iter()
                            .chain(needed.iter())
                            .filter(|k| !available.contains(*k))
                            .cloned()
                            .collect::<BTreeSet<_>>()
                        {
                            call()?;
                            let answer = engine.planning_constant(
                                &path,
                                &atoms[&k],
                                q::ConstantScope::Output,
                                &opts,
                            )?;
                            work.tick(1)?;
                            if let q::PlanningConstant::Proven { value, .. } = answer {
                                room(nodes, options.max_nodes, "nodes")?;
                                nodes += 1;
                                emitted.insert(
                                    k.clone(),
                                    Node {
                                        id: k.clone(),
                                        inputs: BTreeSet::new(),
                                        sources: rules
                                            .get(&k)
                                            .into_iter()
                                            .flatten()
                                            .map(|r| r.source.clone())
                                            .collect(),
                                        operation: Operation::Compute {
                                            output: k.clone(),
                                            expression: Expression {
                                                nodes: vec![Term::Constant(value)],
                                                root: 0,
                                            },
                                        },
                                    },
                                );
                                conditional_constants.insert(k.clone(), value);
                                available.insert(k);
                                progress = true;
                                break;
                            }
                            match answer {
                                q::PlanningConstant::Inconclusive(c) => return Err(c.into()),
                                q::PlanningConstant::ContextNotReady(c) => {
                                    return Ok(Err(Problem::Context(*c)));
                                }
                                _ => (),
                            }
                        }
                    }
                    if progress {
                        continue;
                    }
                    let dependencies = needed
                        .iter()
                        .flat_map(|k| {
                            rules.get(k).into_iter().flatten().flat_map(move |r| {
                                r.body.iter().map(move |(a, p)| (k.clone(), a.clone(), *p))
                            })
                        })
                        .collect();
                    return Ok(Err(Problem::Unresolved {
                        phase: if accepted {
                            "processing"
                        } else {
                            "classification"
                        },
                        atoms: needed.into_iter().collect(),
                        dependencies,
                    }));
                }
            };
        if context.outcome == q::PathOutcome::Mixed {
            let h = plan.hypothesis.clone().expect("mixed context requires H");
            plan.classification =
                match construct(&BTreeSet::from([h.clone()]), false, &mut available)? {
                    Ok(n) => n,
                    Err(p) => return Ok(Build::Problem(Box::new(p))),
                };
            plan.terminal = Terminal::Test(h);
        }
        plan.accepted = match construct(
            &plan.outputs.keys().cloned().collect(),
            true,
            &mut available,
        )? {
            Ok(n) => n,
            Err(p) => return Ok(Build::Problem(Box::new(p))),
        };
        plan.conditional_constants = conditional_constants;
        work.tick(1)?;
        Ok(Build::Ready(plan))
    }
}
