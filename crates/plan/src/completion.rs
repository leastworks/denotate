//! Completion plans keep runtime classification separate from H-conditional values.
//! A path driver walks forward from entry: it sequences what each runtime path
//! determines, substitutes constants the checker proves on the path, splits on an
//! input when stuck, and ends every path in an explicit terminal. Constants proved
//! under H whose definitions are not implied keep a runtime check, so no-meaning
//! and genuinely rejected messages both reject (024.38).
use crate::build::{Work, dependencies, room};
use crate::{AtomKey, Expression, Node, Operation, Options, Output, Rule, Term};
use denotate_check::{CheckError, Domains, GroundAtom, Limits, Polarity, completion_query as q};
use denotate_ir::{Corpus, SemanticKeys, Semantics, VerificationId};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};
mod driver;
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
/// A constant substituted on this path whose definition was not shown implied:
/// the message is rejected unless the definition, evaluated on the computed
/// values, gives the constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    pub atom: AtomKey,
    pub value: bool,
    pub definition: Expression,
}
/// Classification part of the plan: a region, then a split or a terminal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Region {
    pub nodes: BTreeMap<AtomKey, Node>,
    pub next: Next,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Next {
    /// On the actual value of an input.
    Split {
        on: AtomKey,
        then: Box<Region>,
        otherwise: Box<Region>,
    },
    /// Checks, then the terminal; an accepting terminal continues into this
    /// leaf's own accepted region, with the leaf's path facts and values.
    Leaf {
        checks: Vec<Check>,
        terminal: Terminal,
        accepted: Option<Box<Accepted>>,
    },
}
/// Processing after acceptance, per accepted leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Accepted {
    pub nodes: BTreeMap<AtomKey, Node>,
    pub next: AcceptedNext,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AcceptedNext {
    Return,
    /// No accepted message reaches this arm.
    Unreachable,
    Split {
        on: AtomKey,
        then: Box<Accepted>,
        otherwise: Box<Accepted>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    verification: denotate_ir::VerificationKey,
    assumptions: BTreeSet<denotate_ir::AssumptionKey>,
    hypothesis: Option<AtomKey>,
    decisions: Option<BTreeSet<denotate_ir::RelationKey>>,
    classification_scope: usize,
    output_scope: usize,
    inputs: BTreeSet<AtomKey>,
    outputs: BTreeMap<AtomKey, u32>,
    root: Region,
}
impl Plan {
    pub fn inputs(&self) -> &BTreeSet<AtomKey> {
        &self.inputs
    }
    pub fn outputs(&self) -> &BTreeMap<AtomKey, u32> {
        &self.outputs
    }
    pub fn root(&self) -> &Region {
        &self.root
    }
    /// The terminal when the plan has no split (a single path).
    pub fn terminal(&self) -> Option<&Terminal> {
        match &self.root.next {
            Next::Leaf { terminal, .. } => Some(terminal),
            Next::Split { .. } => None,
        }
    }
    /// Number of splits, in classification and in accepted regions.
    pub fn splits(&self) -> usize {
        fn region(r: &Region) -> usize {
            match &r.next {
                Next::Split {
                    then, otherwise, ..
                } => 1 + region(then) + region(otherwise),
                Next::Leaf { accepted, .. } => accepted.as_deref().map_or(0, accepted_splits),
            }
        }
        fn accepted_splits(a: &Accepted) -> usize {
            match &a.next {
                AcceptedNext::Split {
                    then, otherwise, ..
                } => 1 + accepted_splits(then) + accepted_splits(otherwise),
                _ => 0,
            }
        }
        region(&self.root)
    }
    /// Every computation node of the plan, for source lookups.
    pub fn nodes(&self) -> Vec<&Node> {
        fn region<'a>(r: &'a Region, out: &mut Vec<&'a Node>) {
            out.extend(r.nodes.values());
            match &r.next {
                Next::Split {
                    then, otherwise, ..
                } => {
                    region(then, out);
                    region(otherwise, out);
                }
                Next::Leaf { accepted, .. } => {
                    if let Some(a) = accepted {
                        accepted_nodes(a, out);
                    }
                }
            }
        }
        fn accepted_nodes<'a>(a: &'a Accepted, out: &mut Vec<&'a Node>) {
            out.extend(a.nodes.values());
            if let AcceptedNext::Split {
                then, otherwise, ..
            } = &a.next
            {
                accepted_nodes(then, out);
                accepted_nodes(otherwise, out);
            }
        }
        let mut out = vec![];
        region(&self.root, &mut out);
        out
    }
}
/// A runtime path: input pins along the splits taken.
pub type PathFacts = Vec<(AtomKey, bool)>;
#[derive(Debug)]
pub enum Problem {
    InputDomains(Vec<q::InputDomainIssue>),
    /// The selected input contract is invalid or could not be certified.
    Context(q::PlanningContext),
    /// Targets that neither sequence, settle by a constant nor admit a cutting
    /// input split on this path, or an unsequenced remainder with an odd loop.
    Unresolved {
        phase: &'static str,
        path: PathFacts,
        atoms: Vec<AtomKey>,
        dependencies: Vec<(AtomKey, AtomKey, bool)>,
    },
    /// An accepted message on this path has no processing interpretation.
    MeaningFailure {
        path: PathFacts,
    },
    /// The checker's path question was cut off.
    PathInconclusive {
        path: PathFacts,
        cause: denotate_check::Inconclusive,
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
        let opts = q::CheckOptions {
            max_worlds: options.meaning.max_worlds,
            ..Default::default()
        };
        // Only the certified input contract is a prerequisite; classification
        // and output meaning are established path by path.
        let audits = engine.assumption_analysis(&opts)?;
        if audits.iter().any(|a| !a.certified()) {
            let invalid = audits.iter().any(|a| a.failed());
            return Ok(Build::Problem(Box::new(Problem::Context(
                q::PlanningContext {
                    outcome: if invalid {
                        q::PathOutcome::Invalid
                    } else {
                        q::PathOutcome::Inconclusive
                    },
                    assumptions: audits,
                    classification: None,
                    inconclusive: None,
                },
            ))));
        }
        match engine.worlds(&q::WorldQuery::default())? {
            q::WorldAnswer::NoWorld => return Ok(Build::NoPermittedWorlds),
            q::WorldAnswer::Inconclusive(c) => return Ok(Build::OracleInconclusive(c)),
            q::WorldAnswer::World(_) => {}
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
        let classification_scope = match &hypothesis {
            Some(h) => g.dependency_cone([h.clone()], &self.limits)?.facts,
            None => BTreeSet::new(),
        };
        let mut output_scope = g
            .dependency_cone(roots.iter().cloned(), &self.limits)?
            .facts;
        output_scope.extend(classification_scope.iter().cloned());
        let mut atoms = BTreeMap::new();
        for a in output_scope
            .iter()
            .chain(roots.iter())
            .chain(hypothesis.iter())
        {
            work.tick(1)?;
            atoms.insert(AtomKey::from_atom(self.keys, a)?, a.clone());
        }
        let mut inputs = BTreeSet::new();
        for a in g.input_atoms() {
            work.tick(1)?;
            let k = AtomKey::from_atom(self.keys, a)?;
            atoms.insert(k.clone(), a.clone());
            inputs.insert(k);
        }
        let mut rules = BTreeMap::<AtomKey, Vec<Rule>>::new();
        for r in g.rules() {
            work.tick(1)?;
            if !output_scope.contains(&r.head.atom) {
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
        let key = |a: &GroundAtom| AtomKey::from_atom(self.keys, a);
        let class_keys = classification_scope
            .iter()
            .map(key)
            .collect::<std::result::Result<BTreeSet<_>, _>>()?;
        let hypothesis_key = hypothesis.as_ref().map(key).transpose()?;
        // Targets: H and the declared decisions in C(H) (every head of C(H) when
        // decisions are undeclared). Unused helpers stay free.
        let mut class_targets: BTreeSet<AtomKey> = hypothesis_key.iter().cloned().collect();
        for a in &classification_scope {
            work.tick(1)?;
            let k = key(a)?;
            let decision = match &v.options.decisions {
                None => rules.contains_key(&k),
                Some(ds) => ds.contains(&a.relation),
            };
            if decision {
                class_targets.insert(k);
            }
        }
        let keys_of = atoms.iter().map(|(k, a)| (a.clone(), k.clone())).collect();
        let mut driver = driver::Driver {
            engine: &engine,
            keys_of,
            atoms,
            rules,
            inputs: inputs.clone(),
            hypothesis: hypothesis_key.clone(),
            class_targets,
            class_scope: class_keys,
            output_scope: output_scope
                .iter()
                .map(key)
                .collect::<std::result::Result<_, _>>()?,
            outputs: requested.keys().cloned().collect(),
            output_atoms: roots,
            options,
            work,
            nodes: 0,
            calls: 0,
            splits: 0,
        };
        let root = match driver.classify(driver::State::entry(&inputs))? {
            Ok(r) => r,
            Err(p) => return Ok(Build::Problem(Box::new(p))),
        };
        driver.work.tick(1)?;
        Ok(Build::Ready(Plan {
            verification: self.keys.verification(self.verification)?.clone(),
            assumptions: v
                .assumptions
                .iter()
                .map(|a| Ok(self.keys.assumption(*a)?.clone()))
                .collect::<Result<_>>()?,
            hypothesis: hypothesis_key,
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
            inputs,
            outputs: requested,
            root,
        }))
    }
}
fn constant_node(k: &AtomKey, value: bool, rules: &[Rule]) -> Node {
    Node {
        id: k.clone(),
        inputs: BTreeSet::new(),
        sources: rules.iter().map(|r| r.source.clone()).collect(),
        operation: Operation::Compute {
            output: k.clone(),
            expression: Expression {
                nodes: vec![Term::Constant(value)],
                root: 0,
            },
        },
    }
}
fn compute_node(k: &AtomKey, expression: Expression, rules: &[Rule]) -> Node {
    Node {
        id: k.clone(),
        inputs: dependencies(&expression),
        sources: rules.iter().map(|r| r.source.clone()).collect(),
        operation: Operation::Compute {
            output: k.clone(),
            expression,
        },
    }
}
