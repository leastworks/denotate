//! Diagnostic necessary condition for a guarded-settlement certificate. Unlike
//! the stable-model probe, this deliberately retains positive self-support in
//! the unresolved cone. Settled conditions are exact shared functions of inputs.
use super::*;
use crate::guarded_bounds::BorrowedCone;
use biodivine_lib_bdd::{BddPointer, BddValuation};
use denotate_ir::{OccurrenceId, RuleId};

#[derive(Debug, Clone)]
pub struct CandidateProbeLimits {
    /// Aggregate active diagnostic time across one admission invocation.
    pub timeout: Duration,
    pub max_candidates: usize,
    /// Aggregate encoding and validation work, independent of checker work.
    pub max_work: usize,
}
impl Default for CandidateProbeLimits {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(10),
            max_candidates: 64,
            max_work: 10_000_000,
        }
    }
}
#[derive(Debug, Clone, Default)]
pub struct CandidateProbeCounts {
    pub candidates: usize,
    pub ruled_out: usize,
    pub not_ruled_out: usize,
    pub unknown: usize,
    /// Includes cap/allowance exhaustion and candidates ordinary admission did
    /// not reach. These counts cover enumerated candidates across snapshots,
    /// not hypothetical candidates after admission stops.
    pub unexamined: usize,
    pub elapsed: Duration,
}
#[derive(Debug, Clone)]
pub struct CandidateProbePair {
    pub world: BTreeSet<GroundAtom>,
    pub models: [BTreeSet<GroundAtom>; 2],
    pub differing: BTreeSet<GroundAtom>,
    pub reading_fires: [bool; 2],
}
#[derive(Debug, Clone)]
pub struct CandidateProbeReport {
    pub snapshot: u64,
    pub rule: GroundRuleId,
    pub source: RuleId,
    pub occurrence: OccurrenceId,
    pub premise: GroundAtom,
    pub answer: SatProbeAnswer,
    pub reason: Option<String>,
    pub exhaustion: Option<Inconclusive>,
    pub pair: Option<CandidateProbePair>,
    pub cone_atoms: usize,
    pub cone_rules: usize,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    pub elapsed: Duration,
}
impl CandidateProbeReport {
    pub fn state(&self) -> &'static str {
        match self.answer {
            SatProbeAnswer::Sat => "ruled-out",
            SatProbeAnswer::Unsat => "not-ruled-out",
            SatProbeAnswer::Unknown => "unknown",
        }
    }
}
pub(crate) struct Diagnosis {
    config: CandidateProbeLimits,
    limits: Limits,
    used_work: usize,
    seen: BTreeSet<(u64, GroundRuleId, OccurrenceId)>,
    pub counts: CandidateProbeCounts,
}
impl Diagnosis {
    pub fn new(config: CandidateProbeLimits, mut limits: Limits) -> Self {
        limits.progress = Default::default();
        limits.profile = Default::default();
        Self {
            config,
            limits,
            used_work: 0,
            seen: BTreeSet::new(),
            counts: Default::default(),
        }
    }
    pub fn register(&mut self, count: usize) {
        self.counts.candidates += count;
        self.counts.unexamined += count;
    }
    pub fn probe(
        &mut self,
        cone: &BorrowedCone<'_>,
        ctx: &ConditionContext,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
    ) -> Result<Option<CandidateProbeReport>> {
        self.limits.cancellation.check()?;
        let key = (cone.snapshot, candidate.rule.id, literal.term.occurrence);
        if self.seen.contains(&key)
            || self.seen.len() >= self.config.max_candidates
            || self.counts.elapsed >= self.config.timeout
            || self.used_work >= self.config.max_work
        {
            return Ok(None);
        }
        self.seen.insert(key);
        self.limits.timeout = self.config.timeout.saturating_sub(self.counts.elapsed);
        self.limits.max_work = self.config.max_work.saturating_sub(self.used_work);
        let mut budget = Budget::new(&self.limits);
        let report = probe(cone, ctx, candidate, literal, &mut budget)?;
        self.used_work += budget.used();
        if report.exhaustion.is_some_and(|e| e.resource == "work") {
            self.used_work = self.config.max_work;
        }
        self.counts.elapsed += report.elapsed;
        self.counts.unexamined -= 1;
        match report.answer {
            SatProbeAnswer::Sat => self.counts.ruled_out += 1,
            SatProbeAnswer::Unsat => self.counts.not_ruled_out += 1,
            SatProbeAnswer::Unknown => self.counts.unknown += 1,
        }
        Ok(Some(report))
    }
}

// Shared input variables and exact settled BDDs; no BDD operations are performed.
struct Functions {
    inputs: BTreeMap<usize, Lit>,
    truth: Lit,
}
impl Functions {
    fn encode(&mut self, condition: &Condition, cnf: &mut Cnf, b: &mut Budget<'_>) -> Result<Lit> {
        let bdd = condition.diagnostic_bdd();
        b.charge(bdd.size(), "candidate probe BDD encoding")?;
        // BDD nodes are stored after their children. Terminal 0 may be the only
        // node in a false BDD; both terminal literals are always available.
        let mut nodes = vec![!self.truth, self.truth];
        for index in 2..bdd.size() {
            let ptr = BddPointer::from_index(index);
            let var = bdd.var_of(ptr).to_index();
            let input = if let Some(v) = self.inputs.get(&var) {
                *v
            } else {
                let v = cnf.var(b)?;
                self.inputs.insert(var, v);
                v
            };
            let lo = nodes[bdd.low_link_of(ptr).to_index()];
            let hi = nodes[bdd.high_link_of(ptr).to_index()];
            let v = cnf.var(b)?;
            cnf.clause(vec![!input, !v, hi], b)?;
            cnf.clause(vec![!input, v, !hi], b)?;
            cnf.clause(vec![input, !v, lo], b)?;
            cnf.clause(vec![input, v, !lo], b)?;
            nodes.push(v);
        }
        Ok(nodes[bdd.root_pointer().to_index()])
    }
}
struct EncodedProducer<'a> {
    head: usize,
    condition: &'a Condition,
    body: Vec<(usize, bool)>,
    reading: bool,
}
fn probe(
    cone: &BorrowedCone<'_>,
    ctx: &ConditionContext,
    candidate: &ProducerSummary,
    literal: &GroundLiteral,
    b: &mut Budget<'_>,
) -> Result<CandidateProbeReport> {
    let start = Instant::now();
    let mut report = CandidateProbeReport {
        snapshot: cone.snapshot,
        rule: candidate.rule.id,
        source: candidate.rule.source,
        occurrence: literal.term.occurrence,
        premise: literal.term.atom.clone(),
        answer: SatProbeAnswer::Unknown,
        reason: None,
        exhaustion: None,
        pair: None,
        cone_atoms: cone.atoms.len(),
        cone_rules: cone.producers.len(),
        variables: 0,
        clauses: 0,
        literals: 0,
        elapsed: Duration::ZERO,
    };
    let mut cnf = Cnf {
        solver: Solver::new(
            Default::default(),
            Stop {
                cancellation: b.limits.cancellation.clone(),
                start,
                timeout: b.limits.timeout,
                #[cfg(test)]
                hook: None,
            },
        ),
        clauses: 0,
        literals: 0,
    };
    let result = (|| {
        b.charge(cone.atoms.len(), "candidate probe atoms")?;
        let ids = cone
            .atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a, i))
            .collect::<BTreeMap<_, _>>();
        let target = ids[&literal.term.atom];
        let truth = cnf.var(b)?;
        cnf.clause(vec![truth], b)?;
        let mut functions = Functions {
            inputs: BTreeMap::new(),
            truth,
        };
        let domain = functions.encode(&cone.domain, &mut cnf, b)?;
        cnf.clause(vec![domain], b)?;
        let mut variables = [Vec::new(), Vec::new()];
        for copy in &mut variables {
            for _ in &cone.atoms {
                copy.push(cnf.var(b)?);
            }
        }
        let mut producers = Vec::new();
        let mut by_head = vec![Vec::new(); cone.atoms.len()];
        for p in cone.producers.iter().filter(|p| p.live) {
            b.tick("candidate probe producer")?;
            let reading = p.rule.id == candidate.rule.id;
            let mut body = Vec::new();
            if !reading {
                for l in &p.rule.body {
                    b.tick("candidate probe premise")?;
                    if p.settled
                        .iter()
                        .any(|s| s.literal.term.occurrence == l.term.occurrence)
                    {
                        continue;
                    }
                    let Some(id) = ids.get(&l.term.atom) else {
                        return Err(CheckError::InvalidRequest(
                            "candidate probe has an unresolved provider outside its component",
                        ));
                    };
                    body.push((*id, l.polarity == Polarity::Positive));
                }
            }
            let head = ids[&p.rule.head.atom];
            by_head[head].push(producers.len());
            producers.push(EncodedProducer {
                head,
                condition: if reading {
                    &candidate.condition
                } else {
                    &p.condition
                },
                body,
                reading,
            });
        }
        let mut encoded_bodies = [Vec::new(), Vec::new()];
        let mut firing = [None, None];
        for p in &producers {
            let guard = functions.encode(p.condition, &mut cnf, b)?;
            for m in 0..2 {
                let value = if p.reading {
                    let v = cnf.var(b)?;
                    cnf.clause(vec![!v, guard], b)?;
                    firing[m] = Some(v);
                    v
                } else {
                    let mut body = vec![guard];
                    body.extend(p.body.iter().map(|(i, pos)| {
                        if *pos {
                            variables[m][*i]
                        } else {
                            !variables[m][*i]
                        }
                    }));
                    cnf.and(&body, b)?
                };
                encoded_bodies[m].push(value);
            }
        }
        for m in 0..2 {
            for (head, ps) in by_head.iter().enumerate() {
                let bodies = ps.iter().map(|i| encoded_bodies[m][*i]).collect::<Vec<_>>();
                let value = cnf.or(&bodies, b)?;
                cnf.clause(vec![!variables[m][head], value], b)?;
                cnf.clause(vec![variables[m][head], !value], b)?;
            }
        }
        cnf.clause(vec![variables[0][target], variables[1][target]], b)?;
        cnf.clause(vec![!variables[0][target], !variables[1][target]], b)?;
        cnf.solver.cb().check()?;
        let answer = cnf.solver.solve_limited(&[]);
        cnf.solver.cb().check()?;
        if answer == lbool::FALSE {
            return Ok(SatProbeAnswer::Unsat);
        }
        if answer != lbool::TRUE {
            return Err(CheckError::InvalidRequest(
                "candidate SAT search interrupted",
            ));
        }
        // Validate the candidate independently against the Boolean functions and
        // completed producer bodies, not the solver's auxiliary Tseitin bits.
        let value = |v| cnf.solver.value_lit(v) == lbool::TRUE;
        let mut observation = BddValuation::all_false(cone.domain.diagnostic_bdd().num_vars());
        for (i, v) in &functions.inputs {
            observation.set_value(biodivine_lib_bdd::BddVariable::from_index(*i), value(*v));
        }
        if !cone.domain.diagnostic_bdd().eval_in(&observation) {
            return Err(CheckError::InvalidRequest(
                "candidate probe pair violates its domain",
            ));
        }
        let reading_fires = firing.map(|v| v.is_some_and(value));
        let mut models = [BTreeSet::new(), BTreeSet::new()];
        for m in 0..2 {
            let mut supported = vec![false; cone.atoms.len()];
            for p in &producers {
                b.charge(
                    p.body.len() + p.condition.node_count(),
                    "candidate probe pair validation",
                )?;
                let guard = p.condition.diagnostic_bdd().eval_in(&observation);
                let holds = if p.reading {
                    if reading_fires[m] && !guard {
                        return Err(CheckError::InvalidRequest(
                            "candidate probe firing outside guard",
                        ));
                    }
                    reading_fires[m]
                } else {
                    guard
                        && p.body
                            .iter()
                            .all(|(i, pos)| value(variables[m][*i]) == *pos)
                };
                supported[p.head] |= holds;
            }
            for (i, a) in cone.atoms.iter().enumerate() {
                b.tick("candidate probe pair validation")?;
                if supported[i] != value(variables[m][i]) {
                    return Err(CheckError::InvalidRequest(
                        "candidate probe pair is not supported",
                    ));
                }
                if supported[i] {
                    models[m].insert(a.clone());
                }
            }
        }
        let differing = models[0]
            .symmetric_difference(&models[1])
            .cloned()
            .collect::<BTreeSet<_>>();
        if !differing.contains(&literal.term.atom) {
            return Err(CheckError::InvalidRequest(
                "candidate probe pair agrees on premise",
            ));
        }
        let mut world = BTreeSet::new();
        for (a, v) in ctx.diagnostic_inputs() {
            b.tick("candidate probe observation")?;
            if observation.value(v) {
                world.insert(a.clone());
            }
        }
        report.pair = Some(CandidateProbePair {
            world,
            models,
            differing,
            reading_fires,
        });
        Ok(SatProbeAnswer::Sat)
    })();
    match result {
        Ok(answer) => report.answer = answer,
        Err(CheckError::Cancelled) => return Err(CheckError::Cancelled),
        Err(e) => {
            report.reason = Some(e.to_string());
            report.exhaustion = Inconclusive::from_error(e).ok();
        }
    }
    report.variables = cnf.solver.num_vars() as usize;
    report.clauses = cnf.clauses;
    report.literals = cnf.literals;
    report.elapsed = start.elapsed();
    Ok(report)
}

#[cfg(test)]
mod tests;
