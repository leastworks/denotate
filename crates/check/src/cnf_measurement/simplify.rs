//! U-only, acyclic measurement experiments. No rewrite reaches ordinary checking.
use super::{
    model::{Binding, Model, atom},
    *,
};
use std::time::{Duration, Instant};
mod local;
mod trace;
pub use local::ProofShape;
use local::{Answer, Question};
pub use trace::{LocalDifference, ProofObservation};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pass {
    Hash,
    Constants,
    DeadPremises,
    Subsumption,
}
impl Pass {
    pub fn label(self) -> &'static str {
        match self {
            Self::Hash => "structural-hashing",
            Self::Constants => "constants",
            Self::DeadPremises => "dead-rules-and-premises",
            Self::Subsumption => "syntactic-subsumption",
        }
    }
}
#[derive(Clone, Debug)]
pub struct SimplificationLimits {
    pub max_cone_atoms: usize,
    pub max_bdd_nodes: usize,
    pub max_proof_work: usize,
}
impl Default for SimplificationLimits {
    fn default() -> Self {
        Self {
            max_cone_atoms: 64,
            max_bdd_nodes: 4096,
            max_proof_work: 50_000,
        }
    }
}
#[derive(Debug)]
pub struct PassStats {
    pub pass: Pass,
    pub candidates: usize,
    pub proved: usize,
    pub unchanged: usize,
    pub unsupported: usize,
    pub cut_off: usize,
    pub elapsed: Duration,
}
impl PassStats {
    fn new(pass: Pass) -> Self {
        Self {
            pass,
            candidates: 0,
            proved: 0,
            unchanged: 0,
            unsupported: 0,
            cut_off: 0,
            elapsed: Duration::ZERO,
        }
    }
}
#[derive(Debug)]
pub struct Variant {
    pub name: &'static str,
    pub report: Report,
    pub passes: Vec<PassStats>,
    pub proof_bytes: usize,
    pub mapping_bytes: usize,
    pub model_bytes: usize,
    pub elapsed: Duration,
}

// These entries belong to the sequential rewritten snapshots. Together with the
// immutable original graph they identify the removed body/premise and reason.
// No BDDs or solver-selected worlds are retained as evidence.
#[derive(Debug)]
enum Reason {
    Identical(usize),
    Constant(bool),
    Dead,
    Implied(i32),
    Subsumed(Vec<i32>),
}
#[derive(Debug)]
struct Record {
    head: usize,
    body: Vec<i32>,
    reason: Reason,
}
impl Record {
    fn binding(&self) -> Option<Binding> {
        match self.reason {
            Reason::Identical(a) => Some(Binding::Atom(a)),
            Reason::Constant(v) => Some(Binding::Constant(v)),
            _ => None,
        }
    }
}
struct Changes {
    records: Vec<Record>,
}
impl Changes {
    fn record(
        &mut self,
        head: usize,
        body: Vec<i32>,
        reason: Reason,
        b: &mut Budget<'_>,
    ) -> Result<&Record> {
        b.room(
            self.records.len(),
            b.limits.max_rules,
            "CNF rewrite records",
            "records",
        )?;
        b.charge(body.len() + 1, "CNF rewrite records")?;
        self.records.push(Record { head, body, reason });
        Ok(self.records.last().unwrap())
    }
    fn bytes(&self) -> usize {
        self.records.capacity() * std::mem::size_of::<Record>()
            + self
                .records
                .iter()
                .map(|r| {
                    let extra = match &r.reason {
                        Reason::Subsumed(body) => body.capacity() * 4,
                        _ => 0,
                    };
                    r.body.capacity() * 4 + extra
                })
                .sum::<usize>()
    }
}

impl Measurement {
    /// Independent controls and one sequential composition. Each variant has a
    /// fresh allowance; an exhausted local proof changes no candidate.
    pub fn simplify_comparison(
        &self,
        local: &SimplificationLimits,
        limits: &Limits,
    ) -> Result<Vec<Variant>> {
        let all = &[
            Pass::Hash,
            Pass::Constants,
            Pass::DeadPremises,
            Pass::Subsumption,
        ][..];
        let cases: [(&str, &[Pass], bool); 8] = [
            ("baseline", &[], false),
            ("baseline+elimination", &[], true),
            ("structural-hashing", &[Pass::Hash], false),
            ("constants", &[Pass::Constants], false),
            ("dead-rules-and-premises", &[Pass::DeadPremises], false),
            ("syntactic-subsumption", &[Pass::Subsumption], false),
            ("all", all, false),
            ("all+elimination", all, true),
        ];
        let mut variants = Vec::new();
        for (name, passes, eliminate) in cases {
            let start = Instant::now();
            let mut b = Budget::new(limits);
            let mut model = Model::new(&self.program, &mut b)?;
            let mut changes = Changes {
                records: Vec::new(),
            };
            let mut stats = Vec::new();
            for pass in passes {
                stats.push(apply(&mut model, *pass, local, &mut changes, &mut b)?);
            }
            let (mut cnf, candidates) = model.encode(&mut b)?;
            let report = self.report_cnf(&mut cnf, &candidates, eliminate, &mut b)?;
            variants.push(Variant {
                name,
                report,
                passes: stats,
                proof_bytes: changes.bytes(),
                model_bytes: model.vector_bytes(),
                mapping_bytes: model.binding.capacity() * std::mem::size_of::<Binding>(),
                elapsed: start.elapsed(),
            });
        }
        Ok(variants)
    }
}
fn eligible(m: &Model, h: usize, s: &mut PassStats) -> bool {
    if m.inputs[h] || m.resolve(h) != Binding::Atom(h) {
        return false;
    }
    if m.recursive[h] {
        s.unsupported += 1;
        return false;
    }
    true
}
fn query(
    m: &Model,
    q: Question<'_>,
    local: &SimplificationLimits,
    s: &mut PassStats,
    b: &mut Budget<'_>,
) -> Result<Option<Answer>> {
    s.candidates += 1;
    let mut limits = b.limits.clone();
    limits.max_work = limits.max_work.min(local.max_proof_work).min(b.remaining());
    let globally_bounded = b.remaining() <= local.max_proof_work;
    let mut proof = Budget::new(&limits);
    let result = local::prove(m, q, local, &mut proof);
    b.charge(
        limits.max_work.saturating_sub(proof.remaining()),
        "CNF local proofs",
    )?;
    b.check("CNF local proofs")?;
    match result {
        Ok(answer) => {
            if answer == Answer::No {
                s.unchanged += 1;
            } else {
                s.proved += 1;
            }
            Ok(Some(answer))
        }
        Err(CheckError::LimitExceeded {
            resource: "work", ..
        }) if globally_bounded => Err(b.work_exhaustion("CNF local proofs")),
        Err(CheckError::LimitExceeded { .. }) => {
            s.cut_off += 1;
            Ok(None)
        }
        Err(e) => Err(e),
    }
}
fn apply(
    m: &mut Model,
    pass: Pass,
    local: &SimplificationLimits,
    changes: &mut Changes,
    b: &mut Budget<'_>,
) -> Result<PassStats> {
    let start = Instant::now();
    let mut stats = PassStats::new(pass);
    let mut intern = BTreeMap::<Vec<Vec<i32>>, usize>::new();
    for h in m.order.clone() {
        b.tick("CNF simplification")?;
        if !eligible(m, h, &mut stats) {
            continue;
        }
        let mut defs = m.definitions(h, b)?;
        match pass {
            Pass::Hash => {
                stats.candidates += 1;
                if let Some(rep) = intern.get(&defs) {
                    let record = changes.record(h, vec![], Reason::Identical(*rep), b)?;
                    m.binding[record.head] = record.binding().unwrap();
                    stats.proved += 1;
                } else {
                    intern.insert(defs, h);
                    stats.unchanged += 1;
                }
            }
            Pass::Constants => {
                if let Some(Answer::Constant(value)) =
                    query(m, Question::Constant(h), local, &mut stats, b)?
                {
                    let record = changes.record(h, vec![], Reason::Constant(value), b)?;
                    m.binding[record.head] = record.binding().unwrap();
                }
            }
            Pass::DeadPremises => {
                // Earlier removals in this head cannot feed its providers: h is acyclic.
                let mut next = Vec::new();
                for body in defs {
                    if query(m, Question::Dead(&body), local, &mut stats, b)? == Some(Answer::Yes) {
                        changes.record(h, body, Reason::Dead, b)?;
                        continue;
                    }
                    let mut current = body;
                    for premise in current.clone() {
                        if query(
                            m,
                            Question::Implied(&current, premise),
                            local,
                            &mut stats,
                            b,
                        )? == Some(Answer::Yes)
                        {
                            let record =
                                changes.record(h, current.clone(), Reason::Implied(premise), b)?;
                            if let Reason::Implied(proven) = record.reason {
                                current.retain(|l| *l != proven);
                            }
                        }
                    }
                    next.push(current);
                }
                m.bodies[h] = next;
            }
            Pass::Subsumption => {
                // Retained shortest bodies justify removals; a supporting body
                // is never itself removed later in this pass.
                defs.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
                let mut next: Vec<Vec<i32>> = Vec::new();
                let mut work = 0usize;
                for body in &defs {
                    stats.candidates += 1;
                    let mut cover = None;
                    let mut cut = false;
                    for other in &next {
                        let cost = body.len() + other.len() + 1;
                        if work.saturating_add(cost) > local.max_proof_work {
                            cut = true;
                            break;
                        }
                        work += cost;
                        b.charge(cost, "CNF syntactic subsumption")?;
                        if other.len() < body.len()
                            && other.iter().all(|l| body.binary_search(l).is_ok())
                        {
                            cover = Some(other);
                            break;
                        }
                    }
                    if let Some(other) = cover {
                        changes.record(h, body.clone(), Reason::Subsumed(other.clone()), b)?;
                        stats.proved += 1;
                    } else {
                        next.push(body.clone());
                        if cut {
                            stats.cut_off += 1;
                        } else {
                            stats.unchanged += 1;
                        }
                    }
                }
                m.bodies[h] = next;
            }
        }
    }
    stats.elapsed = start.elapsed();
    Ok(stats)
}

#[cfg(test)]
mod tests;
