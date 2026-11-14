//! Opt-in diagnostic search, independent of BDD admission and checking results.
//! Completion overapproximates stable models. Every SAT pair is verified by the
//! reduct's least model; unfounded sets yield sound external-support clauses.
use crate::{
    limits::{Budget, Result},
    *,
};
use batsat::{Callbacks, Lit, Solver, SolverInterface, lbool};
use denotate_ir::{Cardinality, ConstantId, RelationId};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone)]
pub struct SatProbeLimits {
    pub timeout: Duration,
    pub max_refinements: usize,
}
impl Default for SatProbeLimits {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(10),
            max_refinements: 64,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatProbeAnswer {
    Sat,
    Unsat,
    Unknown,
}
impl SatProbeAnswer {
    pub fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}
#[derive(Debug, Clone)]
pub struct SatProbePair {
    /// True inputs in the component/assumption cone. Unlisted inputs are false.
    pub world: BTreeSet<GroundAtom>,
    /// True atoms of the target component, independently verified stable in the cone.
    pub models: [BTreeSet<GroundAtom>; 2],
    pub differing: BTreeSet<GroundAtom>,
}
#[derive(Debug, Clone)]
pub struct SatProbeReport {
    pub component: ComponentId,
    pub answer: SatProbeAnswer,
    pub reason: Option<String>,
    pub pair: Option<SatProbePair>,
    pub supported_pair_seen: bool,
    pub refinements: usize,
    pub solves: usize,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    pub cone_atoms: usize,
    pub cone_rules: usize,
    pub solve_time: Duration,
    pub elapsed: Duration,
}

struct Stop {
    cancellation: Cancellation,
    start: Instant,
    timeout: Duration,
    #[cfg(test)]
    hook: Option<Box<dyn Fn()>>,
}
impl Stop {
    fn check(&self) -> Result<()> {
        self.cancellation.check()?;
        if self.start.elapsed() >= self.timeout {
            return Err(CheckError::deadline("SAT probe", self.timeout));
        }
        Ok(())
    }
}
impl Callbacks for Stop {
    fn stop(&self) -> bool {
        #[cfg(test)]
        if let Some(hook) = &self.hook {
            hook();
        }
        self.check().is_err()
    }
}
struct Cnf {
    solver: Solver<Stop>,
    clauses: usize,
    literals: usize,
}
impl Cnf {
    fn var(&mut self, b: &mut Budget<'_>) -> Result<Lit> {
        b.room(
            self.solver.num_vars() as usize,
            b.limits.max_atoms.min((u32::MAX / 2 - 2) as usize),
            "SAT probe CNF",
            "variables",
        )?;
        Ok(Lit::new(self.solver.new_var_default(), true))
    }
    fn clause(&mut self, mut lits: Vec<Lit>, b: &mut Budget<'_>) -> Result<()> {
        b.room(self.clauses, b.limits.max_rules, "SAT probe CNF", "clauses")?;
        let next = self.literals.saturating_add(lits.len());
        if next > b.limits.max_dependencies {
            return Err(CheckError::limit(
                "SAT probe CNF",
                "literals",
                b.limits.max_dependencies,
                Some(next),
            ));
        }
        b.charge(lits.len(), "SAT probe CNF")?;
        self.clauses += 1;
        self.literals = next;
        self.solver.cb().check()?;
        self.solver.add_clause_reuse(&mut lits);
        self.solver.cb().check()
    }
    fn and(&mut self, lits: &[Lit], b: &mut Budget<'_>) -> Result<Lit> {
        if lits.len() == 1 {
            return Ok(lits[0]);
        }
        let v = self.var(b)?;
        for l in lits {
            self.clause(vec![!v, *l], b)?;
        }
        self.clause(
            std::iter::once(v).chain(lits.iter().map(|l| !*l)).collect(),
            b,
        )?;
        Ok(v)
    }
    fn or(&mut self, lits: &[Lit], b: &mut Budget<'_>) -> Result<Lit> {
        Ok(!self.and(&lits.iter().map(|l| !*l).collect::<Vec<_>>(), b)?)
    }
    fn at_most_one(&mut self, lits: &[Lit], b: &mut Budget<'_>) -> Result<()> {
        // Linear prefix encoding instead of a quadratic pairwise expansion.
        let mut prefix: Option<Lit> = None;
        for l in lits {
            if let Some(p) = prefix {
                self.clause(vec![!p, !*l], b)?;
                prefix = Some(self.or(&[p, *l], b)?);
            } else {
                prefix = Some(*l);
            }
        }
        Ok(())
    }
}
struct Rule {
    head: usize,
    body: Vec<(usize, bool)>,
}
struct Cone {
    atoms: Vec<GroundAtom>,
    rules: Vec<Rule>,
    target: Vec<bool>,
    duplicated: Vec<bool>,
    fixed: Vec<Option<bool>>,
    input: Vec<bool>,
    groups: Vec<(Cardinality, Vec<usize>)>,
}

impl PreparedCheck<'_> {
    /// Probe one prepared (pre-admission) component. No receipts, caches, limits
    /// or verdicts in the ordinary checker are modified by this operation.
    pub fn sat_probe(
        &self,
        component: ComponentId,
        probe: &SatProbeLimits,
        operations: &OperationalLimits,
    ) -> Result<SatProbeReport> {
        let mut limits = self.request.limits.with_operations(operations);
        limits.timeout = probe.timeout;
        limits.progress = Default::default();
        limits.profile = Default::default();
        let mut restrictions = Vec::new();
        for c in &self.request.constraints {
            let r = self
                .program
                .signatures
                .keys()
                .find(|r| {
                    self.semantic_keys
                        .relation(**r)
                        .is_ok_and(|key| key == c.relation())
                })
                .ok_or(CheckError::InvalidRequest(
                    "unknown SAT probe assumption relation",
                ))?;
            restrictions.push((*r, c.kind(), c.group_by().to_vec()));
        }
        probe_component(&self.program, component, &restrictions, probe, &limits)
    }
}

type Restriction = (RelationId, Cardinality, Vec<usize>);
fn cone(
    p: &GroundProgram,
    component: ComponentId,
    restrictions: &[Restriction],
    b: &mut Budget<'_>,
) -> Result<Cone> {
    if p.rewrite_proofs().next().is_some() {
        return Err(CheckError::InvalidRequest(
            "SAT probe requires a pre-admission program",
        ));
    }
    let target = p
        .component(component)
        .ok_or(CheckError::InvalidRequest("unknown SAT probe component"))?
        .atoms
        .iter()
        .collect::<BTreeSet<_>>();
    let mut pending = BTreeSet::from([component]);
    let mut atoms = BTreeSet::new();
    let mut groups = Vec::new();
    let mut assumption_atoms = 0;
    for (relation, kind, columns) in restrictions {
        let mut grouped = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
        if kind.has_coverage() {
            let signature = &p.signatures[relation];
            let domains = columns
                .iter()
                .map(|c| &p.domains[&signature[*c]])
                .collect::<Vec<_>>();
            if !domains.iter().any(|d| d.is_empty()) {
                let mut positions = vec![0; domains.len()];
                loop {
                    b.room(
                        grouped.len(),
                        b.limits.max_atoms,
                        "SAT probe assumptions",
                        "groups",
                    )?;
                    grouped.insert(
                        positions
                            .iter()
                            .enumerate()
                            .map(|(i, j)| domains[i][*j])
                            .collect(),
                        Vec::new(),
                    );
                    let mut i = positions.len();
                    loop {
                        if i == 0 {
                            break;
                        }
                        i -= 1;
                        positions[i] += 1;
                        if positions[i] < domains[i].len() {
                            break;
                        }
                        positions[i] = 0;
                    }
                    if positions.iter().all(|i| *i == 0) {
                        break;
                    }
                }
            }
        }
        for atom in p.atoms() {
            b.tick("SAT probe assumptions")?;
            if atom.relation != *relation {
                continue;
            }
            b.room(
                assumption_atoms,
                b.limits.max_atoms,
                "SAT probe assumptions",
                "atoms",
            )?;
            assumption_atoms += 1;
            grouped
                .entry(columns.iter().map(|i| atom.arguments[*i]).collect())
                .or_default()
                .push(atom.clone());
            pending.insert(p.component_for(atom)?.id);
        }
        for values in grouped.into_values() {
            b.room(
                groups.len(),
                b.limits.max_atoms,
                "SAT probe assumptions",
                "groups",
            )?;
            groups.push((*kind, values));
        }
    }
    let mut seen = BTreeSet::new();
    let mut rules = Vec::new();
    while let Some(id) = pending.pop_first() {
        b.tick("SAT probe cone")?;
        if !seen.insert(id) {
            continue;
        }
        let c = p
            .component(id)
            .ok_or(CheckError::InvalidRequest("foreign SAT probe dependency"))?;
        // Shared upstream atoms must have independent stratified meaning. Their
        // positive recursion is checked by reduct replay, not trusted completion.
        if id != component && c.cycle.is_some() {
            return Err(CheckError::InvalidRequest(
                "SAT probe has an unresolved upstream negative component",
            ));
        }
        for a in &c.atoms {
            if !atoms.contains(a) {
                b.room(atoms.len(), b.limits.max_atoms, "SAT probe cone", "atoms")?;
                atoms.insert(a.clone());
            }
        }
        if c.atoms.iter().all(|a| p.fixed_value(a).is_some()) {
            continue;
        }
        pending.extend(c.dependencies.iter().copied());
        for index in &p.component_rules[id.index] {
            b.room(rules.len(), b.limits.max_rules, "SAT probe cone", "rules")?;
            let r = &p.core.rules[*index];
            if !r.replacements.is_empty() {
                return Err(CheckError::InvalidRequest(
                    "SAT probe requires original rule bodies",
                ));
            }
            for l in &r.body {
                b.tick("SAT probe cone")?;
                if !atoms.contains(&l.term.atom) {
                    b.room(atoms.len(), b.limits.max_atoms, "SAT probe cone", "atoms")?;
                    atoms.insert(l.term.atom.clone());
                }
            }
            rules.push(r);
        }
    }
    let atoms = atoms.into_iter().collect::<Vec<_>>();
    let index = atoms
        .iter()
        .enumerate()
        .map(|(i, a)| (a, i))
        .collect::<BTreeMap<_, _>>();
    let mut dependencies = 0;
    let rules = rules
        .into_iter()
        .map(|r| {
            let mut body = BTreeSet::new();
            for l in &r.body {
                b.room(
                    dependencies,
                    b.limits.max_dependencies,
                    "SAT probe cone",
                    "dependencies",
                )?;
                dependencies += 1;
                body.insert((index[&l.term.atom], l.polarity == Polarity::Positive));
            }
            Ok(Rule {
                head: index[&r.head.atom],
                body: body.into_iter().collect(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let fixed = atoms
        .iter()
        .map(|a| {
            p.fixed_value(a)
                .or_else(|| (!p.atom_index.contains_key(a)).then_some(false))
        })
        .collect();
    let input = atoms.iter().map(|a| p.inputs.contains(a)).collect();
    let target = atoms.iter().map(|a| target.contains(a)).collect::<Vec<_>>();
    // An assumption may inspect a positive component through downstream rules.
    // Those definitions must follow each copy too; only true upstream providers
    // and inputs are shared. A reverse worklist keeps this linear in the cone.
    let mut duplicated = target.clone();
    let mut readers = vec![Vec::new(); atoms.len()];
    for r in &rules {
        for (a, _) in &r.body {
            b.tick("SAT probe copies")?;
            readers[*a].push(r.head);
        }
    }
    let mut pending = (0..atoms.len())
        .filter(|i| duplicated[*i])
        .collect::<Vec<_>>();
    while let Some(a) = pending.pop() {
        for head in &readers[a] {
            b.tick("SAT probe copies")?;
            if !duplicated[*head] {
                duplicated[*head] = true;
                pending.push(*head);
            }
        }
    }
    let groups = groups
        .into_iter()
        .map(|(k, g)| (k, g.iter().map(|a| index[a]).collect()))
        .collect();
    Ok(Cone {
        atoms,
        rules,
        fixed,
        input,
        target,
        duplicated,
        groups,
    })
}

fn probe_component(
    p: &GroundProgram,
    component: ComponentId,
    restrictions: &[Restriction],
    probe: &SatProbeLimits,
    limits: &Limits,
) -> Result<SatProbeReport> {
    let start = Instant::now();
    let mut report = SatProbeReport {
        component,
        answer: SatProbeAnswer::Unknown,
        reason: None,
        pair: None,
        supported_pair_seen: false,
        refinements: 0,
        solves: 0,
        variables: 0,
        clauses: 0,
        literals: 0,
        cone_atoms: 0,
        cone_rules: 0,
        solve_time: Duration::ZERO,
        elapsed: Duration::ZERO,
    };
    let mut cnf = Cnf {
        solver: Solver::new(
            Default::default(),
            Stop {
                cancellation: limits.cancellation.clone(),
                start,
                timeout: limits.timeout,
                #[cfg(test)]
                hook: None,
            },
        ),
        clauses: 0,
        literals: 0,
    };
    let mut budget = Budget::new(limits);
    let result = (|| {
        let c = cone(p, component, restrictions, &mut budget)?;
        report.cone_atoms = c.atoms.len();
        report.cone_rules = c.rules.len();
        let truth = cnf.var(&mut budget)?;
        cnf.clause(vec![truth], &mut budget)?;
        let mut vars = Vec::new();
        for i in 0..c.atoms.len() {
            let v = match c.fixed[i] {
                Some(true) => truth,
                Some(false) => !truth,
                None => cnf.var(&mut budget)?,
            };
            vars.push([
                v,
                if c.duplicated[i] && c.fixed[i].is_none() {
                    cnf.var(&mut budget)?
                } else {
                    v
                },
            ]);
        }
        let mut producers = vec![Vec::new(); c.atoms.len()];
        let mut bodies = Vec::new();
        for (j, r) in c.rules.iter().enumerate() {
            producers[r.head].push(j);
            let mut pair = [truth; 2];
            for side in 0..2 {
                if side == 1 && !c.duplicated[r.head] {
                    pair[1] = pair[0];
                    continue;
                }
                let lits = r
                    .body
                    .iter()
                    .map(|(a, pos)| {
                        if *pos {
                            vars[*a][side]
                        } else {
                            !vars[*a][side]
                        }
                    })
                    .collect::<Vec<_>>();
                pair[side] = cnf.and(&lits, &mut budget)?;
            }
            bodies.push(pair);
        }
        for i in 0..c.atoms.len() {
            if c.input[i] || c.fixed[i].is_some() {
                continue;
            }
            for side in 0..if c.duplicated[i] { 2 } else { 1 } {
                let body = cnf.or(
                    &producers[i]
                        .iter()
                        .map(|j| bodies[*j][side])
                        .collect::<Vec<_>>(),
                    &mut budget,
                )?;
                cnf.clause(vec![!vars[i][side], body], &mut budget)?;
                cnf.clause(vec![vars[i][side], !body], &mut budget)?;
            }
        }
        for (kind, group) in &c.groups {
            for side in 0..2 {
                let lits = group.iter().map(|i| vars[*i][side]).collect::<Vec<_>>();
                if kind.has_coverage() {
                    cnf.clause(lits.clone(), &mut budget)?;
                }
                if kind.has_uniqueness() {
                    cnf.at_most_one(&lits, &mut budget)?;
                }
                if *kind == Cardinality::Empty {
                    for l in lits {
                        cnf.clause(vec![!l], &mut budget)?;
                    }
                }
            }
        }
        let mut differing = Vec::new();
        for i in 0..c.atoms.len() {
            if !c.target[i] {
                continue;
            }
            let [a, b] = vars[i];
            let x = cnf.and(&[a, !b], &mut budget)?;
            let y = cnf.and(&[!a, b], &mut budget)?;
            differing.extend([x, y]);
        }
        cnf.clause(differing, &mut budget)?;
        loop {
            budget.tick("SAT probe solve")?;
            cnf.solver.cb().check()?;
            report.solves += 1;
            let t = Instant::now();
            let answer = cnf.solver.solve_limited(&[]);
            report.solve_time += t.elapsed();
            cnf.solver.cb().check()?;
            if answer == lbool::FALSE {
                report.answer = SatProbeAnswer::Unsat;
                return Ok(());
            }
            if answer != lbool::TRUE {
                return Err(CheckError::Internal(
                    "SAT probe solver stopped without a limit",
                ));
            }
            report.supported_pair_seen = true;
            let models = [0, 1].map(|side| {
                vars.iter()
                    .map(|v| cnf.solver.value_lit(v[side]) == lbool::TRUE)
                    .collect::<Vec<_>>()
            });
            let unfounded = [
                least_unfounded(&c, &models[0], &mut budget)?,
                least_unfounded(&c, &models[1], &mut budget)?,
            ];
            if unfounded.iter().all(|u| u.is_empty()) {
                let select = |side: usize| {
                    c.atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| c.target[*i] && models[side][*i])
                        .map(|(_, a)| a.clone())
                        .collect::<BTreeSet<_>>()
                };
                report.pair = Some(SatProbePair {
                    world: c
                        .atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| c.input[*i] && models[0][*i])
                        .map(|(_, a)| a.clone())
                        .collect(),
                    models: [select(0), select(1)],
                    differing: c
                        .atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| c.target[*i] && models[0][*i] != models[1][*i])
                        .map(|(_, a)| a.clone())
                        .collect(),
                });
                report.answer = SatProbeAnswer::Sat;
                return Ok(());
            }
            if report.refinements >= probe.max_refinements {
                return Err(CheckError::limit(
                    "SAT probe",
                    "refinements",
                    probe.max_refinements,
                    Some(report.refinements + 1),
                ));
            }
            for (side, u) in unfounded.iter().enumerate().filter(|(_, u)| !u.is_empty()) {
                // Every stable model gives any true atom in U support from a rule
                // with no positive premise in U. These clauses hold in ALL worlds,
                // rather than forbidding the current assignment unconditionally.
                let mut external = Vec::new();
                for (j, r) in c.rules.iter().enumerate() {
                    budget.charge(1 + r.body.len(), "SAT probe refinement")?;
                    if u.contains(&r.head) && !r.body.iter().any(|(a, pos)| *pos && u.contains(a)) {
                        external.push(bodies[j][side]);
                    }
                }
                let support = cnf.or(&external, &mut budget)?;
                for a in u {
                    cnf.clause(vec![!vars[*a][side], support], &mut budget)?;
                }
            }
            report.refinements += 1;
        }
    })();
    report.variables = cnf.solver.num_vars() as usize;
    report.clauses = cnf.clauses;
    report.literals = cnf.literals;
    report.elapsed = start.elapsed();
    match result {
        Ok(()) => {}
        Err(CheckError::Cancelled) => return Err(CheckError::Cancelled),
        Err(e) => report.reason = Some(e.to_string()),
    }
    Ok(report)
}

/// Linear worklist evaluation of the candidate's reduct, independent of the
/// production evaluator/admission and of SAT. Positive cycles need real support.
fn least_unfounded(c: &Cone, model: &[bool], b: &mut Budget<'_>) -> Result<BTreeSet<usize>> {
    let mut truth = vec![false; c.atoms.len()];
    let mut queue = Vec::new();
    for i in 0..truth.len() {
        b.tick("SAT probe reduct")?;
        if c.fixed[i] == Some(true) || c.input[i] && model[i] {
            truth[i] = true;
            queue.push(i);
        }
    }
    let mut needed = vec![0; c.rules.len()];
    let mut readers = vec![Vec::new(); truth.len()];
    for (j, r) in c.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, "SAT probe reduct")?;
        if r.body.iter().any(|(a, pos)| !*pos && model[*a]) {
            continue;
        }
        for (a, pos) in &r.body {
            if *pos {
                needed[j] += 1;
                readers[*a].push(j);
            }
        }
        if needed[j] == 0 && !truth[r.head] {
            truth[r.head] = true;
            queue.push(r.head);
        }
    }
    while let Some(a) = queue.pop() {
        for j in &readers[a] {
            b.tick("SAT probe reduct")?;
            needed[*j] -= 1;
            if needed[*j] == 0 {
                let head = c.rules[*j].head;
                if !truth[head] {
                    truth[head] = true;
                    queue.push(head);
                }
            }
        }
    }
    if truth.iter().zip(model).any(|(a, m)| *a && !m) {
        return Err(CheckError::Internal(
            "SAT candidate does not model its reduct",
        ));
    }
    Ok((0..truth.len())
        .filter(|i| model[*i] && !truth[*i])
        .collect())
}

#[cfg(test)]
mod tests;

pub(crate) mod candidates;
pub use candidates::{
    CandidateProbeCounts, CandidateProbeLimits, CandidateProbePair, CandidateProbeReport,
};
