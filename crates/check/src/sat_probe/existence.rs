//! For every permitted world, search for a reduct-verified model.
//! Two query modes share one SAT engine. Model completion must be disabled when
//! choosing a world: otherwise worlds with no model disappear from the search.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatExistenceAnswer {
    EveryWorld,
    NoMeaning,
    InconsistentAssumptions,
    Unknown,
}
impl SatExistenceAnswer {
    pub fn label(self) -> &'static str {
        match self {
            Self::EveryWorld => "every-world",
            Self::NoMeaning => "no-meaning",
            Self::InconsistentAssumptions => "inconsistent-assumptions",
            Self::Unknown => "unknown",
        }
    }
}
#[derive(Debug, Clone)]
pub struct SatExistenceReport {
    pub answer: SatExistenceAnswer,
    /// True inputs in the entire encoded cone; all other cone inputs are false.
    pub world: Option<BTreeSet<GroundAtom>>,
    pub reason: Option<String>,
    pub worlds: usize,
    pub covers: usize,
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

/// W alone, plus free inputs from the full cone. No target equations may filter
/// which worlds are proposed. Assumption definitions retain their stable meaning.
fn world_cone(c: &Cone, negative_target: bool, b: &mut Budget<'_>) -> Result<Cone> {
    let mut producers = vec![Vec::new(); c.atoms.len()];
    for (j, r) in c.rules.iter().enumerate() {
        b.tick("SAT existence world cone")?;
        producers[r.head].push(j);
    }
    let mut needed = vec![false; c.atoms.len()];
    let mut pending = c
        .groups
        .iter()
        .flat_map(|(_, g)| g.iter().copied())
        .collect::<Vec<_>>();
    while let Some(a) = pending.pop() {
        b.tick("SAT existence world cone")?;
        if needed[a] {
            continue;
        }
        needed[a] = true;
        if negative_target && c.target[a] {
            return Err(CheckError::InvalidRequest(
                "SAT existence assumptions depend on the target negative component",
            ));
        }
        for j in &producers[a] {
            b.charge(c.rules[*j].body.len(), "SAT existence world cone")?;
            pending.extend(c.rules[*j].body.iter().map(|(a, _)| *a));
        }
    }
    b.charge(c.atoms.len() + c.rules.len(), "SAT existence world cone")?;
    Ok(Cone {
        atoms: c.atoms.clone(),
        rules: c.rules.iter().filter(|r| needed[r.head]).cloned().collect(),
        fixed: c
            .fixed
            .iter()
            .enumerate()
            .map(|(i, v)| {
                if needed[i] || c.input[i] {
                    *v
                } else {
                    Some(false)
                }
            })
            .collect(),
        input: c.input.clone(),
        target: vec![false; c.atoms.len()],
        duplicated: vec![false; c.atoms.len()],
        groups: c.groups.clone(),
    })
}

struct Encoding {
    vars: Vec<Lit>,
    bodies: Vec<Lit>,
}
fn encode(
    c: &Cone,
    cnf: &mut Cnf,
    truth: Lit,
    inputs: Option<&[Lit]>,
    b: &mut Budget<'_>,
) -> Result<Encoding> {
    let mut vars = Vec::new();
    for i in 0..c.atoms.len() {
        b.tick("SAT existence encoding")?;
        vars.push(match c.fixed[i] {
            Some(true) => truth,
            Some(false) => !truth,
            None if c.input[i] && inputs.is_some() => inputs.unwrap()[i],
            None => cnf.var(b)?,
        });
    }
    let mut producers = vec![Vec::new(); c.atoms.len()];
    let mut bodies = Vec::new();
    for r in &c.rules {
        b.charge(1 + r.body.len(), "SAT existence encoding")?;
        let lits = r
            .body
            .iter()
            .map(|(a, pos)| if *pos { vars[*a] } else { !vars[*a] })
            .collect::<Vec<_>>();
        let body = cnf.and(&lits, b)?;
        producers[r.head].push(body);
        bodies.push(body);
    }
    for i in 0..c.atoms.len() {
        if c.input[i] || c.fixed[i].is_some() {
            continue;
        }
        let body = cnf.or(&producers[i], b)?;
        cnf.clause(vec![!vars[i], body], b)?;
        cnf.clause(vec![vars[i], !body], b)?;
    }
    for (kind, group) in &c.groups {
        let lits = group.iter().map(|i| vars[*i]).collect::<Vec<_>>();
        if kind.has_coverage() {
            cnf.clause(lits.clone(), b)?;
        }
        if kind.has_uniqueness() {
            cnf.at_most_one(&lits, b)?;
        }
        if *kind == Cardinality::Empty {
            for l in lits {
                cnf.clause(vec![!l], b)?;
            }
        }
    }
    Ok(Encoding { vars, bodies })
}

/// Find a stable model, adding only loop clauses valid in every input world.
/// All clauses follow the caller's query gate; failed model queries cannot
/// constrain the world search. One aggregate refinement count covers both modes.
fn stable_model(
    c: &Cone,
    e: &Encoding,
    pins: &[Lit],
    cnf: &mut Cnf,
    probe: &SatProbeLimits,
    report: &mut SatExistenceReport,
    b: &mut Budget<'_>,
) -> Result<Option<Vec<bool>>> {
    loop {
        b.tick("SAT existence solve")?;
        cnf.solver.cb().check()?;
        report.solves += 1;
        let start = Instant::now();
        let answer = cnf.solver.solve_limited(pins);
        report.solve_time += start.elapsed();
        cnf.solver.cb().check()?;
        if answer == lbool::FALSE {
            return Ok(None);
        }
        if answer != lbool::TRUE {
            return Err(CheckError::Internal(
                "SAT existence solver stopped without a limit",
            ));
        }
        b.charge(e.vars.len(), "SAT existence assignment")?;
        let model = e
            .vars
            .iter()
            .map(|v| cnf.solver.value_lit(*v) == lbool::TRUE)
            .collect::<Vec<_>>();
        let unfounded = least_unfounded(c, &model, b)?;
        if unfounded.is_empty() {
            return Ok(Some(model));
        }
        if report.refinements >= probe.max_refinements {
            return Err(CheckError::limit(
                "SAT existence",
                "refinements",
                probe.max_refinements,
                Some(report.refinements + 1),
            ));
        }
        let mut external = Vec::new();
        for (j, r) in c.rules.iter().enumerate() {
            b.charge(1 + r.body.len(), "SAT existence refinement")?;
            if unfounded.contains(&r.head)
                && !r.body.iter().any(|(a, pos)| *pos && unfounded.contains(a))
            {
                external.push(e.bodies[j]);
            }
        }
        let support = cnf.or(&external, b)?;
        for a in unfounded {
            cnf.clause(vec![!e.vars[a], support], b)?;
        }
        report.refinements += 1;
    }
}

/// Sufficient cube on which the same derived interpretation stays stable.
/// Preserve every true body (and therefore its reduct derivations). For each
/// false body preserve one false premise: a fixed derived premise needs no input
/// pin; otherwise pin one false input. This also prevents new producers from
/// becoming enabled. Merely keeping the true derivation's input leaves is unsound.
fn cover(c: &Cone, model: &[bool], b: &mut Budget<'_>) -> Result<BTreeSet<usize>> {
    let mut inputs = BTreeSet::new();
    for r in &c.rules {
        b.charge(1 + r.body.len() * 2, "SAT existence model cover")?;
        let false_literals = r
            .body
            .iter()
            .filter(|(a, pos)| model[*a] != *pos)
            .collect::<Vec<_>>();
        if false_literals.is_empty() {
            inputs.extend(
                r.body
                    .iter()
                    .filter(|(a, _)| c.input[*a] && c.fixed[*a].is_none())
                    .map(|(a, _)| *a),
            );
        } else if false_literals
            .iter()
            .all(|(a, _)| c.input[*a] && c.fixed[*a].is_none())
        {
            inputs.insert(false_literals[0].0);
        }
    }
    Ok(inputs)
}

pub(super) fn search(
    p: &GroundProgram,
    component: ComponentId,
    restrictions: &[Restriction],
    probe: &SatProbeLimits,
    limits: &Limits,
) -> Result<SatExistenceReport> {
    let start = Instant::now();
    let mut b = Budget::new(limits);
    let mut report = SatExistenceReport {
        answer: SatExistenceAnswer::Unknown,
        world: None,
        reason: None,
        worlds: 0,
        covers: 0,
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
        gate: None,
    };
    let result = (|| {
        let c = cone(p, component, restrictions, &mut b)?;
        report.cone_atoms = c.atoms.len();
        report.cone_rules = c.rules.len();
        let w = world_cone(&c, p.component(component).unwrap().cycle.is_some(), &mut b)?;
        let truth = cnf.var(&mut b)?;
        cnf.clause(vec![truth], &mut b)?;
        let active = cnf.var(&mut b)?;
        let worlds = encode(&w, &mut cnf, truth, None, &mut b)?;
        cnf.gate = Some(active);
        let models = encode(&c, &mut cnf, truth, Some(&worlds.vars), &mut b)?;
        loop {
            cnf.gate = None;
            let Some(world) = stable_model(
                &w,
                &worlds,
                &[!active],
                &mut cnf,
                probe,
                &mut report,
                &mut b,
            )?
            else {
                report.answer = if report.worlds == 0 {
                    SatExistenceAnswer::InconsistentAssumptions
                } else {
                    SatExistenceAnswer::EveryWorld
                };
                return Ok(());
            };
            report.worlds += 1;
            b.charge(c.atoms.len(), "SAT existence observation")?;
            let mut pins = vec![active];
            pins.extend((0..c.atoms.len()).filter(|i| c.input[*i]).map(|i| {
                if world[i] {
                    worlds.vars[i]
                } else {
                    !worlds.vars[i]
                }
            }));
            cnf.gate = Some(active);
            let Some(model) =
                stable_model(&c, &models, &pins, &mut cnf, probe, &mut report, &mut b)?
            else {
                report.world = Some(
                    c.atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| c.input[*i] && world[*i])
                        .map(|(_, a)| a.clone())
                        .collect(),
                );
                report.answer = SatExistenceAnswer::NoMeaning;
                return Ok(());
            };
            let cube = cover(&c, &model, &mut b)?;
            // Exclude the cube only from subsequent world proposals, never from
            // model searches. This is intentionally gated in the opposite mode.
            cnf.gate = Some(!active);
            cnf.clause(
                cube.iter()
                    .map(|i| {
                        if world[*i] {
                            !worlds.vars[*i]
                        } else {
                            worlds.vars[*i]
                        }
                    })
                    .collect(),
                &mut b,
            )?;
            report.covers += 1;
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

#[cfg(test)]
mod tests;
