use super::*;
#[derive(Debug)]
pub enum Existence {
    EveryWorld,
    NoMeaning(Observation),
    Inconclusive(Inconclusive),
}
#[derive(Debug)]
pub enum Uniqueness {
    AtMostOne,
    Multiple {
        observation: Observation,
        first: Model,
        second: Model,
    },
    Inconclusive(Inconclusive),
}
#[derive(Debug)]
pub struct Meaning {
    pub existence: Existence,
    pub uniqueness: Uniqueness,
}
impl Meaning {
    pub fn unique_everywhere(&self) -> bool {
        matches!(self.existence, Existence::EveryWorld)
            && matches!(self.uniqueness, Uniqueness::AtMostOne)
    }
}
impl Engine {
    pub(super) fn meaning(&mut self, options: &CheckOptions) -> Result<Meaning> {
        // Local stratification of original ground rules is a sufficient theorem,
        // independent of U/W. It needs no admission or symbolic evaluation.
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        let stratified = (|| {
            for c in self.program.components() {
                b.tick("SAT stratification")?;
                if c.cycle.is_some() {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        match stratified {
            Ok(true) => {
                return Ok(Meaning {
                    existence: Existence::EveryWorld,
                    uniqueness: Uniqueness::AtMostOne,
                });
            }
            Err(e) => {
                let c = query_inconclusive(e)?;
                return Ok(Meaning {
                    existence: Existence::Inconclusive(c),
                    uniqueness: Uniqueness::Inconclusive(c),
                });
            }
            Ok(false) => {}
        }
        let existence = self.existence(options)?;
        let uniqueness = self.uniqueness()?;
        Ok(Meaning {
            existence,
            uniqueness,
        })
    }
    fn existence(&mut self, options: &CheckOptions) -> Result<Existence> {
        let _progress = self.limits.progress.scope("SAT existence", None, true);
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        let result: Result<Existence> = (|| {
            let mut remaining = Query::default();
            let mut worlds = 0;
            loop {
                let world = match self.phase_query(Mode::World, &remaining, &mut b)? {
                    Answer::NoModel => return Ok(Existence::EveryWorld),
                    Answer::Inconclusive(c) => return Err(c.into()),
                    Answer::Model(m) => m,
                };
                b.room(worlds, options.max_worlds, "SAT existence", "worlds")?;
                worlds += 1;
                let observation = world.observation(&mut b)?;
                let pins = observation
                    .present
                    .iter()
                    .map(|a| (a.clone(), true))
                    .chain(observation.absent.iter().map(|a| (a.clone(), false)))
                    .collect();
                match self.phase_query(
                    Mode::Program,
                    &Query {
                        pins,
                        exclude: vec![],
                    },
                    &mut b,
                )? {
                    Answer::NoModel => return Ok(Existence::NoMeaning(observation)),
                    Answer::Inconclusive(c) => return Err(c.into()),
                    Answer::Model(m) => {
                        let values = m.cone_values(&self.cone, &mut b)?;
                        let cover = existence::cover(&self.cone, &values, &mut b)?;
                        // This sufficient cube preserves all producer truth and
                        // finite support. Subsequent world queries still enforce W.
                        remaining.exclude.push(
                            cover
                                .into_iter()
                                .map(|i| (self.cone.atoms[i].clone(), values[i]))
                                .collect(),
                        );
                    }
                }
            }
        })();
        match result {
            Ok(v) => Ok(v),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok(Existence::Inconclusive(query_inconclusive(
                    e.in_phase("SAT existence", None),
                )?))
            }
        }
    }
    fn uniqueness(&mut self) -> Result<Uniqueness> {
        let _progress = self.limits.progress.scope("SAT uniqueness", None, true);
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        self.stats = Stats::default();
        if let Some(e) = &self.append_failed {
            return Ok(Uniqueness::Inconclusive(query_inconclusive(e.clone())?));
        }
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.timeout = limits.timeout;
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result: Result<Uniqueness> = (|| {
            if self.pair_encoding.is_none() {
                let built: Result<(Lit, Encoding)> = (|| {
                    let gate = self.cnf.var(&mut b)?;
                    self.cnf.gate = Some(gate);
                    let second = encode(
                        &self.cone,
                        &mut self.cnf,
                        self.truth,
                        Some(&self.program_encoding.vars),
                        &mut b,
                    )?;
                    let mut differences = Vec::new();
                    for i in 0..self.cone.atoms.len() {
                        b.tick("SAT uniqueness encoding")?;
                        if self.cone.input[i] || self.cone.fixed[i].is_some() {
                            continue;
                        }
                        let a = self.program_encoding.vars[i];
                        let z = second.vars[i];
                        let left = self.cnf.and(&[a, !z], &mut b)?;
                        let right = self.cnf.and(&[!a, z], &mut b)?;
                        differences.extend([left, right]);
                    }
                    self.cnf.clause(differences, &mut b)?;
                    Ok((gate, second))
                })();
                match built {
                    Ok(e) => self.pair_encoding = Some(e),
                    Err(e) => {
                        self.append_failed = Some(e.clone());
                        return Err(e);
                    }
                }
            }
            loop {
                let gate = self.pair_encoding.as_ref().unwrap().0;
                if !self.solve(&[self.active, gate], conflicts, propagations, &mut b)? {
                    return Ok(Uniqueness::AtMostOne);
                }
                let mut pair = Vec::new();
                let mut refined = false;
                for side in 0..2 {
                    let e = if side == 0 {
                        &self.program_encoding
                    } else {
                        &self.pair_encoding.as_ref().unwrap().1
                    };
                    b.charge(e.vars.len(), "SAT uniqueness assignment")?;
                    let values = e
                        .vars
                        .iter()
                        .map(|l| self.cnf.solver.value_lit(*l) == lbool::TRUE)
                        .collect::<Vec<_>>();
                    let unfounded = least_unfounded(&self.cone, &values, &mut b)?;
                    if unfounded.is_empty() {
                        pair.push(self.model(Mode::Program, &values));
                        continue;
                    }
                    b.room(
                        self.stats.refinements,
                        self.config.max_refinements,
                        "SAT uniqueness",
                        "refinements",
                    )?;
                    self.cnf.gate = Some(if side == 0 { self.active } else { gate });
                    if let Err(e) = refine(&self.cone, e, unfounded, &mut self.cnf, &mut b) {
                        self.append_failed = Some(e.clone());
                        return Err(e);
                    }
                    self.stats.refinements += 1;
                    refined = true;
                    break;
                }
                if !refined {
                    let second = pair.pop().unwrap();
                    let first = pair.pop().unwrap();
                    let observation = first.observation(&mut b)?;
                    return Ok(Uniqueness::Multiple {
                        observation,
                        first,
                        second,
                    });
                }
            }
        })();
        self.stats.variables = self.cnf.solver.num_vars() as usize;
        self.stats.clauses = self.cnf.clauses;
        self.stats.literals = self.cnf.literals;
        self.stats.conflicts = self.cnf.solver.num_conflicts() - conflicts;
        self.stats.propagations = self.cnf.solver.num_propagations() - propagations;
        match result {
            Ok(v) => Ok(v),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok(Uniqueness::Inconclusive(query_inconclusive(
                    e.in_phase("SAT uniqueness", None),
                )?))
            }
        }
    }
}
impl Model {
    fn cone_values(&self, c: &Cone, b: &mut Budget<'_>) -> Result<Vec<bool>> {
        b.charge(c.fixed.len(), "SAT model cover")?;
        Ok((0..c.fixed.len())
            .map(|i| c.fixed[i].unwrap_or_else(|| self.values[i / 64] & (1u64 << (i % 64)) != 0))
            .collect())
    }
}
