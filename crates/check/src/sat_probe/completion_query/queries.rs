use super::*;

struct Run<'a> {
    engine: &'a Engine,
    budget: Budget<'a>,
    cnf: Cnf,
    truth: Lit,
    world: Encoding,
    inactive: Vec<Lit>,
    solves: usize,
}

impl Engine {
    /// W alone. No completion equations outside selected acyclic restrictions
    /// can suppress an otherwise permitted observation.
    pub fn worlds(&self, query: &WorldQuery) -> Result<WorldAnswer> {
        let result: Result<WorldAnswer> = (|| {
            let mut run = Run::new(self)?;
            let mut pins = Vec::new();
            for (a, value) in &query.pins {
                let l = run.input(a)?;
                pins.push(if *value { l } else { !l });
            }
            for cube in &query.exclude {
                let mut clause = Vec::new();
                for (a, value) in cube {
                    let l = run.input(a)?;
                    clause.push(if *value { !l } else { l });
                }
                run.cnf.clause(clause, &mut run.budget)?;
            }
            if !run.solve(&pins)? {
                return Ok(WorldAnswer::NoWorld);
            }
            let values = checked_assignment(&self.world, &run.world, &run.cnf, &mut run.budget)?;
            Ok(WorldAnswer::World(
                self.model(values, ModelScope::WholeProgram).observation(),
            ))
        })();
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(WorldAnswer::Inconclusive(inconclusive(
                e.in_phase("completion world", None),
            )?)),
        }
    }

    /// All omitted eligible inputs are absent. First check membership in W,
    /// then classify in H's original upstream cone, then check processing with
    /// that unique classification pinned. No downstream model chooses a class.
    pub fn observation(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
    ) -> Result<ObservationOutcome> {
        let mut present_set = BTreeSet::new();
        let result = (|| {
            let mut run = Run::new(self)?;
            for a in present {
                run.budget.tick("completion observation")?;
                if !self.program.inputs.contains(&a) {
                    return Err(CheckError::InvalidObservation(a));
                }
                present_set.insert(a);
            }
            let mut pins = Vec::new();
            for a in &self.program.inputs {
                let l = run.input(a)?;
                pins.push(if present_set.contains(a) { l } else { !l });
            }
            if !run.solve(&pins)? {
                return Ok(ObservationOutcome::NotPermitted);
            }
            // Validate W independently, before any program equations are installed.
            checked_assignment(&self.world, &run.world, &run.cnf, &mut run.budget)?;
            let Some((cone, members, hypothesis)) = &self.classification else {
                return Ok(ObservationOutcome::WholeProgram(run.models(
                    &self.cone,
                    &pins,
                    None,
                    ModelScope::WholeProgram,
                    None,
                )?));
            };
            match run.models(
                cone,
                &pins,
                Some(*hypothesis),
                ModelScope::Classification,
                None,
            )? {
                Interpretations::NoMeaning => Ok(ObservationOutcome::Rejected),
                Interpretations::Multiple { first, second } => {
                    Ok(ObservationOutcome::Ambiguous { first, second })
                }
                Interpretations::Inconclusive { cause, example } => {
                    Ok(ObservationOutcome::Inconclusive { cause, example })
                }
                Interpretations::Unique(classification) => {
                    let processing = run.models(
                        &self.cone,
                        &pins,
                        None,
                        ModelScope::Processing,
                        Some((members, &classification)),
                    )?;
                    Ok(ObservationOutcome::Accepted {
                        classification,
                        processing,
                    })
                }
            }
        })();
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(ObservationOutcome::Inconclusive {
                cause: inconclusive(e.in_phase("completion observation", None))?,
                example: None,
            }),
        }
    }
}

impl<'a> Run<'a> {
    fn new(engine: &'a Engine) -> Result<Self> {
        let mut budget = Budget::new(&engine.limits);
        budget.check("completion query")?;
        let mut cnf = Cnf {
            solver: Solver::new(
                Default::default(),
                Stop {
                    polls: Some(PollLimit {
                        used: std::cell::Cell::new(0),
                        max: engine.config.max_solver_polls,
                    }),
                    cancellation: engine.limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: engine.limits.timeout,
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        let truth = cnf.var(&mut budget)?;
        cnf.clause(vec![truth], &mut budget)?;
        let world = encode(&engine.world, &mut cnf, truth, None, &mut budget)?;
        Ok(Self {
            engine,
            budget,
            cnf,
            truth,
            world,
            inactive: vec![],
            solves: 0,
        })
    }

    fn input(&mut self, atom: &GroundAtom) -> Result<Lit> {
        self.budget
            .charge(atom.arguments.len() + 1, "completion input query")?;
        self.engine.program.validate_atom(atom)?;
        if !self.engine.input_relations.contains(&atom.relation) {
            return Err(CheckError::InvalidRequest(
                "world queries accept input atoms only",
            ));
        }
        // A legal tuple outside `within` is always false, including if it occurs
        // in an original rule and therefore has a (non-input) inventory entry.
        if !self.engine.program.inputs.contains(atom) {
            return Ok(!self.truth);
        }
        Ok(self.world.vars[self.engine.program.atom_index[atom]])
    }

    fn solve(&mut self, pins: &[Lit]) -> Result<bool> {
        self.budget.tick("completion solve")?;
        self.cnf.solver.cb().check()?;
        self.budget.room(
            self.solves,
            self.engine.config.max_solves,
            "completion solve",
            "solves",
        )?;
        self.solves += 1;
        let answer = self.cnf.solver.solve_limited(pins);
        self.cnf.solver.cb().check()?;
        for (used, limit, resource) in [
            (
                self.cnf.solver.num_conflicts(),
                self.engine.config.max_conflicts,
                "conflicts",
            ),
            (
                self.cnf.solver.num_propagations(),
                self.engine.config.max_propagations,
                "propagations",
            ),
        ] {
            if used > limit {
                return Err(CheckError::limit(
                    "completion solve",
                    resource,
                    limit.try_into().unwrap_or(usize::MAX),
                    Some(used.try_into().unwrap_or(usize::MAX)),
                ));
            }
        }
        self.budget.check("completion solve")?;
        if answer == lbool::TRUE {
            Ok(true)
        } else if answer == lbool::FALSE {
            Ok(false)
        } else {
            Err(CheckError::Internal(
                "completion solver stopped without a limit",
            ))
        }
    }

    fn models(
        &mut self,
        cone: &Cone,
        world_pins: &[Lit],
        hypothesis: Option<usize>,
        scope: ModelScope,
        accepted: Option<(&BTreeSet<GroundAtom>, &Model)>,
    ) -> Result<Interpretations> {
        let mut example = None;
        let phase = match scope {
            ModelScope::Classification => "completion classification",
            ModelScope::Processing => "completion processing",
            ModelScope::WholeProgram => "completion meaning",
        };
        let result: Result<Interpretations> = (|| {
            let gate = self.cnf.var(&mut self.budget)?;
            self.cnf.gate = Some(gate);
            let e = encode(
                cone,
                &mut self.cnf,
                self.truth,
                Some(&self.world.vars),
                &mut self.budget,
            )?;
            let mut pins = world_pins.to_vec();
            pins.extend(self.inactive.iter().map(|g| !*g));
            pins.push(gate);
            if let Some(h) = hypothesis {
                pins.push(e.vars[h]);
            }
            if let Some((members, model)) = accepted {
                for atom in members {
                    self.budget.tick(phase)?;
                    let i = self
                        .engine
                        .program
                        .atom_index
                        .get(atom)
                        .copied()
                        .unwrap_or(cone.atoms.len() + 1);
                    pins.push(if model.value(atom).unwrap() {
                        e.vars[i]
                    } else {
                        !e.vars[i]
                    });
                }
            }
            self.inactive.push(gate);
            if !self.solve(&pins)? {
                return Ok(Interpretations::NoMeaning);
            }
            let values = checked_assignment(cone, &e, &self.cnf, &mut self.budget)?;
            let first = self.engine.model(values, scope);
            example = Some(first.clone());
            // Exclude exactly this interpretation on original relational atoms,
            // never the auxiliary body/encoding variables. World inputs are pinned.
            let mut different = Vec::new();
            for (i, atom) in cone.atoms.iter().enumerate() {
                self.budget.tick(phase)?;
                if self.engine.input_relations.contains(&atom.relation) {
                    continue;
                }
                if let Some(value) = first.value(atom) {
                    different.push(if value { !e.vars[i] } else { e.vars[i] });
                }
            }
            let second_gate = self.cnf.var(&mut self.budget)?;
            self.cnf.gate = Some(second_gate);
            self.cnf.clause(different, &mut self.budget)?;
            self.inactive.push(second_gate);
            pins.push(second_gate);
            if !self.solve(&pins)? {
                return Ok(Interpretations::Unique(first));
            }
            let values = checked_assignment(cone, &e, &self.cnf, &mut self.budget)?;
            Ok(Interpretations::Multiple {
                first,
                second: self.engine.model(values, scope),
            })
        })();
        self.cnf.gate = None;
        match result {
            Ok(a) => Ok(a),
            Err(e) => Ok(Interpretations::Inconclusive {
                cause: inconclusive(e.in_phase(phase, None))?,
                example,
            }),
        }
    }
}

/// Check the original finite equations, not merely that SAT returned a model.
fn checked_assignment(
    cone: &Cone,
    e: &Encoding,
    cnf: &Cnf,
    b: &mut Budget<'_>,
) -> Result<Vec<bool>> {
    let mut values = Vec::new();
    for l in &e.vars {
        b.tick("completion model validation")?;
        values.push(cnf.solver.value_lit(*l) == lbool::TRUE);
    }
    let mut produced = vec![false; values.len()];
    for r in &cone.rules {
        b.charge(r.body.len() + 1, "completion model validation")?;
        produced[r.head] |= r.body.iter().all(|(a, pos)| values[*a] == *pos);
    }
    for i in 0..values.len() {
        b.tick("completion model validation")?;
        if let Some(fixed) = cone.fixed[i] {
            if values[i] != fixed {
                return Err(CheckError::Internal("invalid completion constant"));
            }
        } else if !cone.input[i] && values[i] != produced[i] {
            return Err(CheckError::Internal(
                "SAT interpretation violates original completion",
            ));
        }
    }
    for (kind, group) in &cone.groups {
        b.charge(group.len() + 1, "completion model validation")?;
        let n = group.iter().filter(|i| values[**i]).count();
        if (kind.has_coverage() && n == 0)
            || (kind.has_uniqueness() && n > 1)
            || (*kind == Cardinality::Empty && n != 0)
        {
            return Err(CheckError::Internal(
                "SAT interpretation violates input restriction",
            ));
        }
    }
    Ok(values)
}
