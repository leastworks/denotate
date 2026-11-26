use super::*;

pub(super) struct Run<'a, 'b, 'l> {
    pub(super) engine: &'a Engine,
    pub(super) budget: &'b mut Budget<'l>,
    pub(super) cnf: Cnf,
    pub(super) truth: Lit,
    pub(super) world: Encoding,
    inactive: Vec<Lit>,
    /// This run's allowance: capped by its engine's `config` (a local cap),
    /// debiting the enclosing scope (question or pass) with every solve.
    pub(super) ledger: Arc<super::ledger::SatLedger>,
    certified: bool,
    formula_pins: bool,
    work_started: usize,
    solve_timings: Vec<crate::CompletionSolveTiming>,
    omitted_solve_timings: usize,
    solve_time: Duration,
}

impl Drop for Run<'_, '_, '_> {
    fn drop(&mut self) {
        if let Some((_, stats)) = &mut self.cnf.measurement {
            stats.solve_timings = std::mem::take(&mut self.solve_timings);
            stats.omitted_solve_timings = self.omitted_solve_timings;
            stats.solve_time = self.solve_time;
            stats.work = Some(self.budget.used().saturating_sub(self.work_started));
            stats.work_by_phase = self.budget.query_work();
        }
    }
}

impl Engine {
    /// Certified W alone. No completion equations outside selected restrictions
    /// can suppress an otherwise permitted observation.
    pub fn worlds(&self, query: &WorldQuery) -> Result<WorldAnswer> {
        // One allowance for the query and its no-world assumption audit.
        let scoped = self.scoped();
        let this = &*scoped;
        let result = this.worlds_using(query, &mut Budget::new(&this.limits))?;
        if matches!(result, WorldAnswer::NoWorld)
            && this
                .assumption_analysis(&CheckOptions::default())?
                .iter()
                .any(|a| !a.certified())
        {
            return Ok(WorldAnswer::Inconclusive(contracts::uncertified()));
        }
        Ok(result)
    }
    pub(super) fn worlds_using(
        &self,
        query: &WorldQuery,
        budget: &mut Budget<'_>,
    ) -> Result<WorldAnswer> {
        let result: Result<WorldAnswer> = (|| {
            let mut run = Run::new(self, budget)?;
            run.label("completion worlds");
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
                run.cnf.clause(clause, run.budget)?;
            }
            if !run.solve(&pins)? {
                return Ok(WorldAnswer::NoWorld);
            }
            let values = checked_assignment(&self.world, &run.world, &run.cnf, run.budget)?;
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
    /// then classify in H's live upstream cone, then check processing with
    /// its established decisions pinned, retaining C and H. Helpers remain free;
    /// no downstream model chooses a class.
    pub fn observation(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
    ) -> Result<ObservationOutcome> {
        self.observation_using(present, &mut Budget::new(&self.limits), true)
    }
    pub(super) fn observation_using(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
        processing: bool,
    ) -> Result<ObservationOutcome> {
        // One allowance for the whole observation: assumption audits and the query.
        let scoped = self.scoped();
        let this = &*scoped;
        let mut present_set = BTreeSet::new();
        let result = (|| {
            for a in present {
                budget.tick("completion observation")?;
                if !self.program.inputs.contains(&a) {
                    return Err(CheckError::InvalidObservation(a));
                }
                present_set.insert(a);
            }
            let issues = this.assumptions_at(&present_set, budget)?;
            if !issues.is_empty() {
                return Ok(ObservationOutcome::UndeterminedAssumptions(issues));
            }
            let mut run = Run::new(this, budget)?;
            run.label("completion observation");
            // Inputs stay pinned through every query below; their assumption
            // determinacy was already established independently.
            run.certified = false;
            let mut pins = Vec::new();
            for a in &self.program.inputs {
                let l = run.input(a)?;
                pins.push(if present_set.contains(a) { l } else { !l });
            }
            if !run.solve(&pins)? {
                return Ok(ObservationOutcome::NotPermitted);
            }
            // Validate W independently, before any program equations are installed.
            checked_assignment(&self.world, &run.world, &run.cnf, run.budget)?;
            let Some((cone, members, hypothesis)) = &self.classification else {
                if !processing {
                    return Ok(ObservationOutcome::WholeProgram(
                        Interpretations::NotAnalysed,
                    ));
                }
                return Ok(ObservationOutcome::WholeProgram(run.models(
                    &self.cone,
                    &pins,
                    None,
                    ModelScope::WholeProgram,
                    None,
                    false,
                )?));
            };
            match run.models(
                cone,
                &pins,
                Some(*hypothesis),
                ModelScope::Classification,
                None,
                false,
            )? {
                Interpretations::NoMeaning => {
                    // Existence of C is independent of determinacy: one validated
                    // interpretation is enough. Disable the earlier H query gate.
                    match run.models(
                        cone,
                        &pins,
                        None,
                        ModelScope::ClassificationWithoutHypothesis,
                        None,
                        true,
                    )? {
                        Interpretations::Unique(without_hypothesis) => {
                            Ok(ObservationOutcome::Rejected { without_hypothesis })
                        }
                        Interpretations::NoMeaning => {
                            Ok(ObservationOutcome::ClassificationNoMeaning)
                        }
                        Interpretations::Inconclusive { cause, .. } => {
                            Ok(ObservationOutcome::Inconclusive {
                                cause,
                                example: None,
                            })
                        }
                        _ => unreachable!(),
                    }
                }
                Interpretations::Multiple { first, second } => {
                    Ok(ObservationOutcome::Ambiguous { first, second })
                }
                Interpretations::Inconclusive { cause, example } => {
                    Ok(ObservationOutcome::Inconclusive { cause, example })
                }
                Interpretations::Unique(classification) => {
                    let processing = if processing {
                        run.models(
                            &self.cone,
                            &pins,
                            Some(*hypothesis),
                            ModelScope::Processing,
                            Some((members, &classification)),
                            false,
                        )?
                    } else {
                        Interpretations::NotAnalysed
                    };
                    Ok(ObservationOutcome::Accepted {
                        classification,
                        processing,
                    })
                }
                Interpretations::NotAnalysed => unreachable!(),
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

#[cfg(test)]
pub(super) fn property(
    engine: &Engine,
    cone: &Cone,
    members: Arc<BTreeSet<GroundAtom>>,
    world: &Observation,
    classification: Option<&Model>,
    part: &PropertyPart,
    budget: &mut Budget<'_>,
) -> Result<Option<Model>> {
    let mut run = Run::new(engine, budget)?;
    let e = encode(
        cone,
        &mut run.cnf,
        run.truth,
        Some(&run.world.vars),
        run.budget,
    )?;
    let mut pins = Vec::new();
    for a in &world.present {
        pins.push(run.input(a)?);
    }
    for a in &world.absent {
        pins.push(!run.input(a)?);
    }
    if let Some(model) = classification {
        let (_, members, hypothesis) = engine.classification.as_ref().unwrap();
        pins.push(e.vars[*hypothesis]);
        for a in members.iter() {
            run.budget.tick("completion property classification")?;
            if !engine.decision(a) {
                continue;
            }
            let i = engine
                .program
                .atom_index
                .get(a)
                .copied()
                .unwrap_or(cone.atoms.len() + 1);
            pins.push(if model.value(a).unwrap() {
                e.vars[i]
            } else {
                !e.vars[i]
            });
        }
    }
    let mut lits = Vec::new();
    for a in &part.tuples {
        run.budget.tick("completion property tuples")?;
        lits.push(e.vars[engine.program.atom_index[a]]);
    }
    match part.component {
        Cardinality::Empty => pins.extend(lits),
        Cardinality::AtLeastOne => pins.extend(lits.iter().map(|l| !*l)),
        Cardinality::AtMostOne => {
            let mut seen = !run.truth;
            let mut many = !run.truth;
            for l in lits {
                let both = run.cnf.and(&[seen, l], run.budget)?;
                many = run.cnf.or(&[many, both], run.budget)?;
                seen = run.cnf.or(&[seen, l], run.budget)?;
            }
            pins.push(many);
        }
        Cardinality::ExactlyOne => unreachable!(),
    }
    if !run.solve(&pins)? {
        return Ok(None);
    }
    let values = checked_assignment(cone, &e, &run.cnf, run.budget)?;
    let mut model = engine.model(values, ModelScope::Property);
    model.members = Some(members);
    Ok(Some(model))
}

impl<'a, 'b, 'l> Run<'a, 'b, 'l> {
    pub(super) fn label(&mut self, phase: &'static str) {
        if let Some((_, stats)) = &mut self.cnf.measurement {
            stats.phase = phase;
        }
    }
    pub(super) fn new(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        let mut run = Self::universe(engine, budget)?;
        for a in engine.assumptions.iter() {
            let local;
            let e = if a.cone.rules.is_empty() {
                // With no defining rules, derived tuples are false, exactly as
                // in U. Input-only restrictions need no equation copy at all.
                &run.world
            } else {
                local = encoding::encode_named(
                    &a.cone,
                    &mut run.cnf,
                    run.truth,
                    Some(&run.world.vars),
                    run.budget,
                    "selected-assumption",
                )?;
                &local
            };
            let truth = a.formula(e, &mut run.cnf, run.truth, run.budget)?;
            run.cnf.clause(vec![truth], run.budget)?;
        }
        for pin in &engine.formula_pins {
            let l = pin
                .certificate
                .encode(&run.world.vars, run.truth, &mut run.cnf, run.budget)?;
            run.cnf
                .clause(vec![if pin.value { l } else { !l }], run.budget)?;
        }
        run.formula_pins = true;
        run.certified = true;
        Ok(run)
    }
    pub(super) fn universe(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        Self::base(engine, budget, true, engine.run_ledger())
    }
    /// A run inside another run's allowance (certification): it shares and
    /// debits all four of that run's allowances, with no cap of its own.
    pub(super) fn universe_under(
        engine: &'a Engine,
        budget: &'b mut Budget<'l>,
        parent: &Arc<super::ledger::SatLedger>,
    ) -> Result<Self> {
        Self::base(
            engine,
            budget,
            true,
            parent.child(super::ledger::unbounded()),
        )
    }
    /// Local boundary queries need neither W nor an input-universe encoding.
    pub(super) fn local(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        Self::base(engine, budget, false, engine.run_ledger())
    }
    fn base(
        engine: &'a Engine,
        budget: &'b mut Budget<'l>,
        universe: bool,
        ledger: Arc<super::ledger::SatLedger>,
    ) -> Result<Self> {
        let work_started = budget.used();
        budget.begin_query_work();
        budget.check("completion query")?;
        let mut cnf = Cnf {
            measurement: engine.limits.completion_sizes.clone().map(|sink| {
                (
                    sink,
                    crate::CompletionSearchSize {
                        branch_depth: None,
                        solve_timings: vec![],
                        omitted_solve_timings: 0,
                        solve_time: Duration::ZERO,
                        existence: Default::default(),
                        elapsed: Duration::ZERO,
                        work: None,
                        work_by_phase: Default::default(),
                        phase: "completion query",
                        variables: 0,
                        clauses: 0,
                        literals: 0,
                        encodings: 0,
                        encoding_details: vec![],
                        omitted_encodings: 0,
                    },
                )
            }),
            solver: Solver::new(
                Default::default(),
                Stop {
                    exploration: engine
                        .limits
                        .completion_exploration
                        .then(|| engine.limits.progress.clone()),
                    deadline: engine.limits.run_deadline,
                    // Each solve sets its own poll room from the ledger.
                    polls: Some(PollLimit {
                        used: std::cell::Cell::new(0),
                        max: usize::MAX,
                    }),
                    cancellation: engine.limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: engine.limits.timeout.min(budget.remaining_time()),
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        let truth = cnf.var(budget)?;
        cnf.clause(vec![truth], budget)?;
        let world = if universe {
            encoding::encode_named(
                &engine.world,
                &mut cnf,
                truth,
                None,
                budget,
                "input-universe",
            )?
        } else {
            Encoding {
                vars: vec![],
                validation: None,
            }
        };
        Ok(Self {
            engine,
            budget,
            cnf,
            truth,
            world,
            inactive: vec![],
            ledger,
            certified: false,
            formula_pins: false,
            work_started,
            solve_timings: vec![],
            omitted_solve_timings: 0,
            solve_time: Duration::ZERO,
        })
    }

    pub(super) fn input(&mut self, atom: &GroundAtom) -> Result<Lit> {
        self.budget
            .charge(atom.arguments.len() + 1, "completion input query")?;
        if self
            .engine
            .ignored_input_domains
            .iter()
            .any(|d| d.input == atom.relation)
        {
            return Err(CheckError::InvalidRequest(
                "input domain is outside this verification's dependency scope",
            ));
        }
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

    pub(super) fn input_pins(&self, values: &[bool]) -> Vec<Lit> {
        self.engine
            .world
            .input
            .iter()
            .enumerate()
            .filter_map(|(i, input)| {
                input.then_some(if values[i] {
                    self.world.vars[i]
                } else {
                    !self.world.vars[i]
                })
            })
            .collect()
    }
    pub(super) fn exclude(&mut self, cube: &BTreeMap<usize, bool>) -> Result<()> {
        self.budget
            .charge(cube.len(), "completion assumption cube")?;
        self.cnf.clause(
            cube.iter()
                .map(|(i, v)| {
                    if *v {
                        !self.world.vars[*i]
                    } else {
                        self.world.vars[*i]
                    }
                })
                .collect(),
            self.budget,
        )
    }
    pub(super) fn solve(&mut self, pins: &[Lit]) -> Result<bool> {
        while self.raw_solve(pins)? {
            if !self.certified {
                return Ok(true);
            }
            let values =
                checked_assignment(&self.engine.world, &self.world, &self.cnf, self.budget)?;
            let mut excluded = false;
            for a in self.engine.assumptions.iter() {
                if !a.recursive {
                    continue;
                }
                // A separate solver prevents downstream equations, H, other
                // restrictions and candidate exclusions from choosing A's truth.
                let parent = self.ledger.clone();
                let mut check = Run::universe_under(self.engine, self.budget, &parent)?;
                check.label("completion assumption certification");
                let result: Result<_> = (|| {
                    let e = encode(
                        &a.cone,
                        &mut check.cnf,
                        check.truth,
                        Some(&check.world.vars),
                        check.budget,
                    )?;
                    let formula = a.formula(&e, &mut check.cnf, check.truth, check.budget)?;
                    let mut fixed = check.input_pins(&values);
                    fixed.push(!formula);
                    if !check.solve(&fixed)? {
                        return Ok(None);
                    }
                    let model = checked_assignment(&a.cone, &e, &check.cnf, check.budget)?;
                    Ok(Some(super::symbolic::cover(
                        &a.cone,
                        &model,
                        None,
                        check.budget,
                    )?))
                })();
                drop(check);
                if let Some(cube) = result? {
                    self.exclude(&cube)?;
                    excluded = true;
                    break;
                }
            }
            if !excluded {
                return Ok(true);
            }
        }
        Ok(false)
    }
    /// Preserve the former per-part SAT allowances while retaining clauses.
    /// The enclosing work/CNF allowances and deadline never restart.
    pub(super) fn next_property_part(&mut self) -> Result<()> {
        self.budget.check("completion property")?;
        self.cnf.solver.cb().check_time()?;
        self.ledger.reset();
        Ok(())
    }
    /// Local uniqueness uses arbitrary shared boundary values, with no W/H.
    /// Release its CNF afterwards, while charging the enclosing query's work,
    /// solves, polls, conflicts, propagations and deadline (no renewed allowance).
    pub(super) fn local_unique(
        &mut self,
        cone: &Cone,
        mut solving: impl FnMut(usize, usize),
    ) -> (Result<bool>, usize, usize, usize) {
        let local = Cnf {
            measurement: None,
            solver: Solver::new(
                Default::default(),
                Stop {
                    exploration: self
                        .engine
                        .limits
                        .completion_exploration
                        .then(|| self.engine.limits.progress.clone()),
                    deadline: self.cnf.solver.cb().deadline,
                    polls: Some(PollLimit {
                        used: std::cell::Cell::new(0),
                        max: usize::MAX,
                    }),
                    cancellation: self.engine.limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: self.budget.remaining_time(),
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        let mut validation_started = None;
        let original = std::mem::replace(&mut self.cnf, local);
        // This solver has free boundary values, not the branch's input universe.
        let formula_pins = std::mem::replace(&mut self.formula_pins, false);
        let result = (|| {
            let truth = self.cnf.var(self.budget)?;
            self.cnf.clause(vec![truth], self.budget)?;
            let a = encoding::encode_named(
                cone,
                &mut self.cnf,
                truth,
                None,
                self.budget,
                "local-uniqueness",
            )?;
            let b = encoding::encode_named(
                cone,
                &mut self.cnf,
                truth,
                Some(&a.vars),
                self.budget,
                "local-uniqueness",
            )?;
            let mut diff = Vec::new();
            for i in 0..cone.fixed.len() {
                self.budget.tick("completion local uniqueness")?;
                if cone.input[i] || a.vars[i] == b.vars[i] {
                    continue;
                }
                diff.push(self.cnf.and(&[a.vars[i], !b.vars[i]], self.budget)?);
                diff.push(self.cnf.and(&[!a.vars[i], b.vars[i]], self.budget)?);
            }
            self.cnf.clause(diff, self.budget)?;
            solving(self.cnf.solver.num_vars() as usize, self.cnf.clauses);
            if !self.raw_solve(&[])? {
                return Ok(true);
            }
            validation_started = Some(self.budget.used());
            checked_assignment(cone, &a, &self.cnf, self.budget)?;
            checked_assignment(cone, &b, &self.cnf, self.budget)?;
            Ok(false)
        })();
        let variables = self.cnf.solver.num_vars() as usize;
        let clauses = self.cnf.clauses;
        self.cnf = original;
        self.formula_pins = formula_pins;
        let validation_work = validation_started.map_or(0, |start| self.budget.used() - start);
        (result, variables, clauses, validation_work)
    }

    pub(super) fn usage(&self) -> QueryLimits {
        self.ledger.used()
    }
    #[cfg(test)]
    pub(super) fn solves(&self) -> usize {
        self.ledger.used().max_solves
    }

    pub(super) fn raw_solve(&mut self, pins: &[Lit]) -> Result<bool> {
        self.budget.tick("completion solve")?;
        self.cnf.solver.cb().check_time()?;
        self.ledger.admit(self.budget)?;
        let started = Instant::now();
        let remaining = self
            .engine
            .limits
            .run_deadline
            .map(|d| d.saturating_duration_since(started));
        let _solve_scope = self.engine.limits.progress.scope(
            "completion SAT solve",
            Some(crate::CheckingTarget::CompletionSolve {
                remaining_ms: remaining.map(|d| d.as_millis().min(u64::MAX as u128) as u64),
            }),
            true,
        );
        // Progress observers are synchronous. Do not enter the solver if output
        // or an observer consumed the remaining time after the first check.
        self.budget.check("completion solve")?;
        self.cnf.solver.cb().check_time()?;
        // Enforce the remaining allowance inside the call: batsat stops when a
        // count reaches its budget, so allow R more and stop on the (R + 1)th;
        // polls stop past `max`. A probe's work cap stops polls the same way, one
        // past the remaining work, so its stop is charged as work below.
        let room = self.ledger.remaining();
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let before_polls = self
            .cnf
            .solver
            .cb()
            .polls
            .as_ref()
            .map_or(0, |p| p.used.get());
        let poll_room = if self.engine.probe {
            room.polls.min(self.budget.remaining())
        } else {
            room.polls
        };
        if let Some(p) = &mut self.cnf.solver.cb_mut().polls {
            p.max = before_polls.saturating_add(poll_room);
        }
        self.cnf.solver.set_budgets(
            Some(conflicts.saturating_add(room.conflicts).saturating_add(1)),
            Some(
                propagations
                    .saturating_add(room.propagations)
                    .saturating_add(1),
            ),
        );
        let answer = self.cnf.solver.solve_limited(pins);
        let polls = self
            .cnf
            .solver
            .cb()
            .polls
            .as_ref()
            .map_or(0, |p| p.used.get())
            .saturating_sub(before_polls);
        if let Some(p) = &mut self.cnf.solver.cb_mut().polls {
            p.max = usize::MAX;
        }
        self.ledger.debit(&QueryLimits {
            max_solves: 1,
            max_solver_polls: polls,
            max_conflicts: self.cnf.solver.num_conflicts().saturating_sub(conflicts),
            max_propagations: self
                .cnf
                .solver
                .num_propagations()
                .saturating_sub(propagations),
        });
        let elapsed = started.elapsed();
        self.solve_time += elapsed;
        let overrun = self.engine.limits.run_deadline.map_or(Duration::ZERO, |d| {
            Instant::now().saturating_duration_since(d)
        });
        if self.solve_timings.len() < 64 {
            self.solve_timings.push(crate::CompletionSolveTiming {
                remaining_at_start: remaining,
                elapsed,
                overrun,
            });
        } else {
            self.omitted_solve_timings += 1;
        }

        // Precedence: cancellation and deadlines, then the allowance that
        // stopped the call, then the probe's work. A call that proved SAT or
        // UNSAT at the crossing checkpoint keeps its answer; the overshoot
        // refuses the next call.
        self.cnf.solver.cb().check_time()?;
        if answer == lbool::UNDEF {
            if let Some(error) = self.ledger.exhausted() {
                return Err(error);
            }
        }
        if self.engine.probe {
            self.budget
                .charge(polls, "completion unsplit probe solver work")?;
        }
        self.budget.check("completion solve")?;
        if answer == lbool::TRUE {
            if self.formula_pins {
                for pin in &self.engine.formula_pins {
                    let value = pin.certificate.evaluate(
                        |i| self.cnf.solver.value_lit(self.world.vars[i]) == lbool::TRUE,
                        self.budget,
                    )?;
                    if value != pin.value {
                        return Err(CheckError::Internal("branch formula replay disagrees"));
                    }
                }
            }
            Ok(true)
        } else if answer == lbool::FALSE {
            Ok(false)
        } else {
            Err(CheckError::Internal(
                "completion solver stopped without a limit",
            ))
        }
    }

    pub(super) fn models(
        &mut self,
        cone: &Cone,
        world_pins: &[Lit],
        hypothesis: Option<usize>,
        scope: ModelScope,
        accepted: Option<(&BTreeSet<GroundAtom>, &Model)>,
        existence_only: bool,
    ) -> Result<Interpretations> {
        let mut example = None;
        let phase = match scope {
            ModelScope::Classification => "completion classification",
            ModelScope::ClassificationWithoutHypothesis => "completion classification existence",
            ModelScope::Processing => "completion processing",
            ModelScope::WholeProgram => "completion meaning",
            ModelScope::Property => "completion property",
            ModelScope::Assumption => "completion assumption",
            ModelScope::InputDomain => "completion input domain",
        };
        let result: Result<Interpretations> = (|| {
            let gate = self.cnf.var(self.budget)?;
            self.cnf.gate = Some(gate);
            let e = encode(
                cone,
                &mut self.cnf,
                self.truth,
                Some(&self.world.vars),
                self.budget,
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
                    if !self.engine.decision(atom) {
                        continue;
                    }
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
            let values = checked_assignment(cone, &e, &self.cnf, self.budget)?;
            let first = self.engine.model(values, scope);
            if existence_only {
                return Ok(Interpretations::Unique(first));
            }
            example = Some(first.clone());
            // Exclude this projection onto original decision atoms, never helper
            // or encoding variables. All equations remain; world inputs are pinned.
            let mut different = Vec::new();
            for (i, atom) in cone.atoms.iter().enumerate() {
                self.budget.tick(phase)?;
                if self.engine.input_relations.contains(&atom.relation)
                    || !self.engine.decision(atom)
                {
                    continue;
                }
                if let Some(value) = first.value(atom) {
                    different.push(if value { !e.vars[i] } else { e.vars[i] });
                }
            }
            let second_gate = self.cnf.var(self.budget)?;
            self.cnf.gate = Some(second_gate);
            self.cnf.clause(different, self.budget)?;
            self.inactive.push(second_gate);
            pins.push(second_gate);
            if !self.solve(&pins)? {
                return Ok(Interpretations::Unique(first));
            }
            let values = checked_assignment(cone, &e, &self.cnf, self.budget)?;
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
pub(super) fn checked_assignment(
    cone: &Cone,
    e: &Encoding,
    cnf: &Cnf,
    b: &mut Budget<'_>,
) -> Result<Vec<bool>> {
    let mut values = vec![false; e.vars.len()];
    if let Some(index) = &e.validation {
        b.charge(index.read.len(), "completion model validation")?;
        for i in &index.read {
            values[*i] = cnf.solver.value_lit(e.vars[*i]) == lbool::TRUE;
        }
    } else {
        b.charge(e.vars.len(), "completion model validation")?;
        for (i, l) in e.vars.iter().enumerate() {
            values[i] = cnf.solver.value_lit(*l) == lbool::TRUE;
        }
    }
    validate_assignment(cone, &values, e.validation.as_ref(), b)?;
    Ok(values)
}

pub(super) fn validate_assignment(
    cone: &Cone,
    values: &[bool],
    index: Option<&encoding::Validation>,
    b: &mut Budget<'_>,
) -> Result<()> {
    let mut produced = vec![false; values.len()];
    for r in &cone.rules {
        b.charge(r.body.len() + 1, "completion model validation")?;
        produced[r.head] |= r.body.iter().all(|(a, pos)| values[*a] == *pos);
    }
    let heads: Box<dyn Iterator<Item = usize>> = if let Some(index) = index {
        Box::new(index.heads.iter().copied())
    } else {
        Box::new(0..values.len())
    };
    for i in heads {
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
    validate_retained(cone, values, b)?;
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
    Ok(())
}

pub(super) fn validate_retained(cone: &Cone, values: &[bool], b: &mut Budget<'_>) -> Result<()> {
    for eq in &cone.retained {
        b.charge(
            eq.bodies.iter().map(|body| body.len() + 1).sum(),
            "completion retained validation",
        )?;
        if values[eq.head]
            != eq
                .bodies
                .iter()
                .any(|body| body.iter().all(|(i, p)| values[*i] == *p))
        {
            return Err(CheckError::Internal(
                "forced definition violates original completion",
            ));
        }
    }
    Ok(())
}
