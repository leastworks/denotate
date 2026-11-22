use super::*;

pub(super) struct Run<'a, 'b, 'l> {
    pub(super) engine: &'a Engine,
    pub(super) budget: &'b mut Budget<'l>,
    pub(super) cnf: Cnf,
    pub(super) truth: Lit,
    pub(super) world: Encoding,
    inactive: Vec<Lit>,
    pub(super) solves: usize,
    pub(super) solve_limit: usize,
    certified: bool,
    work_started: usize,
}

impl Drop for Run<'_, '_, '_> {
    fn drop(&mut self) {
        if let Some((_, stats)) = &mut self.cnf.measurement {
            stats.work = Some(self.budget.used().saturating_sub(self.work_started));
        }
    }
}

impl Engine {
    /// Certified W alone. No completion equations outside selected restrictions
    /// can suppress an otherwise permitted observation.
    pub fn worlds(&self, query: &WorldQuery) -> Result<WorldAnswer> {
        let result = self.worlds_using(query, &mut Budget::new(&self.limits))?;
        if matches!(result, WorldAnswer::NoWorld)
            && self
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
        let mut present_set = BTreeSet::new();
        let result = (|| {
            for a in present {
                budget.tick("completion observation")?;
                if !self.program.inputs.contains(&a) {
                    return Err(CheckError::InvalidObservation(a));
                }
                present_set.insert(a);
            }
            let mut solves = 0;
            let issues = self.assumptions_at(&present_set, budget, &mut solves)?;
            if !issues.is_empty() {
                return Ok(ObservationOutcome::UndeterminedAssumptions(issues));
            }
            let mut run = Run::new(self, budget)?;
            run.label("completion observation");
            run.solve_limit = self.config.max_solves.saturating_sub(solves);
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
        for a in &engine.assumptions {
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
        run.certified = true;
        Ok(run)
    }
    pub(super) fn universe(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        let work_started = budget.used();
        budget.check("completion query")?;
        let mut cnf = Cnf {
            measurement: engine.limits.completion_sizes.clone().map(|sink| {
                (
                    sink,
                    crate::CompletionSearchSize {
                        elapsed: Duration::ZERO,
                        work: None,
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
                    polls: Some(PollLimit {
                        used: std::cell::Cell::new(0),
                        max: engine.config.max_solver_polls,
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
        let world = encoding::encode_named(
            &engine.world,
            &mut cnf,
            truth,
            None,
            budget,
            "input-universe",
        )?;
        Ok(Self {
            engine,
            budget,
            cnf,
            truth,
            world,
            inactive: vec![],
            solves: 0,
            solve_limit: engine.config.max_solves,
            certified: false,
            work_started,
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
            for a in &self.engine.assumptions {
                if !a.recursive {
                    continue;
                }
                // A separate solver prevents downstream equations, H, other
                // restrictions and candidate exclusions from choosing A's truth.
                let mut check = Run::universe(self.engine, self.budget)?;
                check.label("completion assumption certification");
                check.solve_limit = self.solve_limit.saturating_sub(self.solves);
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
                self.solves += check.solves;
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
    fn raw_solve(&mut self, pins: &[Lit]) -> Result<bool> {
        self.budget.tick("completion solve")?;
        self.cnf.solver.cb().check()?;
        self.budget
            .room(self.solves, self.solve_limit, "completion solve", "solves")?;
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
