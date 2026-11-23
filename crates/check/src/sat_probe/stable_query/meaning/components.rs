use super::*;

/// A compact, dependency-closed original program, with its own completion and
/// refinement gate. U/W remain in the shared world encoding, never in this cone.
pub(super) struct Scope {
    pub(super) cone: Cone,
    pub(super) global: Vec<usize>,
    gate: Lit,
    encoding: Encoding,
}
pub(super) struct ScopedModels {
    pub(super) world: Model,
    pub(super) first: Vec<bool>,
    pub(super) second: Option<Vec<bool>>,
}
impl Engine {
    fn component_scope(&mut self, root: usize, b: &mut Budget<'_>) -> Result<Scope> {
        self.components_scope(vec![root], b)
    }
    pub(super) fn components_scope(
        &mut self,
        mut pending: Vec<usize>,
        b: &mut Budget<'_>,
    ) -> Result<Scope> {
        let mut reached = BTreeSet::new();
        let mut atoms = BTreeSet::new();
        let mut rules = BTreeSet::new();
        while let Some(i) = pending.pop() {
            b.tick("SAT component cone")?;
            if !reached.insert(i) {
                continue;
            }
            let c = &self.program.core.components[i];
            b.charge(
                c.atoms.len() + c.dependencies.len() + self.program.core.component_rules[i].len(),
                "SAT component cone",
            )?;
            atoms.extend(c.atoms.iter().map(|a| self.program.core.atom_index[a]));
            rules.extend(self.program.core.component_rules[i].iter().copied());
            pending.extend(c.dependencies.iter().map(|d| d.index));
        }
        let n = self.cone.atoms.len();
        let mut global: Vec<_> = atoms.into_iter().collect();
        let count = global.len();
        global.extend([n, n + 1]);
        b.charge(global.len(), "SAT component cone")?;
        let local: BTreeMap<_, _> = global.iter().enumerate().map(|(i, g)| (*g, i)).collect();
        let mut cone = Cone {
            atoms: global[..count]
                .iter()
                .map(|i| self.cone.atoms[*i].clone())
                .collect(),
            rules: Vec::new().into(),
            input: global.iter().map(|i| self.cone.input[*i]).collect(),
            fixed: global.iter().map(|i| self.cone.fixed[*i]).collect(),
            target: vec![false; global.len()].into(),
            duplicated: vec![false; global.len()].into(),
            groups: vec![].into(),
            source_rules: rules.len(),
        };
        for i in rules {
            let r = &self.cone.rules[i];
            b.charge(1 + r.body.len(), "SAT component cone")?;
            cone.rules.push(Rule {
                source: r.source,
                head: local[&r.head],
                body: r.body.iter().map(|(a, p)| (local[a], *p)).collect(),
            });
        }
        let built: Result<Scope> = (|| {
            let gate = self.cnf.var(b)?;
            self.cnf.gate = Some(gate);
            let inputs: Vec<_> = global
                .iter()
                .map(|i| self.world_encoding.vars[*i])
                .collect();
            let encoding = encode(&cone, &mut self.cnf, self.truth, Some(&inputs), b)?;
            Ok(Scope {
                cone,
                global,
                gate,
                encoding,
            })
        })();
        if let Err(ref e) = built {
            self.append_failed = Some(e.clone());
        }
        built
    }

    /// One capped query over W and the isolated cone. A second encoding asks
    /// whether this cone itself has two meanings, without downstream equations.
    fn scoped_query(
        &mut self,
        scope: &Scope,
        pins: &[Lit],
        pair: Option<(Lit, &Encoding)>,
        b: &mut Budget<'_>,
    ) -> Result<Option<ScopedModels>> {
        if let Some(e) = &self.append_failed {
            return Err(e.clone());
        }
        b.check("SAT component query")?;
        self.stats = Stats::default();
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let timeout = self.cnf.solver.cb().timeout;
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.timeout = timeout.min(b.remaining_time());
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result = (|| {
            let mut assumptions = vec![!self.active, scope.gate];
            assumptions.extend_from_slice(pins);
            if let Some((gate, _)) = pair {
                assumptions.push(gate);
            }
            loop {
                if !self.solve(&assumptions, conflicts, propagations, b)? {
                    return Ok(None);
                }
                let mut world = None;
                let mut first = None;
                let mut second = None;
                let mut refined = false;
                // W can itself contain positive recursion. Validate it too: its
                // completion alone could otherwise admit forbidden input worlds.
                let encodings = [
                    (None, &self.world_cone, &self.world_encoding),
                    (Some(scope.gate), &scope.cone, &scope.encoding),
                ];
                for (gate, cone, encoding) in encodings
                    .into_iter()
                    .chain(pair.map(|(g, e)| (Some(g), &scope.cone, e)))
                {
                    b.charge(encoding.vars.len(), "SAT component assignment")?;
                    let values: Vec<_> = encoding
                        .vars
                        .iter()
                        .map(|l| self.cnf.solver.value_lit(*l) == lbool::TRUE)
                        .collect();
                    let unfounded = least_unfounded(cone, &values, b)?;
                    if !unfounded.is_empty() {
                        b.room(
                            self.stats.refinements,
                            self.config.max_refinements,
                            "SAT component query",
                            "refinements",
                        )?;
                        self.cnf.gate = gate;
                        if let Err(e) = refine(cone, encoding, unfounded, &mut self.cnf, b) {
                            self.append_failed = Some(e.clone());
                            return Err(e);
                        }
                        self.stats.refinements += 1;
                        refined = true;
                        break;
                    }
                    if gate.is_none() {
                        world = Some(self.model(Mode::World, &values));
                    } else if gate == Some(scope.gate) {
                        first = Some(values);
                    } else {
                        second = Some(values);
                    }
                }
                if !refined {
                    return Ok(Some(ScopedModels {
                        world: world.unwrap(),
                        first: first.unwrap(),
                        second,
                    }));
                }
            }
        })();
        self.cnf.solver.cb_mut().timeout = timeout;
        result
    }

    fn scope_unique(&mut self, scope: &Scope, b: &mut Budget<'_>) -> Result<bool> {
        Ok(self.scope_pair(scope, b)?.is_none())
    }
    pub(super) fn scope_pair(
        &mut self,
        scope: &Scope,
        b: &mut Budget<'_>,
    ) -> Result<Option<ScopedModels>> {
        let built: Result<(Lit, Encoding)> = (|| {
            let gate = self.cnf.var(b)?;
            self.cnf.gate = Some(gate);
            let second = encode(
                &scope.cone,
                &mut self.cnf,
                self.truth,
                Some(&scope.encoding.vars),
                b,
            )?;
            let mut differences = Vec::new();
            for i in 0..scope.cone.atoms.len() {
                b.tick("SAT component uniqueness")?;
                if scope.cone.input[i] || scope.cone.fixed[i].is_some() {
                    continue;
                }
                let a = scope.encoding.vars[i];
                let z = second.vars[i];
                differences.push(self.cnf.and(&[a, !z], b)?);
                differences.push(self.cnf.and(&[!a, z], b)?);
            }
            self.cnf.clause(differences, b)?;
            Ok((gate, second))
        })();
        let (gate, second) = match built {
            Ok(v) => v,
            Err(e) => {
                self.append_failed = Some(e.clone());
                return Err(e);
            }
        };
        self.scoped_query(scope, &[], Some((gate, &second)), b)
    }

    pub(super) fn decomposed_existence(
        &mut self,
        options: &CheckOptions,
        stats: &mut ExistenceStats,
        unique_cones: &mut BTreeSet<usize>,
        b: &mut Budget<'_>,
    ) -> Result<Existence> {
        b.charge(
            self.program.core.components.len(),
            "SAT component eligibility",
        )?;
        stats.components_total = self
            .program
            .core
            .components
            .iter()
            .filter(|c| c.cycle.is_some())
            .count();
        let mut determined = vec![true; self.program.core.components.len()];
        let mut seen = BTreeSet::new();
        let mut worlds = 0;
        for i in 0..determined.len() {
            let c = &self.program.core.components[i];
            b.charge(1 + c.dependencies.len(), "SAT component eligibility")?;
            let upstream = c.dependencies.iter().all(|d| determined[d.index]);
            if c.cycle.is_none() {
                determined[i] = upstream;
                continue;
            }
            if !upstream {
                stats.fallback = Some("upstream cone is not uniquely determined");
                stats.scopes.push(ExistenceScopeStats {
                    component: None,
                    position: stats.scopes.len() + 1,
                    state: "searching",
                    counters: CubeStats {
                        support_size: stats.support_size,
                        ..Default::default()
                    },
                });
                self.limits.progress.sat_existence(stats);
                let result = self.search_existence(None, options, stats, &mut seen, &mut worlds, b);
                self.finish_existence_scope(stats, &result);
                return result;
            }
            stats.scopes.push(ExistenceScopeStats {
                component: Some(i),
                position: stats.scopes.len() + 1,
                state: "preparing",
                counters: CubeStats::default(),
            });
            self.limits.progress.sat_existence(stats);
            let result = (|| {
                let scope = self.component_scope(i, b)?;
                let last = stats.scopes.last_mut().unwrap();
                last.counters.support_size = scope.cone.input.iter().filter(|v| **v).count();
                last.state = "searching";
                self.limits.progress.sat_existence(stats);
                let outcome =
                    self.search_existence(Some(&scope), options, stats, &mut seen, &mut worlds, b)?;
                if matches!(outcome, Existence::EveryWorld) {
                    stats.scopes.last_mut().unwrap().state = "checking-eligibility";
                    self.limits.progress.sat_existence(stats);
                    determined[i] = self.scope_unique(&scope, b)?;
                    if determined[i] {
                        unique_cones.insert(i);
                    }
                }
                Ok(outcome)
            })();
            self.finish_existence_scope(stats, &result);
            if matches!(result, Ok(Existence::EveryWorld)) {
                stats.scopes.last_mut().unwrap().state = if determined[i] {
                    "determined"
                } else {
                    "existent-ambiguous"
                };
                self.limits.progress.sat_existence(stats);
            } else {
                return result;
            }
        }
        Ok(Existence::EveryWorld)
    }
    fn finish_existence_scope(&self, stats: &mut ExistenceStats, result: &Result<Existence>) {
        stats.scopes.last_mut().unwrap().state = match result {
            Ok(Existence::EveryWorld) => "every-world",
            Ok(Existence::NoMeaning(_)) => "no-meaning",
            _ => "inconclusive",
        };
        self.limits.progress.sat_existence(stats);
    }

    fn search_existence(
        &mut self,
        scope: Option<&Scope>,
        options: &CheckOptions,
        stats: &mut ExistenceStats,
        seen: &mut BTreeSet<usize>,
        worlds: &mut usize,
        b: &mut Budget<'_>,
    ) -> Result<Existence> {
        let enumeration = self.start_enumeration(b)?;
        let mut scope_seen = BTreeSet::new();
        loop {
            let world = match self.enumeration_world(&enumeration, b)? {
                Answer::NoModel => return Ok(Existence::EveryWorld),
                Answer::Inconclusive(c) => return Err(c.into()),
                Answer::Model(m) => m,
            };
            b.room(*worlds, options.max_worlds, "SAT existence", "worlds")?;
            *worlds += 1;
            let cover = if let Some(scope) = scope {
                // Only the cone inputs are needed for its model. The complete
                // observation remains available if this world has no extension.
                b.charge(scope.global.len(), "SAT component pins")?;
                let pins: Vec<_> = scope
                    .global
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| scope.cone.input[*i])
                    .map(|(_, g)| {
                        let lit = self.world_encoding.vars[*g];
                        if world.values[*g / 64] & (1u64 << (*g % 64)) != 0 {
                            lit
                        } else {
                            !lit
                        }
                    })
                    .collect();
                let Some(values) = self.scoped_query(scope, &pins, None, b)? else {
                    return Ok(Existence::NoMeaning(world.observation(b)?));
                };
                let local_cover = cubes::certified(&scope.cone, &values.first, b)?;
                b.charge(local_cover.len(), "SAT component cube")?;
                // Map only the certified input literals back to the shared world
                // encoding; derived local indices never escape this scope.
                let cover: BTreeSet<_> = local_cover.iter().map(|i| scope.global[*i]).collect();
                cover
            } else {
                let observation = world.observation(b)?;
                let pins = observation
                    .present
                    .iter()
                    .map(|a| (a.clone(), true))
                    .chain(observation.absent.iter().map(|a| (a.clone(), false)))
                    .collect();
                let m = match self.phase_query(
                    Mode::Program,
                    &Query {
                        pins,
                        exclude: vec![],
                    },
                    b,
                )? {
                    Answer::NoModel => return Ok(Existence::NoMeaning(observation)),
                    Answer::Inconclusive(c) => return Err(c.into()),
                    Answer::Model(m) => m,
                };
                let values = m.cone_values(&self.cone, b)?;
                cubes::certified(&self.cone, &values, b)?
            };
            b.charge(cover.len(), "SAT existence statistics")?;
            seen.extend(cover.iter().copied());
            scope_seen.extend(cover.iter().copied());
            for s in [
                &mut stats.total,
                &mut stats.scopes.last_mut().unwrap().counters,
            ] {
                s.cubes += 1;
                s.min_inputs = Some(s.min_inputs.map_or(cover.len(), |n| n.min(cover.len())));
                s.max_inputs = s.max_inputs.max(cover.len());
                s.distinct_cube_literals += cover.len();
            }
            stats.distinct_inputs = seen.len();
            stats.scopes.last_mut().unwrap().counters.distinct_inputs = scope_seen.len();
            let before = (
                stats.emitted_exclusion_literals,
                stats.emitted_selector_literals,
            );
            let appended = self.exclude_world_cube(
                &enumeration,
                &cover,
                |i| world.values[i / 64] & (1u64 << (i % 64)) != 0,
                stats,
                b,
            );
            let delta = (
                stats.emitted_exclusion_literals - before.0,
                stats.emitted_selector_literals - before.1,
            );
            let s = &mut stats.scopes.last_mut().unwrap().counters;
            s.emitted_exclusion_literals += delta.0;
            s.emitted_selector_literals += delta.1;
            self.limits.progress.sat_existence(stats);
            appended?;
        }
    }
}
