//! Verification-local input facts. No program equation may justify a pin.
use super::*;

#[derive(Debug, Clone, Default)]
pub struct PinStats {
    pub attempted: usize,
    pub proved: usize,
    pub unknown: usize,
    pub truncated: bool,
}

pub(super) fn inventory(
    p: &GroundProgram,
    c: &Cone,
    keys: &SemanticKeys,
    b: &mut Budget<'_>,
) -> Result<(Vec<GroundAtom>, Vec<Vec<GroundAtom>>)> {
    let mut ordered = BTreeMap::new();
    for a in &p.inputs {
        b.tick("SAT input ordering")?;
        // Bare query users need not supply diagnostic keys. Optional search is
        // skipped for unnamed inputs, rather than inventing an arena-based order.
        if let Ok(key) = AtomKey::from_atom(keys, a) {
            ordered.insert(key, a.clone());
        }
    }
    let mut groups = BTreeMap::new();
    for (kind, members) in &c.groups {
        b.charge(members.len() + 1, "SAT split groups")?;
        if *kind != Cardinality::ExactlyOne
            || members.len() < 2
            || members
                .iter()
                .any(|i| !c.input[*i] || c.fixed[*i].is_some())
        {
            continue;
        }
        let mut named = BTreeMap::new();
        for i in members {
            if let Ok(k) = AtomKey::from_atom(keys, &c.atoms[*i]) {
                named.insert(k, c.atoms[*i].clone());
            }
        }
        if named.len() != members.len() {
            continue;
        }
        groups.insert(
            named.keys().cloned().collect::<Vec<_>>(),
            named.into_values().collect(),
        );
    }
    Ok((
        ordered.into_values().collect(),
        groups.into_values().collect(),
    ))
}

impl Engine {
    pub fn pin_stats(&self) -> &PinStats {
        &self.pin_stats
    }
    /// Proved input literals, scoped to this engine's immutable W/context.
    pub fn input_pins(&self) -> &BTreeMap<GroundAtom, bool> {
        &self.input_pins
    }

    pub(super) fn discover_pins(&mut self, preparation: &mut Budget<'_>) -> Result<()> {
        let mut limits = self.limits.clone();
        limits.max_work = limits.max_work.min(self.config.max_pin_work);
        limits.timeout = limits.timeout.min(preparation.remaining_time());
        let mut b = Budget::tracked(&limits);
        let mut pins = BTreeMap::new();
        let result: Result<()> = (|| {
            if self.config.max_pin_candidates == 0 || self.ordered_inputs.is_empty() {
                return Ok(());
            }
            let _progress = limits.progress.scope("SAT input pins", None, true);
            let world = match self.phase_query(Mode::World, &Query::default(), &mut b)? {
                Answer::Model(m) => m,
                Answer::NoModel => return Ok(()), // Never use inconsistency to prove arbitrary pins.
                Answer::Inconclusive(_) => {
                    self.pin_stats.unknown += 1;
                    return Ok(());
                }
            };
            // Prioritize inputs reaching unresolved cycles, then the remaining inputs.
            let relevant = self.negative_input_support(&mut b)?;
            let mut candidates = self.ordered_inputs.clone();
            candidates.sort_by_key(|a| !relevant.contains(a)); // stable semantic-key ties
            self.pin_stats.truncated = candidates.len() > self.config.max_pin_candidates;
            for a in candidates.into_iter().take(self.config.max_pin_candidates) {
                b.tick("SAT input pins")?;
                let value = world.value(&a).unwrap();
                self.pin_stats.attempted += 1;
                match self.phase_query(
                    Mode::World,
                    &Query {
                        pins: vec![(a.clone(), !value)],
                        exclude: vec![],
                    },
                    &mut b,
                )? {
                    Answer::NoModel => {
                        pins.insert(a, value);
                        self.pin_stats.proved += 1;
                    }
                    Answer::Model(_) => (),
                    Answer::Inconclusive(_) => {
                        self.pin_stats.unknown += 1;
                        break;
                    }
                }
            }
            Ok(())
        })();
        if let Err(e) = result {
            b.failure(&e);
            query_inconclusive(e)?; // cancellation and invalid requests are not optional cutoffs
            self.pin_stats.unknown += 1;
        }
        let dependency = if self
            .preparation_receipts
            .get(&crate::QueryKey::AssumptionValidation)
            .is_some()
        {
            crate::QueryKey::AssumptionValidation
        } else {
            crate::QueryKey::SettledAtoms
        };
        b.record(
            &mut self.preparation_receipts,
            crate::QueryKey::SatInputPins,
            [dependency],
        )?;
        preparation.check("SAT input pins")?;
        // Poll caps belong to solves, not subsequent CNF construction. In
        // particular an optional interrupted solve must not poison preparation.
        let stop = self.cnf.solver.cb_mut();
        stop.polls = None;
        stop.start = Instant::now();
        stop.timeout = preparation.remaining_time();
        // A partial query append cannot be kept. All proven pins remain valid in
        // the unchanged W; discard the failed solver before publishing the engine.
        if self.append_failed.is_some() {
            self.reset_world(preparation)?;
        }
        if !pins.is_empty() {
            self.fold_pins(pins, preparation)?;
        }
        self.cache.clear();
        self.cache_bytes = 0;
        self.stats = Stats::default();
        Ok(())
    }

    pub(super) fn negative_input_support(
        &self,
        b: &mut Budget<'_>,
    ) -> Result<BTreeSet<GroundAtom>> {
        b.charge(self.program.core.components.len(), "SAT negative cone")?;
        let mut todo: Vec<_> = self
            .program
            .core
            .components
            .iter()
            .filter(|c| c.cycle.is_some())
            .map(|c| c.id.index)
            .collect();
        let mut visited = BTreeSet::new();
        let mut inputs = BTreeSet::new();
        while let Some(i) = todo.pop() {
            b.tick("SAT negative cone")?;
            if !visited.insert(i) {
                continue;
            }
            let c = &self.program.core.components[i];
            b.charge(c.atoms.len() + c.dependencies.len(), "SAT negative cone")?;
            inputs.extend(
                c.atoms
                    .iter()
                    .filter(|a| self.program.inputs.contains(*a))
                    .cloned(),
            );
            todo.extend(c.dependencies.iter().map(|d| d.index));
        }
        Ok(inputs)
    }
    pub(super) fn fold_pins(
        &mut self,
        pins: BTreeMap<GroundAtom, bool>,
        b: &mut Budget<'_>,
    ) -> Result<()> {
        let (program, values, origins, _) =
            self.program.settle_atoms_with_inputs(None, &pins, b)?;
        let previous = self.origins.as_deref().unwrap_or(&self.settled.origins);
        let origins = origins.iter().map(|id| previous[id.index]).collect();
        let mut rules = Vec::new();
        let n = self.cone.atoms.len();
        for r in &program.core.rules {
            b.charge(r.body.len() + 1, "SAT pinned rules")?;
            let resolve = |a: &GroundAtom| match program.fixed_value(a) {
                Some(true) => n,
                Some(false) => n + 1,
                None => program.core.atom_index.get(a).copied().unwrap_or(n + 1),
            };
            rules.push(Rule {
                ground: None,
                source: Some(r.source),
                head: program.core.atom_index[&r.head.atom],
                body: r
                    .body
                    .iter()
                    .map(|l| (resolve(&l.term.atom), l.polarity == Polarity::Positive))
                    .collect(),
            });
        }
        self.cone.rules = rules.into();
        self.cone.source_rules = self.cone.rules.len();
        self.pinned_values
            .extend(values.into_iter().map(|(a, v)| (a, v.value)));
        self.input_pins.extend(pins);
        self.origins = Some(origins);
        self.program = Arc::new(program);
        Ok(())
    }
    pub(super) fn encode_program(&mut self, b: &mut Budget<'_>) -> Result<()> {
        self.cnf.gate = Some(self.active);
        self.program_encoding = encode(
            &self.cone,
            &mut self.cnf,
            self.truth,
            Some(&self.world_encoding.vars),
            b,
        )?;
        Ok(())
    }
    pub(super) fn reset_world(&mut self, b: &mut Budget<'_>) -> Result<()> {
        self.cnf = Cnf {
            measurement: None,
            solver: Solver::new(
                Default::default(),
                Stop {
                    deadline: None,
                    polls: None,
                    cancellation: self.limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: b.remaining_time(),
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        self.truth = self.cnf.var(b)?;
        self.cnf.clause(vec![self.truth], b)?;
        self.active = self.cnf.var(b)?;
        self.world_encoding = encode(&self.world_cone, &mut self.cnf, self.truth, None, b)?;
        for (a, value) in &self.input_pins {
            let lit = self.world_encoding.vars[self.program.core.atom_index[a]];
            self.cnf.clause(vec![if *value { lit } else { !lit }], b)?;
        }
        self.append_failed = None;
        self.pair_encoding = None;
        self.cache.clear();
        self.cache_bytes = 0;
        Ok(())
    }
}
