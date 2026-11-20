use super::*;
mod components;
mod uniqueness;
pub use uniqueness::UniquenessStats;
pub(super) mod cubes;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum MeaningMode {
    #[default]
    Full,
    Uniqueness,
    /// Existence in the selected obligations' upstream cone; uniqueness is optional.
    Cone,
    None,
}
impl MeaningMode {
    pub fn label(self) -> &'static str {
        match self {
            Self::Full => "full",
            Self::Uniqueness => "uniqueness",
            Self::None => "none",
            Self::Cone => "cone",
        }
    }
}
/// Invocation-local measurements. Cubes are distinct: each contains the new world
/// selected outside all previous cubes. Literal counts include neither selectors
/// nor program-query pins, unless explicitly named selector_literals.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CubeStats {
    pub cubes: usize,
    pub min_inputs: Option<usize>,
    pub max_inputs: usize,
    pub distinct_cube_literals: usize,
    /// Inputs in this counter's scope (whole-program for aggregate counters).
    pub support_size: usize,
    pub distinct_inputs: usize,
    pub emitted_exclusion_literals: usize,
    pub emitted_selector_literals: usize,
}
impl CubeStats {
    pub fn mean_inputs(&self) -> Option<f64> {
        (self.cubes != 0).then(|| self.distinct_cube_literals as f64 / self.cubes as f64)
    }
}

/// Aggregate counters retain whole-program supportSize. Scope counters report
/// only that cone's support; repeated upstream work remains visible in totals.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExistenceStats {
    pub total: CubeStats,
    pub components_total: usize,
    pub scopes: Vec<ExistenceScopeStats>,
    pub fallback: Option<&'static str>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExistenceScopeStats {
    /// Residual component ordinal in this prepared program; None is the fallback.
    pub component: Option<usize>,
    pub position: usize,
    pub state: &'static str,
    pub counters: CubeStats,
}
impl std::ops::Deref for ExistenceStats {
    type Target = CubeStats;
    fn deref(&self) -> &CubeStats {
        &self.total
    }
}
impl std::ops::DerefMut for ExistenceStats {
    fn deref_mut(&mut self) -> &mut CubeStats {
        &mut self.total
    }
}

#[derive(Debug)]
pub enum Existence {
    NotAnalysed,
    EveryWorld,
    NoMeaning(Observation),
    Inconclusive(Inconclusive),
}
#[derive(Debug)]
pub enum Uniqueness {
    NotAnalysed,
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
    pub mode: MeaningMode,
    pub split: Option<SplitStats>,
    pub existence_stats: Option<ExistenceStats>,
    pub uniqueness_stats: Option<UniquenessStats>,
    pub existence: Existence,
    pub uniqueness: Uniqueness,
}
impl Meaning {
    pub fn unique_everywhere(&self) -> bool {
        matches!(self.existence, Existence::EveryWorld)
            && matches!(self.uniqueness, Uniqueness::AtMostOne)
    }
}
/// Private to this engine's existence search. No ordinary query/cache key can
/// name this changing constraint set. A subsequent check starts a fresh selector.
struct WorldEnumeration {
    selector: Lit,
}
impl Engine {
    fn start_enumeration(&mut self, b: &mut Budget<'_>) -> Result<WorldEnumeration> {
        if let Some(e) = &self.append_failed {
            return Err(e.clone());
        }
        let selector = self.append_query(
            &QueryKey {
                mode: Mode::World,
                pins: vec![],
                exclude: vec![],
            },
            b,
        )?;
        Ok(WorldEnumeration { selector })
    }
    fn enumeration_world(
        &mut self,
        enumeration: &WorldEnumeration,
        b: &mut Budget<'_>,
    ) -> Result<Answer> {
        b.check("SAT existence")?;
        let timeout = self.cnf.solver.cb().timeout;
        self.cnf.solver.cb_mut().timeout = timeout.min(b.remaining_time());
        let result = self.query_with_selector(
            Mode::World,
            &Query::default(),
            Some(enumeration.selector),
            b,
        );
        self.cnf.solver.cb_mut().timeout = timeout;
        result
    }
    fn exclude_world_cube(
        &mut self,
        enumeration: &WorldEnumeration,
        cover: &BTreeSet<usize>,
        value: impl Fn(usize) -> bool,
        stats: &mut ExistenceStats,
        b: &mut Budget<'_>,
    ) -> Result<()> {
        if let Some(e) = &self.append_failed {
            return Err(e.clone());
        }
        let clause = cover
            .iter()
            .map(|i| {
                let lit = self.world_encoding.vars[*i];
                if value(*i) { !lit } else { lit }
            })
            .collect();
        self.cnf.gate = Some(enumeration.selector);
        let before_clauses = self.cnf.clauses;
        let before_literals = self.cnf.literals;
        let result = self.cnf.clause(clause, b);
        // Include charged emission even if the append subsequently exhausts or
        // is cancelled. A partially appended encoding is never reused.
        let selectors = self.cnf.clauses - before_clauses;
        stats.emitted_selector_literals += selectors;
        stats.emitted_exclusion_literals += self.cnf.literals - before_literals - selectors;
        if let Err(e) = &result {
            self.append_failed = Some(e.clone());
        }
        result
    }
}

impl Engine {
    /// Existence and uniqueness in this engine's prepared scope, without checking obligations.
    /// Callers must separately establish that permitted inputs exist; an empty
    /// context must not be published as an executable/checked success.
    pub fn meaning(&mut self, options: &CheckOptions) -> Result<Meaning> {
        self.meaning_with_deadline(options, None)
    }
    /// Split arms share an outer deadline while retaining separate work allowances.
    pub(super) fn meaning_with_deadline(
        &mut self,
        options: &CheckOptions,
        deadline: Option<&Budget<'_>>,
    ) -> Result<Meaning> {
        self.validate_meaning_scope(options.meaning)?;
        let mut meaning = Meaning {
            mode: options.meaning,
            split: None,
            existence: Existence::NotAnalysed,
            uniqueness: Uniqueness::NotAnalysed,
            existence_stats: None,
            uniqueness_stats: None,
        };
        if options.meaning == MeaningMode::None {
            return Ok(meaning);
        }
        // Local stratification proves only the requested phases. Deliberately
        // skipped phases remain explicit even when the theorem would be cheap.
        let mut limits = self.limits.clone();
        if let Some(deadline) = deadline {
            limits.timeout = limits.timeout.min(deadline.remaining_time());
        }
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
                if matches!(options.meaning, MeaningMode::Full | MeaningMode::Cone) {
                    meaning.existence = Existence::EveryWorld;
                }
                if options.meaning != MeaningMode::Cone {
                    meaning.uniqueness = Uniqueness::AtMostOne;
                }
                return Ok(meaning);
            }
            Err(e) => {
                let c = query_inconclusive(e)?;
                if matches!(options.meaning, MeaningMode::Full | MeaningMode::Cone) {
                    meaning.existence = Existence::Inconclusive(c);
                }
                if options.meaning != MeaningMode::Cone {
                    meaning.uniqueness = Uniqueness::Inconclusive(c);
                }
                return Ok(meaning);
            }
            Ok(false) => {}
        }
        if let Some(split) = self.split_meaning(options, &mut b)? {
            return Ok(split);
        }
        let mut unique_cones = BTreeSet::new();
        if matches!(options.meaning, MeaningMode::Full | MeaningMode::Cone) {
            let (existence, stats) = self.existence_using(options, &mut unique_cones, &mut b)?;
            meaning.existence = existence;
            meaning.existence_stats = Some(stats);
        }
        if options.meaning == MeaningMode::Cone {
            return Ok(meaning);
        }
        let (uniqueness, stats) =
            self.scoped_uniqueness(&unique_cones, deadline.map(|b| b.remaining_time()))?;
        meaning.uniqueness = uniqueness;
        meaning.uniqueness_stats = Some(stats);
        Ok(meaning)
    }
    #[cfg(test)]
    fn existence(&mut self, options: &CheckOptions) -> Result<(Existence, ExistenceStats)> {
        let limits = self.limits.clone();
        self.existence_using(options, &mut BTreeSet::new(), &mut Budget::new(&limits))
    }
    fn existence_using(
        &mut self,
        options: &CheckOptions,
        unique_cones: &mut BTreeSet<usize>,
        b: &mut Budget<'_>,
    ) -> Result<(Existence, ExistenceStats)> {
        let _progress = self.limits.progress.scope("SAT existence", None, true);
        let mut stats = ExistenceStats::default();
        self.limits.progress.sat_existence(&stats);
        let result: Result<Existence> = (|| {
            b.charge(self.cone.input.len(), "SAT existence support")?;
            stats.support_size = self.cone.input.iter().filter(|v| **v).count();
            self.decomposed_existence(options, &mut stats, unique_cones, b)
        })();
        match result {
            Ok(v) => Ok((v, stats)),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok((
                    Existence::Inconclusive(query_inconclusive(e.in_phase("SAT existence", None))?),
                    stats,
                ))
            }
        }
    }
    fn whole_uniqueness(&mut self, b: &mut Budget<'_>) -> Result<Uniqueness> {
        b.check("SAT uniqueness")?;
        self.stats = Stats::default();
        if let Some(e) = &self.append_failed {
            return Ok(Uniqueness::Inconclusive(query_inconclusive(e.clone())?));
        }
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let timeout = self.cnf.solver.cb().timeout;
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.timeout = b.remaining_time();
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result: Result<Uniqueness> = (|| {
            if self.pair_encoding.is_none() {
                let built: Result<(Lit, Encoding)> = (|| {
                    let gate = self.cnf.var(b)?;
                    self.cnf.gate = Some(gate);
                    let second = encode(
                        &self.cone,
                        &mut self.cnf,
                        self.truth,
                        Some(&self.program_encoding.vars),
                        b,
                    )?;
                    let mut differences = Vec::new();
                    for i in 0..self.cone.atoms.len() {
                        b.tick("SAT uniqueness encoding")?;
                        if self.cone.input[i] || self.cone.fixed[i].is_some() {
                            continue;
                        }
                        let a = self.program_encoding.vars[i];
                        let z = second.vars[i];
                        let left = self.cnf.and(&[a, !z], b)?;
                        let right = self.cnf.and(&[!a, z], b)?;
                        differences.extend([left, right]);
                    }
                    self.cnf.clause(differences, b)?;
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
                if !self.solve(&[self.active, gate], conflicts, propagations, b)? {
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
                    let unfounded = least_unfounded(&self.cone, &values, b)?;
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
                    if let Err(e) = refine(&self.cone, e, unfounded, &mut self.cnf, b) {
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
                    let observation = first.observation(b)?;
                    return Ok(Uniqueness::Multiple {
                        observation,
                        first,
                        second,
                    });
                }
            }
        })();
        self.cnf.solver.cb_mut().timeout = timeout;
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

#[cfg(test)]
mod tests;
