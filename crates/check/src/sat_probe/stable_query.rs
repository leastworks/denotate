//! Experimental stable queries for one immutable program and named verification.
//! No BDD conditions, admission, or cross-session cache reuse.
use super::*;
use denotate_ir::{Corpus, SemanticKeys, VerificationId};
use existence::{Encoding, encode, refine, world_cone};
use std::{collections::VecDeque, sync::Arc};
mod attribution;
mod build;
mod checking;
mod meaning;
mod obligations;
mod oracle;
pub use checking::*;
pub use meaning::{
    CubeStats, Existence, ExistenceScopeStats, ExistenceStats, Meaning, MeaningMode, Uniqueness,
};
pub use oracle::*;

#[derive(Debug, Clone)]
pub struct QueryLimits {
    pub max_refinements: usize,
    pub max_solves: usize,
    /// Cooperative interrupt cap; batsat does not expose its internal budget setters.
    pub max_solver_polls: usize,
    /// Checked after each solve before accepting an answer. These can overshoot
    /// during one call; solver polls, cancellation and deadline interrupt the call.
    pub max_conflicts: u64,
    pub max_propagations: u64,
    pub cache_entries: usize,
    pub cache_bytes: usize,
}
impl Default for QueryLimits {
    fn default() -> Self {
        Self {
            max_refinements: 64,
            max_solves: 128,
            max_solver_polls: 100_000,
            max_conflicts: 100_000,
            max_propagations: 1_000_000,
            cache_entries: 32,
            cache_bytes: 8 * 1024 * 1024,
        }
    }
}
/// A conjunction of pins, minus a union of cubes. An empty exclusion cube excludes
/// everything. Input pins can describe a partial or complete observation. Program
/// queries may also pin derived atoms. No query changes the selected assumptions.
#[derive(Debug, Clone, Default)]
pub struct Query {
    pub pins: Vec<(GroundAtom, bool)>,
    pub exclude: Vec<Vec<(GroundAtom, bool)>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Mode {
    World,
    Program,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct QueryKey {
    mode: Mode,
    pins: Vec<i32>,
    exclude: Vec<Vec<i32>>,
}
#[derive(Debug, Clone)]
pub struct Model {
    program: Arc<GroundProgram>,
    input_relations: Arc<BTreeSet<RelationId>>,
    values: Arc<[u64]>,
    mode: Mode,
}
impl Model {
    /// None means invalid atom, or an unreported derived value in world mode.
    pub fn value(&self, atom: &GroundAtom) -> Option<bool> {
        if self.mode == Mode::World && !self.input_relations.contains(&atom.relation) {
            return None;
        }
        let resolved = resolve(&self.program, atom).ok()?;
        Some(match resolved {
            Resolved::Fixed(v) => v,
            Resolved::Atom(i) => self.values[i / 64] & (1u64 << (i % 64)) != 0,
        })
    }
    /// Differing residual values in two full-program interpretations of this prepared program.
    /// Fixed atoms cannot differ; scan residual bitvectors without domain lookups.
    pub fn differences<'a>(
        &'a self,
        other: &'a Self,
    ) -> Option<impl Iterator<Item = (&'a GroundAtom, bool, bool)> + 'a> {
        if self.mode != Mode::Program
            || other.mode != Mode::Program
            || !Arc::ptr_eq(&self.program, &other.program)
        {
            return None;
        }
        Some(
            self.program
                .core
                .atoms
                .iter()
                .enumerate()
                .filter_map(move |(i, a)| {
                    let x = self.values[i / 64] & (1u64 << (i % 64)) != 0;
                    let y = other.values[i / 64] & (1u64 << (i % 64)) != 0;
                    (x != y).then_some((a, x, y))
                }),
        )
    }
    pub fn true_inputs(&self) -> impl Iterator<Item = &GroundAtom> {
        self.program
            .inputs
            .iter()
            .filter(|a| self.value(a) == Some(true))
    }
}
#[derive(Debug, Clone)]
pub enum Answer {
    Model(Model),
    /// No stable model satisfies this query. This is not a totality/uniqueness verdict.
    NoModel,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub solves: usize,
    pub refinements: usize,
    pub conflicts: u64,
    pub propagations: u64,
    pub cache_hit: bool,
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
}
struct Cached {
    key: QueryKey,
    answer: Answer,
    bytes: usize,
}
/// All learnt clauses and cached answers belong to this immutable verification.
/// A different selection, program, or domain requires a new engine.
pub struct Engine {
    program: Arc<GroundProgram>,
    input_relations: Arc<BTreeSet<RelationId>>,
    cone: Cone,
    world_cone: Cone,
    cnf: Cnf,
    program_encoding: Encoding,
    pair_encoding: Option<(Lit, Encoding)>,
    verification: VerificationId,
    selection: Vec<(denotate_ir::ObligationId, Cardinality, RelationId)>,
    notices: BTreeSet<denotate_ir::NoticeId>,
    columns: BTreeMap<denotate_ir::ObligationId, Vec<usize>>,
    residual_relations: BTreeSet<RelationId>,
    world_encoding: Encoding,
    active: Lit,
    truth: Lit,
    limits: Limits,
    config: QueryLimits,
    cache: VecDeque<Cached>,
    cache_bytes: usize,
    stats: Stats,
    /// Partial clause emission is not reusable. Solve/refinement cutoffs alone
    /// leave a valid engine; construction/append exhaustion requires rebuilding.
    append_failed: Option<CheckError>,
}
#[derive(Clone, Copy)]
enum Resolved {
    Atom(usize),
    Fixed(bool),
}
fn resolve(p: &GroundProgram, a: &GroundAtom) -> Result<Resolved> {
    let Some(signature) = p.signatures.get(&a.relation) else {
        return Err(CheckError::UnknownAtom(a.clone()));
    };
    if signature.len() != a.arguments.len()
        || signature
            .iter()
            .zip(&a.arguments)
            .any(|(s, c)| !p.domains[s].contains(c))
    {
        return Err(CheckError::UnknownAtom(a.clone()));
    }
    Ok(if let Some(value) = p.fixed_value(a) {
        Resolved::Fixed(value)
    } else if let Some(i) = p.core.atom_index.get(a) {
        Resolved::Atom(*i)
    } else {
        Resolved::Fixed(false)
    })
}
// Query deadlines are an explicit unknown, like deterministic resource caps.
// Keep the shared checker's deadline/error policy unchanged.
fn query_inconclusive(error: CheckError) -> Result<Inconclusive> {
    match error {
        CheckError::Deadline { phase, details } => Ok(Inconclusive {
            phase,
            resource: "deadline",
            details,
        }),
        error => Inconclusive::from_error(error),
    }
}
impl Engine {
    pub fn prepare<'a>(
        corpus: &'a Corpus,
        domains: &Domains,
        keys: &'a SemanticKeys,
        verification: VerificationId,
        limits: &Limits,
        config: QueryLimits,
    ) -> Result<Self> {
        let program = Arc::new(build::prepare(corpus, domains, keys, verification, limits)?);
        let mut b = Budget::new(limits);
        let cone = build::cone(&program, corpus, verification, &mut b)?;
        let world_cone = world_cone(&cone, false, &mut b)?;
        let mut cnf = Cnf {
            solver: Solver::new(
                Default::default(),
                Stop {
                    polls: None,
                    cancellation: limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: limits.timeout,
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        let truth = cnf.var(&mut b)?;
        cnf.clause(vec![truth], &mut b)?;
        let active = cnf.var(&mut b)?;
        let world_encoding = encode(&world_cone, &mut cnf, truth, None, &mut b)?;
        cnf.gate = Some(active);
        let program_encoding = encode(&cone, &mut cnf, truth, Some(&world_encoding.vars), &mut b)?;
        b.check("SAT stable preparation")?;
        let input_relations = Arc::new(
            corpus
                .relations()
                .filter(|r| r.role == denotate_ir::RelationRole::Input)
                .map(|r| r.id)
                .collect(),
        );
        let declaration = corpus.verification(verification).unwrap();
        let selection = declaration
            .obligations
            .iter()
            .map(|id| {
                let r = &corpus.obligation(*id).unwrap().requirement;
                (*id, r.kind(), r.relation())
            })
            .collect();
        b.charge(program.core.atoms.len(), "SAT relation inventory")?;
        let residual_relations = program.core.atoms.iter().map(|a| a.relation).collect();
        let notices = declaration.notices.iter().copied().collect();
        let columns = declaration
            .obligations
            .iter()
            .map(|id| {
                (
                    *id,
                    corpus
                        .obligation(*id)
                        .unwrap()
                        .requirement
                        .group_by()
                        .to_vec(),
                )
            })
            .collect();
        Ok(Self {
            verification,
            columns,
            residual_relations,
            selection,
            notices,
            pair_encoding: None,
            program,
            input_relations,
            cone,
            world_cone,
            cnf,
            program_encoding,
            world_encoding,
            active,
            truth,
            limits: limits.clone(),
            config,
            cache: VecDeque::new(),
            cache_bytes: 0,
            stats: Stats::default(),
            append_failed: None,
        })
    }
    pub fn stats(&self) -> &Stats {
        &self.stats
    }
    pub fn models(&mut self, query: &Query) -> Result<Answer> {
        self.query(Mode::Program, query)
    }
    /// Only input pins and exclusions are accepted. Checked program equations and
    /// refinements cannot suppress a permitted world that has no program meaning.
    pub fn worlds(&mut self, query: &Query) -> Result<Answer> {
        self.query(Mode::World, query)
    }
    fn key(&self, mode: Mode, query: &Query, b: &mut Budget<'_>) -> Result<QueryKey> {
        // Extra signed token n+1 represents fixed truth. It cannot collide with a
        // residual atom. Query pins/exclusions are canonicalized, never projected.
        let token = |a: &GroundAtom, v: bool, b: &mut Budget<'_>| -> Result<i32> {
            b.charge(a.arguments.len() + 1, "SAT query key")?;
            if mode == Mode::World && !self.input_relations.contains(&a.relation) {
                return Err(CheckError::InvalidRequest(
                    "world queries accept input atoms only",
                ));
            }
            let l = match resolve(&self.program, a)? {
                Resolved::Fixed(x) => {
                    if x {
                        (self.cone.atoms.len() + 1) as i32
                    } else {
                        -((self.cone.atoms.len() + 1) as i32)
                    }
                }
                Resolved::Atom(i) => (i + 1) as i32,
            };
            Ok(if v { l } else { -l })
        };
        let mut pins = query
            .pins
            .iter()
            .map(|(a, v)| token(a, *v, b))
            .collect::<Result<Vec<_>>>()?;
        pins.sort_unstable();
        pins.dedup();
        let mut exclude = Vec::new();
        for cube in &query.exclude {
            let mut lits = cube
                .iter()
                .map(|(a, v)| token(a, *v, b))
                .collect::<Result<Vec<_>>>()?;
            lits.sort_unstable();
            lits.dedup();
            exclude.push(lits);
        }
        exclude.sort();
        exclude.dedup();
        Ok(QueryKey {
            mode,
            pins,
            exclude,
        })
    }
    fn query(&mut self, mode: Mode, query: &Query) -> Result<Answer> {
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        // Keep a named owner for the budget's borrowed limits.
        self.query_using(mode, query, &mut b)
    }
    fn query_using(&mut self, mode: Mode, query: &Query, b: &mut Budget<'_>) -> Result<Answer> {
        self.query_with_selector(mode, query, None, b)
    }
    // An enumeration selector has mutable exclusions. Its answers must never
    // consult or populate the immutable ordinary-query cache.
    fn query_with_selector(
        &mut self,
        mode: Mode,
        query: &Query,
        selector: Option<Lit>,
        b: &mut Budget<'_>,
    ) -> Result<Answer> {
        self.limits.cancellation.check()?;
        self.stats = Stats::default();
        if let Some(error) = &self.append_failed {
            return Ok(Answer::Inconclusive(query_inconclusive(error.clone())?));
        }
        let start_conflicts = self.cnf.solver.num_conflicts();
        let start_propagations = self.cnf.solver.num_propagations();
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result: Result<Answer> = (|| {
            let key = if selector.is_none() {
                Some(self.key(mode, query, b)?)
            } else {
                None
            };
            if let Some(key) = &key {
                if let Some(cached) = self.cache.iter().find(|entry| &entry.key == key) {
                    b.charge(
                        key.pins.len() + key.exclude.iter().map(Vec::len).sum::<usize>() + 1,
                        "SAT cache lookup",
                    )?;
                    self.stats.cache_hit = true;
                    return Ok(cached.answer.clone());
                }
            }
            let gate = match selector {
                Some(gate) => gate,
                None => self.append_query(key.as_ref().unwrap(), b)?,
            };
            let pins = [
                if mode == Mode::Program {
                    self.active
                } else {
                    !self.active
                },
                gate,
            ];
            let answer = self.search(mode, &pins, start_conflicts, start_propagations, b)?;
            if let Some(key) = key {
                self.remember(key, &answer, b)?;
            }
            Ok(answer)
        })();
        self.stats.variables = self.cnf.solver.num_vars() as usize;
        self.stats.clauses = self.cnf.clauses;
        self.stats.literals = self.cnf.literals;
        self.stats.conflicts = self.cnf.solver.num_conflicts() - start_conflicts;
        self.stats.propagations = self.cnf.solver.num_propagations() - start_propagations;
        match result {
            Ok(v) => Ok(v),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok(Answer::Inconclusive(query_inconclusive(
                    e.in_phase("SAT stable query", None),
                )?))
            }
        }
    }
    // Pins and exclusions share one isolated lifetime, including when the oracle
    // appends an expression mismatch under the same selector.
    fn append_query(&mut self, key: &QueryKey, b: &mut Budget<'_>) -> Result<Lit> {
        let e = if key.mode == Mode::Program {
            &self.program_encoding
        } else {
            &self.world_encoding
        };
        let map = |l: i32| {
            let i = l.unsigned_abs() as usize - 1;
            let value = if i == self.cone.atoms.len() {
                self.truth
            } else {
                e.vars[i]
            };
            if l > 0 { value } else { !value }
        };
        let appended: Result<Lit> = (|| {
            let gate = self.cnf.var(b)?;
            self.cnf.gate = Some(gate);
            for l in &key.pins {
                self.cnf.clause(vec![map(*l)], b)?;
            }
            for cube in &key.exclude {
                self.cnf
                    .clause(cube.iter().map(|l| !map(*l)).collect(), b)?;
            }
            Ok(gate)
        })();
        if let Err(ref e) = appended {
            self.append_failed = Some(e.clone());
        }
        appended
    }
    fn search(
        &mut self,
        mode: Mode,
        pins: &[Lit],
        conflicts: u64,
        propagations: u64,
        b: &mut Budget<'_>,
    ) -> Result<Answer> {
        loop {
            if !self.solve(pins, conflicts, propagations, b)? {
                return Ok(Answer::NoModel);
            }
            let c = if mode == Mode::Program {
                &self.cone
            } else {
                &self.world_cone
            };
            let e = if mode == Mode::Program {
                &self.program_encoding
            } else {
                &self.world_encoding
            };
            b.charge(e.vars.len(), "SAT stable assignment")?;
            let values = e
                .vars
                .iter()
                .map(|l| self.cnf.solver.value_lit(*l) == lbool::TRUE)
                .collect::<Vec<_>>();
            let unfounded = least_unfounded(c, &values, b)?;
            if unfounded.is_empty() {
                return Ok(Answer::Model(self.model(mode, &values)));
            }
            b.room(
                self.stats.refinements,
                self.config.max_refinements,
                "SAT stable query",
                "refinements",
            )?;
            // Program lemmas are shared among program queries only. World lemmas
            // are valid in the assumption-only base and may be shared with both.
            self.cnf.gate = if mode == Mode::Program {
                Some(self.active)
            } else {
                None
            };
            if let Err(error) = refine(c, e, unfounded, &mut self.cnf, b) {
                self.append_failed = Some(error.clone());
                return Err(error);
            }
            self.stats.refinements += 1;
        }
    }
    fn solve(
        &mut self,
        pins: &[Lit],
        conflicts: u64,
        propagations: u64,
        b: &mut Budget<'_>,
    ) -> Result<bool> {
        b.tick("SAT stable query")?;
        self.cnf.solver.cb().check()?;
        b.room(
            self.stats.solves,
            self.config.max_solves,
            "SAT stable query",
            "solves",
        )?;
        self.stats.solves += 1;
        let answer = self.cnf.solver.solve_limited(pins);
        self.cnf.solver.cb().check()?;
        for (used, limit, resource) in [
            (
                self.cnf.solver.num_conflicts() - conflicts,
                self.config.max_conflicts,
                "conflicts",
            ),
            (
                self.cnf.solver.num_propagations() - propagations,
                self.config.max_propagations,
                "propagations",
            ),
        ] {
            if used > limit {
                return Err(CheckError::limit(
                    "SAT stable query",
                    resource,
                    limit.try_into().unwrap_or(usize::MAX),
                    Some(used.try_into().unwrap_or(usize::MAX)),
                ));
            }
        }
        if answer == lbool::FALSE {
            return Ok(false);
        }
        if answer != lbool::TRUE {
            return Err(CheckError::Internal(
                "SAT stopped without an exhaustion reason",
            ));
        }
        Ok(true)
    }
    fn model(&self, mode: Mode, values: &[bool]) -> Model {
        let mut bits = vec![0; self.cone.atoms.len().div_ceil(64)];
        for (i, v) in values.iter().take(self.cone.atoms.len()).enumerate() {
            if *v {
                bits[i / 64] |= 1u64 << (i % 64);
            }
        }
        Model {
            program: self.program.clone(),
            input_relations: self.input_relations.clone(),
            values: bits.into(),
            mode,
        }
    }
    fn remember(&mut self, key: QueryKey, answer: &Answer, b: &mut Budget<'_>) -> Result<()> {
        if self.config.cache_entries == 0 {
            return Ok(());
        }
        let bytes = std::mem::size_of::<Cached>()
            + key.pins.capacity() * 4
            + key.exclude.capacity() * std::mem::size_of::<Vec<i32>>()
            + key.exclude.iter().map(|x| x.capacity() * 4).sum::<usize>()
            + match answer {
                Answer::Model(m) => m.values.len() * 8,
                _ => 0,
            };
        if bytes > self.config.cache_bytes {
            return Ok(());
        }
        if let Err(e) = b.tick("SAT query cache") {
            return if matches!(e, CheckError::Cancelled) {
                Err(e)
            } else {
                Ok(())
            };
        }
        while self.cache.len() >= self.config.cache_entries
            || self.cache_bytes.saturating_add(bytes) > self.config.cache_bytes
        {
            self.cache_bytes -= self.cache.pop_front().unwrap().bytes;
        }
        self.cache_bytes += bytes;
        self.cache.push_back(Cached {
            key,
            answer: answer.clone(),
            bytes,
        });
        Ok(())
    }
}
#[cfg(test)]
mod tests;
