//! Bounded caches owned by ONE immutable CNF and W/H context. In shadow mode no
//! hit supplies an answer: callers solve and compare every claimed hit. Forcing
//! may enforce MODEL hits only (`FixedQueries::enforcing`): a wrong SAT claim can
//! only keep an atom unforced, never install a constant, and a deterministic
//! sample of claimed hits is re-solved as a tripwire. Core hits stay advisory.
use super::*;
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub queries: usize,
    pub model_hits: usize,
    pub core_hits: usize,
    pub mismatches: usize,
    pub checked_hits: usize,
    pub models: usize,
    pub cores: usize,
    pub skipped_models: usize,
    pub skipped_cores: usize,
    /// Model hits answered without a solve (enforcing mode).
    pub enforced_hits: usize,
    /// Model hits re-solved as the tripwire sample (enforcing mode).
    pub sampled_hits: usize,
}
#[derive(Clone, Copy)]
pub(super) struct Caps {
    pub model_bytes: usize,
    pub core_bytes: usize,
    pub models: usize,
    pub cores: usize,
}
impl Default for Caps {
    fn default() -> Self {
        Self {
            model_bytes: 8 << 20,
            core_bytes: 8 << 20,
            models: 4096,
            cores: 16384,
        }
    }
}
struct Core {
    literals: Box<[usize]>,
}
#[derive(Clone, Copy)]
struct Watch {
    id: usize,
    signature: u64,
}

pub(super) struct Cache {
    variables: usize,
    caps: Caps,
    // One bitvector per variable, in blocks of 64 models. A block holds one
    // word for every variable. Allocation grows only when a model is inserted.
    columns: Vec<u64>,
    cores: Vec<Core>,
    watches: HashMap<usize, Vec<Watch>>,
    stamps: Vec<u32>,
    epoch: u32,
    core_bytes: usize,
    empty_core: bool,
    pub stats: Stats,
}
fn signature(literals: &[usize]) -> u64 {
    literals.iter().fold(0, |mask, i| {
        let hash = (*i as u64).wrapping_mul(0x9e3779b97f4a7c15);
        mask | (1 << (hash >> 58))
    })
}
impl Cache {
    pub fn new(variables: usize, caps: Caps, b: &mut Budget<'_>) -> Result<Self> {
        let stamp_bytes = variables.saturating_mul(2).saturating_mul(4);
        let stamps = if stamp_bytes <= caps.core_bytes {
            b.charge(variables * 2, "completion shadow cache allocation")?;
            vec![0; variables * 2]
        } else {
            vec![]
        };
        Ok(Self {
            variables,
            caps,
            columns: vec![],
            cores: vec![],
            watches: HashMap::new(),
            core_bytes: stamps.len() * 4,
            stamps,
            epoch: 0,
            empty_core: false,
            stats: Stats::default(),
        })
    }
    fn core_hit(&mut self, assumptions: &[usize], b: &mut Budget<'_>) -> Result<bool> {
        if self.empty_core {
            return Ok(true);
        }
        if self.stamps.is_empty() {
            return Ok(false);
        }
        if self.epoch == u32::MAX {
            b.charge(self.stamps.len(), "completion shadow core stamps")?;
            self.stamps.fill(0);
            self.epoch = 0;
        }
        self.epoch += 1;
        b.charge(assumptions.len(), "completion shadow core lookup")?;
        for a in assumptions {
            self.stamps[*a] = self.epoch;
        }
        let query_signature = signature(assumptions);
        for a in assumptions {
            if let Some(bucket) = self.watches.get(a) {
                for watch in bucket {
                    b.tick("completion shadow core lookup")?;
                    if watch.signature & !query_signature != 0 {
                        continue;
                    }
                    let literals = &self.cores[watch.id].literals;
                    b.charge(literals.len(), "completion shadow core subset")?;
                    if literals.iter().all(|l| self.stamps[*l] == self.epoch) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }
    pub fn lookup(
        &mut self,
        assumptions: &[Lit],
        removable: bool,
        b: &mut Budget<'_>,
    ) -> Result<Option<bool>> {
        self.stats.queries += 1;
        let ids: Vec<_> = assumptions.iter().map(|l| l.idx() as usize).collect();
        b.charge(ids.len(), "completion shadow lookup")?;
        if ids.iter().any(|i| *i >= self.variables * 2) {
            return Err(CheckError::Internal(
                "cache queried with a different encoding",
            ));
        }
        if !removable && self.stats.models > 0 {
            for block in 0..self.stats.models.div_ceil(64) {
                let count = (self.stats.models - block * 64).min(64);
                let mut matches = if count == 64 {
                    u64::MAX
                } else {
                    (1u64 << count) - 1
                };
                for l in assumptions {
                    b.tick("completion shadow model lookup")?;
                    let bits = self.columns[block * self.variables + l.var().idx() as usize];
                    matches &= if l.sign() { bits } else { !bits };
                    if matches == 0 {
                        break;
                    }
                }
                if matches != 0 {
                    self.stats.model_hits += 1;
                    return Ok(Some(true));
                }
            }
        }
        if self.core_hit(&ids, b)? {
            self.stats.core_hits += 1;
            Ok(Some(false))
        } else {
            Ok(None)
        }
    }
    /// Compare only conclusive solver answers. Never replace one with the claim.
    pub fn compare(&mut self, claimed: Option<bool>, actual: bool) {
        self.stats.checked_hits += usize::from(claimed.is_some());
        self.stats.mismatches += usize::from(claimed.is_some_and(|v| v != actual));
    }
    pub fn model(&mut self, model: &[lbool], b: &mut Budget<'_>) -> Result<()> {
        let next = self.stats.models;
        let blocks = (next + 1).div_ceil(64);
        if next >= self.caps.models
            || self.variables.saturating_mul(blocks).saturating_mul(8) > self.caps.model_bytes
        {
            self.stats.skipped_models += 1;
            return Ok(());
        }
        b.charge(self.variables * 2, "completion shadow model insertion")?;
        if model.len() != self.variables
            || model
                .iter()
                .any(|v| *v != lbool::TRUE && *v != lbool::FALSE)
        {
            self.stats.skipped_models += 1;
            return Ok(());
        }
        let words = self.variables * blocks;
        if words > self.columns.capacity() {
            self.columns.reserve_exact(words - self.columns.len());
        }
        self.columns.resize(words, 0);
        let bit = 1u64 << (next % 64);
        let start = (next / 64) * self.variables;
        for (i, v) in model.iter().enumerate() {
            if *v == lbool::TRUE {
                self.columns[start + i] |= bit;
            } else {
                self.columns[start + i] &= !bit;
            }
        }
        self.stats.models += 1;
        Ok(())
    }
    /// batsat's conflict clause contains the NEGATIONS of failed assumptions.
    /// Store the assumptions themselves, and validate that polarity explicitly.
    /// With removable clauses, conservatively decline core writes. Selector-
    /// dependent cores could be supported later with a separate lifetime contract.
    pub fn core(
        &mut self,
        conflict: &[Lit],
        assumptions: &[Lit],
        removable: bool,
        b: &mut Budget<'_>,
    ) -> Result<()> {
        if removable {
            self.stats.skipped_cores += 1;
            return Ok(());
        }
        b.charge(
            conflict.len() + assumptions.len(),
            "completion shadow core insertion",
        )?;
        let mut literals: Vec<_> = conflict.iter().map(|l| (!*l).idx() as usize).collect();
        literals.sort_unstable();
        literals.dedup();
        let query: BTreeSet<_> = assumptions.iter().map(|l| l.idx() as usize).collect();
        if literals.iter().any(|l| !query.contains(l)) {
            return Err(CheckError::Internal(
                "solver conflict is not negated assumptions",
            ));
        }
        if self.core_hit(&literals, b)? {
            return Ok(());
        }
        let bytes = literals
            .len()
            .saturating_mul(std::mem::size_of::<usize>())
            .saturating_add(128);
        if self.stats.cores >= self.caps.cores
            || self.core_bytes.saturating_add(bytes) > self.caps.core_bytes
            || (self.stamps.is_empty() && !literals.is_empty())
        {
            self.stats.skipped_cores += 1;
            return Ok(());
        }
        if literals.is_empty() {
            self.empty_core = true;
        } else {
            let watch = *literals
                .iter()
                .min_by_key(|l| (self.watches.get(l).map_or(0, Vec::len), **l))
                .unwrap();
            self.watches.entry(watch).or_default().push(Watch {
                id: self.cores.len(),
                signature: signature(&literals),
            });
        }
        self.cores.push(Core {
            literals: literals.into_boxed_slice(),
        });
        self.core_bytes += bytes;
        self.stats.cores += 1;
        Ok(())
    }
}

/// An exclusive borrow of the proof solver freezes its encoding for the whole
/// query family. A different view/context gets another owner, not another key in
/// a global cache. Only assumptions vary; learned clauses remain solver-private.
pub(super) struct FixedQueries<'r, 'a, 'b, 'l> {
    run: &'r mut queries::Run<'a, 'b, 'l>,
    cache: Cache,
    encoding: (usize, usize, usize),
    enforce_models: bool,
    claimed_models: usize,
}
/// Every `MODEL_HIT_SAMPLE`th claimed model hit, starting with the first, is
/// re-solved in enforcing mode.
pub(super) const MODEL_HIT_SAMPLE: usize = 100;
impl<'r, 'a, 'b, 'l> FixedQueries<'r, 'a, 'b, 'l> {
    pub fn new(run: &'r mut queries::Run<'a, 'b, 'l>) -> Result<Self> {
        Self::with_mode(run, false)
    }
    /// Boolean answers only: an enforced hit does not update the solver's current
    /// model, so a caller needing a witness must solve.
    pub fn enforcing(run: &'r mut queries::Run<'a, 'b, 'l>) -> Result<Self> {
        Self::with_mode(run, true)
    }
    fn with_mode(run: &'r mut queries::Run<'a, 'b, 'l>, enforce_models: bool) -> Result<Self> {
        let encoding = (
            run.cnf.solver.num_vars() as usize,
            run.cnf.clauses,
            run.cnf.literals,
        );
        let cache = Cache::new(encoding.0, Caps::default(), run.budget)?;
        Ok(Self {
            run,
            cache,
            encoding,
            enforce_models,
            claimed_models: 0,
        })
    }
    pub fn solve(&mut self, pins: &[Lit]) -> Result<bool> {
        let current = (
            self.run.cnf.solver.num_vars() as usize,
            self.run.cnf.clauses,
            self.run.cnf.literals,
        );
        if current != self.encoding {
            return Err(CheckError::Internal("shadow cache encoding changed"));
        }
        // Cancellation and deadlines apply on every path, cache hits included.
        self.run.engine.limits.cancellation.check()?;
        self.run.budget.check("completion cached solve")?;
        let hit = self.cache.lookup(pins, false, self.run.budget)?;
        if self.enforce_models && hit == Some(true) {
            self.claimed_models += 1;
            if (self.claimed_models - 1) % MODEL_HIT_SAMPLE != 0 {
                self.cache.stats.enforced_hits += 1;
                return Ok(true);
            }
            // The sample spends the ordinary allowance; an interrupted re-solve
            // propagates its cutoff and is never counted as a disagreement.
            let actual = self.run.raw_solve(pins)?;
            self.cache.stats.sampled_hits += 1;
            self.cache.compare(hit, actual);
            if !actual {
                return Err(CheckError::Internal(
                    "cached SAT model contradicted by the solver",
                ));
            }
            self.cache
                .model(self.run.cnf.solver.get_model(), self.run.budget)?;
            return Ok(true);
        }
        let actual = self.run.raw_solve(pins)?;
        self.cache.compare(hit, actual);
        if actual {
            self.cache
                .model(self.run.cnf.solver.get_model(), self.run.budget)?;
        } else {
            self.cache.core(
                self.run.cnf.solver.unsat_core(),
                pins,
                false,
                self.run.budget,
            )?;
        }
        Ok(actual)
    }
    pub fn stats(&self) -> &Stats {
        &self.cache.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use batsat::BasicSolver;

    fn ask(
        s: &mut BasicSolver,
        c: &mut Cache,
        pins: &[Lit],
        removable: bool,
        b: &mut Budget<'_>,
    ) -> bool {
        let hit = c.lookup(pins, removable, b).unwrap();
        let result = s.solve_limited(pins);
        assert!(result == lbool::TRUE || result == lbool::FALSE);
        let sat = result == lbool::TRUE;
        c.compare(hit, sat);
        if sat {
            c.model(s.get_model(), b).unwrap();
        } else {
            c.core(s.unsat_core(), pins, removable, b).unwrap();
        }
        sat
    }
    #[test]
    fn shadow_hits_agree_with_every_small_assumption_query_and_core_polarity() {
        let limits = Limits::default();
        for clause in 0..8 {
            let mut b = Budget::new(&limits);
            let mut s = BasicSolver::default();
            let vars: Vec<_> = (0..3)
                .map(|_| Lit::new(s.new_var_default(), true))
                .collect();
            let body: Vec<_> = vars
                .iter()
                .enumerate()
                .map(|(i, l)| if clause & (1 << i) == 0 { *l } else { !*l })
                .collect();
            s.add_clause_reuse(&mut body.clone());
            let mut cache = Cache::new(3, Caps::default(), &mut b).unwrap();
            let mut all = vec![];
            for mut code in 0..27 {
                let mut pins = vec![];
                for v in &vars {
                    match code % 3 {
                        1 => pins.push(*v),
                        2 => pins.push(!*v),
                        _ => (),
                    }
                    code /= 3;
                }
                all.push(pins);
            }
            for pins in all.iter().chain(all.iter().rev()) {
                let expected = (0..8).any(|bits| {
                    let holds = |l: &Lit| ((bits & (1 << l.var().idx())) != 0) == l.sign();
                    pins.iter().all(holds) && body.iter().any(holds)
                });
                assert_eq!(ask(&mut s, &mut cache, pins, false, &mut b), expected);
            }
            assert_eq!(cache.stats.mismatches, 0);
            assert!(cache.stats.model_hits > 0 && cache.stats.core_hits > 0);
        }
    }
    #[test]
    fn core_subsumption_signatures_empty_core_and_memory_caps_are_conservative() {
        let limits = Limits::default();
        let mut b = Budget::new(&limits);
        let mut s = BasicSolver::default();
        let a = Lit::new(s.new_var_default(), true);
        let z = Lit::new(s.new_var_default(), true);
        s.add_clause_reuse(&mut vec![!a]);
        let mut cache = Cache::new(2, Caps::default(), &mut b).unwrap();
        assert!(!ask(&mut s, &mut cache, &[a], false, &mut b));
        let count = cache.stats.cores;
        assert!(!ask(&mut s, &mut cache, &[a, z], false, &mut b));
        assert_eq!(cache.stats.cores, count, "a stronger core is subsumed");
        assert_eq!(cache.lookup(&[!a, z], false, &mut b).unwrap(), None);
        assert!(ask(&mut s, &mut cache, &[!a, z], false, &mut b));
        let mut empty = Cache::new(2, Caps::default(), &mut b).unwrap();
        empty.core(&[], &[], false, &mut b).unwrap();
        assert_eq!(empty.lookup(&[z], false, &mut b).unwrap(), Some(false));
        empty.epoch = u32::MAX;
        assert_eq!(empty.lookup(&[], false, &mut b).unwrap(), Some(false));
        let mut tiny = Cache::new(
            2,
            Caps {
                model_bytes: 0,
                core_bytes: 0,
                models: 0,
                cores: 0,
            },
            &mut b,
        )
        .unwrap();
        assert!(ask(&mut s, &mut tiny, &[!a], false, &mut b));
        assert!(!ask(&mut s, &mut tiny, &[a], false, &mut b));
        assert_eq!(tiny.stats.models + tiny.stats.cores, 0);
        assert_eq!(tiny.stats.mismatches, 0);
    }
    #[test]
    fn removable_clauses_disable_model_reads_and_core_writes_and_shadow_never_answers() {
        let limits = Limits::default();
        let mut b = Budget::new(&limits);
        let mut s = BasicSolver::default();
        let a = Lit::new(s.new_var_default(), true);
        let gate = Lit::new(s.new_var_default(), true);
        s.add_clause_reuse(&mut vec![!gate, !a]);
        let mut cache = Cache::new(2, Caps::default(), &mut b).unwrap();
        assert!(ask(&mut s, &mut cache, &[a, !gate], false, &mut b));
        let hits = cache.stats.model_hits;
        assert!(!ask(&mut s, &mut cache, &[a, gate], true, &mut b));
        assert_eq!(cache.stats.model_hits, hits);
        assert_eq!(cache.stats.cores, 0);
        assert!(ask(&mut s, &mut cache, &[a, !gate], false, &mut b));
        // A counted disagreement never substitutes the claimed result.
        cache.compare(Some(false), true);
        assert_eq!(cache.stats.mismatches, 1);
    }
}

#[cfg(test)]
mod owner_tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{atom, rel};
    #[test]
    fn fixed_encoding_owner_always_solves_even_on_a_hit_or_mismatch() {
        let mut c = Corpus::new();
        let i = rel(&mut c, "input", true);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &Default::default());
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let input = run.world.vars[e.program.atom_index[&atom(i)]];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::new(&mut run).unwrap();
        assert!(!fixed.solve(&[!input]).unwrap());
        assert!(!fixed.solve(&[!input]).unwrap());
        assert!(fixed.solve(&[input]).unwrap());
        assert!(fixed.solve(&[input]).unwrap());
        assert!(fixed.stats().core_hits > 0 && fixed.stats().model_hits > 0);
        assert_eq!(fixed.stats().mismatches, 0);
        fixed.cache.stats.models = 0;
        fixed.cache.columns.clear();
        fixed.cache.empty_core = true; // Deliberately wrong claim; solver still wins.
        assert!(fixed.solve(&[input]).unwrap());
        assert_eq!(fixed.stats().mismatches, 1);
        assert_eq!(fixed.run.solves(), 5, "shadow mode must not skip a solve");
        fixed.run.ledger = fixed.run.ledger.no_more_solves();
        assert!(
            fixed.solve(&[input]).is_err(),
            "a cache hit must not bypass solver limits in shadow mode"
        );
        assert!(fixed.stats().model_hits + fixed.stats().core_hits > fixed.stats().checked_hits);
    }

    /// One input forced true by a clause: `[input]` is SAT, `[!input]` UNSAT.
    fn forced_input() -> (Engine, GroundAtom) {
        let mut c = Corpus::new();
        let i = rel(&mut c, "input", true);
        let v = verification(&mut c, None, &[]);
        (prepare(&c, v, &Default::default()), atom(i))
    }

    #[test]
    fn enforced_model_hits_skip_the_solver_except_the_sample() {
        let (e, i) = forced_input();
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let input = run.world.vars[e.program.atom_index[&i]];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::enforcing(&mut run).unwrap();
        for _ in 0..201 {
            assert!(fixed.solve(&[input]).unwrap());
        }
        // One miss, then 200 claims: claims 1 and 101 are re-solved.
        assert_eq!(fixed.stats().sampled_hits, 2);
        assert_eq!(fixed.stats().enforced_hits, 198);
        assert_eq!(fixed.stats().mismatches, 0);
        assert_eq!(fixed.run.solves(), 3, "enforced hits issue no solve");
        // UNSAT queries are never answered from the model cache.
        assert!(!fixed.solve(&[!input]).unwrap());
        assert_eq!(fixed.run.solves(), 4);
    }

    #[test]
    fn a_wrong_cached_model_trips_the_tripwire() {
        let (e, i) = forced_input();
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let var = e.program.atom_index[&i];
        let input = run.world.vars[var];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::enforcing(&mut run).unwrap();
        assert!(fixed.solve(&[input]).unwrap());
        // Inject a model violating the clause: it claims `[!input]` is SAT.
        let mut wrong: Vec<_> = fixed.run.cnf.solver.get_model().to_vec();
        let v = input.var().idx() as usize;
        wrong[v] = if input.sign() {
            lbool::FALSE
        } else {
            lbool::TRUE
        };
        fixed.cache.model(&wrong, fixed.run.budget).unwrap();
        let result = fixed.solve(&[!input]);
        assert!(
            matches!(result, Err(CheckError::Internal(m)) if m.contains("contradicted")),
            "{result:?}"
        );
        assert_eq!(fixed.stats().mismatches, 1);
    }

    #[test]
    fn an_interrupted_sample_reports_its_cutoff_not_a_mismatch() {
        let (e, i) = forced_input();
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let input = run.world.vars[e.program.atom_index[&i]];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::enforcing(&mut run).unwrap();
        assert!(fixed.solve(&[input]).unwrap());
        fixed.run.ledger = fixed.run.ledger.no_more_solves();
        // The first claim is sampled; its re-solve has no solve left.
        let error = fixed.solve(&[input]).unwrap_err();
        assert!(
            inconclusive(error).is_ok(),
            "a resource cutoff, not an error"
        );
        assert_eq!(fixed.stats().mismatches, 0);
        assert_eq!(fixed.stats().checked_hits, 0);
    }

    #[test]
    fn enforced_hits_still_honour_cancellation() {
        let (e, i) = forced_input();
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let input = run.world.vars[e.program.atom_index[&i]];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::enforcing(&mut run).unwrap();
        assert!(fixed.solve(&[input]).unwrap());
        assert!(fixed.solve(&[input]).unwrap()); // sampled claim 1
        e.limits.cancellation.cancel();
        assert!(matches!(fixed.solve(&[input]), Err(CheckError::Cancelled)));
    }

    #[test]
    fn an_unsampled_hit_stops_at_an_expired_deadline() {
        let (mut e, i) = forced_input();
        e.limits.timeout = Duration::from_millis(200);
        let mut b = Budget::new(&e.limits);
        let mut run = queries::Run::new(&e, &mut b).unwrap();
        let input = run.world.vars[e.program.atom_index[&i]];
        run.cnf.clause(vec![input], run.budget).unwrap();
        let mut fixed = FixedQueries::enforcing(&mut run).unwrap();
        assert!(fixed.solve(&[input]).unwrap()); // miss
        assert!(fixed.solve(&[input]).unwrap()); // claim 1, sampled
        let solves = fixed.run.solves();
        std::thread::sleep(Duration::from_millis(300));
        // Claim 2 would be answered from the cache; the deadline wins first.
        let error = fixed.solve(&[input]).unwrap_err();
        assert!(
            inconclusive(error).is_ok(),
            "a deadline cutoff, not an error"
        );
        assert_eq!(fixed.run.solves(), solves);
        assert_eq!(fixed.stats().enforced_hits, 0);
    }
}
