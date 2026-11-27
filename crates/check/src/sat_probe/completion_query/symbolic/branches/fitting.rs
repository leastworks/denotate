//! Shared read-only incidence indexes and paged branch-local propagation state.
use super::*;
use std::ops::{Index, IndexMut};
const PAGE: usize = 1024;
#[derive(Clone)]
struct Pages<T> {
    pages: Vec<Arc<Vec<T>>>,
    len: usize,
}
impl<T: Clone> Pages<T> {
    fn new(v: Vec<T>) -> Self {
        Self {
            len: v.len(),
            pages: v.chunks(PAGE).map(|p| Arc::new(p.to_vec())).collect(),
        }
    }
    fn values(&self) -> Vec<T> {
        self.pages.iter().flat_map(|p| p.iter().cloned()).collect()
    }
}
impl<T> Index<usize> for Pages<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        &self.pages[i / PAGE][i % PAGE]
    }
}
impl<T: Clone> IndexMut<usize> for Pages<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        &mut Arc::make_mut(&mut self.pages[i / PAGE])[i % PAGE]
    }
}
pub(super) struct Incidence {
    cone: Arc<Cone>,
    readers: Vec<Vec<(usize, bool)>>,
    pub producers: Vec<Vec<usize>>,
}
#[derive(Clone)]
pub(super) struct State {
    index: Arc<Incidence>,
    values: Pages<Option<bool>>,
    alive: Pages<usize>,
    missing: Pages<usize>,
    dead: Pages<bool>,
}
impl State {
    #[cfg(test)]
    pub(super) fn values_for_test(&self) -> Vec<Option<bool>> {
        self.values.values()
    }
    #[cfg(test)]
    pub(super) fn index_for_test(&self) -> Arc<Incidence> {
        self.index.clone()
    }

    pub fn new(c: Arc<Cone>, b: &mut Budget<'_>) -> Result<Self> {
        b.charge(c.fixed.len() + c.rules.len(), "completion branch index")?;
        let mut readers = vec![vec![]; c.fixed.len()];
        let mut producers = vec![vec![]; c.fixed.len()];
        let mut alive = vec![0; c.fixed.len()];
        let mut missing = vec![0; c.rules.len()];
        let mut dead = vec![false; c.rules.len()];
        let mut seeds = vec![];
        for (j, r) in c.rules.iter().enumerate() {
            b.charge(r.body.len() + 1, "completion branch index")?;
            producers[r.head].push(j);
            if r.body
                .iter()
                .any(|(a, p)| c.fixed[*a].is_some_and(|v| v != *p))
            {
                dead[j] = true;
                continue;
            }
            alive[r.head] += 1;
            for (a, p) in &r.body {
                if c.fixed[*a].is_none() {
                    missing[j] += 1;
                    readers[*a].push((j, *p));
                }
            }
            if missing[j] == 0 && !c.input[r.head] {
                seeds.push((r.head, true));
            }
        }
        for (i, n) in alive.iter().enumerate() {
            if *n == 0 && !c.input[i] {
                seeds.push((i, false));
            }
        }
        let mut s = Self {
            values: Pages::new(c.fixed.clone()),
            alive: Pages::new(alive),
            missing: Pages::new(missing),
            dead: Pages::new(dead),
            index: Arc::new(Incidence {
                cone: c,
                readers,
                producers,
            }),
        };
        s.propagate(seeds, b)?;
        Ok(s)
    }
    fn propagate(&mut self, mut queue: Vec<(usize, bool)>, b: &mut Budget<'_>) -> Result<()> {
        while let Some((i, v)) = queue.pop() {
            b.tick("completion branch propagation")?;
            if self.values[i].is_some() {
                continue;
            }
            self.values[i] = Some(v);
            for &(r, p) in &self.index.readers[i] {
                b.tick("completion branch propagation")?;
                if self.dead[r] {
                    continue;
                }
                let h = self.index.cone.rules[r].head;
                if p != v {
                    self.dead[r] = true;
                    self.alive[h] -= 1;
                    if self.alive[h] == 0 && !self.index.cone.input[h] {
                        queue.push((h, false));
                    }
                } else {
                    self.missing[r] -= 1;
                    if self.missing[r] == 0 && !self.index.cone.input[h] {
                        queue.push((h, true));
                    }
                }
            }
        }
        Ok(())
    }
    pub fn child(&self, pins: &[(usize, bool)], b: &mut Budget<'_>) -> Result<Self> {
        // Cloning page pointers is charged; unchanged pages and all rules stay shared.
        b.charge(
            self.values.pages.len()
                + self.alive.pages.len()
                + self.missing.pages.len()
                + self.dead.pages.len()
                + pins.len(),
            "completion branch fork",
        )?;
        let mut child = self.clone();
        for (i, v) in pins {
            if child.values[*i].is_some_and(|x| x != *v) {
                return Err(CheckError::Internal("conflicting branch input pins"));
            }
        }
        child.propagate(pins.to_vec(), b)?;
        Ok(child)
    }
    pub fn value(&self, i: usize) -> Option<bool> {
        self.values[i]
    }
    pub fn producer(&self, i: usize) -> Option<usize> {
        let mut rs = self.index.producers[i]
            .iter()
            .copied()
            .filter(|r| !self.dead[*r]);
        let r = rs.next()?;
        rs.next().is_none().then_some(r)
    }
    pub fn edge_live(
        &self,
        head: usize,
        target: usize,
        negative: bool,
        b: &mut Budget<'_>,
    ) -> Result<bool> {
        if self.value(head).is_some() || self.value(target).is_some() {
            return Ok(false);
        }
        for r in &self.index.producers[head] {
            let rule = &self.index.cone.rules[*r];
            b.charge(rule.body.len() + 1, "completion split trial edges")?;
            if !self.dead[*r] && rule.body.contains(&(target, !negative)) {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub fn source(&self) -> &Cone {
        &self.index.cone
    }
    /// The same state with its retained equations dropped (they were shown
    /// implied). Incidence depends only on rules, so values carry over.
    pub fn without_retained(&self, b: &mut Budget<'_>) -> Result<Self> {
        let c = &self.index.cone;
        b.charge(
            c.fixed.len() + c.rules.len(),
            "completion forcing discharge",
        )?;
        let mut cone = (**c).clone();
        cone.retained = vec![].into();
        let mut out = self.clone();
        out.index = Arc::new(Incidence {
            cone: Arc::new(cone),
            readers: self.index.readers.clone(),
            producers: self.index.producers.clone(),
        });
        Ok(out)
    }
    /// Only ancestor-proved constants and explicit assignments enter a proof.
    /// Ordinary propagation is for ranking/execution, not a common-equations premise.
    fn proof_cone(&self, pins: &[(usize, bool)], b: &mut Budget<'_>) -> Result<Arc<Cone>> {
        b.charge(
            self.index.cone.fixed.len() + pins.len(),
            "completion branch proof inputs",
        )?;
        let mut c = (*self.index.cone).clone();
        for (i, v) in pins {
            c.fixed[*i] = Some(*v);
        }
        Ok(Arc::new(c))
    }
    pub fn analysis_cone(&self, b: &mut Budget<'_>) -> Result<Arc<Cone>> {
        Ok(Arc::new(search_free::reduce(&*self.cone(b)?, b)?.cone))
    }
    pub fn cone(&self, b: &mut Budget<'_>) -> Result<Arc<Cone>> {
        b.charge(self.values.len, "completion branch values")?;
        let c = &self.index.cone;
        Ok(Arc::new(Cone {
            atoms: c.atoms.clone(),
            rules: c.rules.clone(),
            input: c.input.clone(),
            target: c.target.clone(),
            duplicated: c.duplicated.clone(),
            groups: c.groups.clone(),
            source_rules: c.source_rules,
            retained: c.retained.clone(),
            fixed: self.values.values(),
        }))
    }
}
#[derive(Clone)]
pub(super) struct Bundle {
    pub cone: State,
    pub world: State,
    pub classification: Option<State>,
    pub assumptions: Vec<State>,
    views: BTreeMap<pruning::ViewKey, State>,
    cone_key: pruning::ViewKey,
    classification_key: Option<pruning::ViewKey>,
    pub pins: Vec<(usize, bool)>,
    pub formulas: Vec<branch_formula::Pin>,
    pub trials: Option<Arc<std::sync::Mutex<pruning::TrialPool>>>,
    pub proofs: Vec<PruningReport>,
    pub forcing: Vec<forcing::ForcingRecord>,
    forced_scopes: BTreeSet<(Vec<usize>, PruningContext)>,
    /// Scopes (classification or not) whose current views were pruned to a
    /// fixed point; any view change clears it. Re-pruning an unchanged view
    /// repeats the same attempts and proves nothing new.
    saturated: BTreeSet<bool>,
}
impl Bundle {
    pub fn new(e: &Engine, b: &mut Budget<'_>) -> Result<Self> {
        let views = e
            .pruning
            .as_ref()
            .map(|c| c.lock().unwrap().branch_views(e))
            .unwrap_or_default();
        Ok(Self {
            formulas: e.formula_pins.clone(),
            pins: e
                .pruning
                .as_ref()
                .map(|c| c.lock().unwrap().pins.clone())
                .unwrap_or_default(),
            proofs: vec![],
            forcing: vec![],
            forced_scopes: BTreeSet::new(),
            saturated: BTreeSet::new(),
            trials: e
                .pruning
                .as_ref()
                .and_then(|c| c.lock().unwrap().trials.clone()),
            views: views
                .into_iter()
                .map(|(k, c)| Ok((k, State::new(c, b)?)))
                .collect::<Result<_>>()?,
            cone_key: pruning::view_key(&e.cone, PruningContext::World),
            classification_key: e
                .classification
                .as_ref()
                .map(|(c, _, _)| pruning::view_key(c, PruningContext::World)),
            cone: State::new(e.cone.clone(), b)?,
            world: State::new(e.world.clone(), b)?,
            classification: e
                .classification
                .as_ref()
                .map(|(c, _, _)| State::new(c.clone(), b))
                .transpose()?,
            assumptions: e
                .assumptions
                .iter()
                .map(|a| State::new(Arc::new(a.cone.clone()), b))
                .collect::<Result<_>>()?,
        })
    }
    pub fn child(&self, pins: &[(usize, bool)], b: &mut Budget<'_>) -> Result<Self> {
        let mut assignments: BTreeMap<_, _> = self.pins.iter().copied().collect();
        for (i, v) in pins {
            if assignments.insert(*i, *v).is_some_and(|old| old != *v) {
                return Err(CheckError::Internal("conflicting branch context"));
            }
        }
        let assignments: Vec<_> = assignments.into_iter().collect();
        Ok(Self {
            pins: assignments.clone(),
            formulas: self.formulas.clone(),
            trials: self.trials.clone(),
            proofs: vec![],
            forcing: vec![],
            forced_scopes: BTreeSet::new(),
            saturated: BTreeSet::new(),
            views: self
                .views
                .iter()
                .map(|(k, s)| {
                    let mut k = k.clone();
                    k.2 = assignments.clone();
                    Ok((k, s.child(pins, b)?))
                })
                .collect::<Result<_>>()?,
            cone_key: self.cone_key.clone(),
            classification_key: self.classification_key.clone(),
            cone: self.cone.child(pins, b)?,
            world: self.world.child(pins, b)?,
            classification: self
                .classification
                .as_ref()
                .map(|s| s.child(pins, b))
                .transpose()?,
            assumptions: self
                .assumptions
                .iter()
                .map(|s| s.child(pins, b))
                .collect::<Result<_>>()?,
        })
    }
    pub fn scope(&self, classification: bool) -> Vec<usize> {
        if classification {
            self.classification_key.as_ref().unwrap().0.clone()
        } else {
            self.cone_key.0.clone()
        }
    }
    /// Typed derived pins keep their input formula and original proof context.
    /// They never overwrite the assumption/universe equations or unrelated scopes.
    pub fn child_with_formula(
        &self,
        pins: &[(usize, bool)],
        formula: Option<&Arc<branch_formula::SettledAtom>>,
        b: &mut Budget<'_>,
    ) -> Result<Self> {
        let Some(formula) = formula else {
            return self.child(pins, b);
        };
        let mut out = self.child(&[], b)?;
        let [(atom, value)] = pins else {
            return Err(CheckError::Internal("formula branch needs one pin"));
        };
        if *atom != formula.atom {
            return Err(CheckError::Internal(
                "formula pin does not match certificate",
            ));
        }
        let value = *value;
        let mut assignments: BTreeMap<_, _> = self.pins.iter().copied().collect();
        if assignments
            .insert(formula.atom, value)
            .is_some_and(|v| v != value)
        {
            return Err(CheckError::Internal("conflicting formula pins"));
        }
        out.pins = assignments.into_iter().collect();
        out.views = out
            .views
            .into_iter()
            .map(|(mut k, s)| {
                k.2 = out.pins.clone();
                (k, s)
            })
            .collect();
        for context in [PruningContext::World, PruningContext::Hypothesis] {
            if formula.context == PruningContext::Hypothesis && context == PruningContext::World {
                continue;
            }
            let classification = self
                .classification_key
                .as_ref()
                .is_some_and(|k| k.0 == *formula.scope);
            let (state, _) = self.ranking(classification, context == PruningContext::Hypothesis);
            let key = ((*formula.scope).clone(), context, out.pins.clone());
            out.views.insert(key, state.child(pins, b)?);
        }
        out.formulas.push(branch_formula::Pin {
            certificate: formula.clone(),
            value,
        });
        Ok(out)
    }
    pub fn ranking(&self, classification: bool, hypothesis: bool) -> (&State, &'static str) {
        let base = if classification {
            self.classification.as_ref().unwrap()
        } else {
            &self.cone
        };
        let mut key = if classification {
            self.classification_key.as_ref().unwrap().clone()
        } else {
            self.cone_key.clone()
        };
        key.2 = self.pins.clone();
        if hypothesis {
            key.1 = PruningContext::Hypothesis;
            if let Some(s) = self.views.get(&key) {
                return (s, "W+H");
            }
        }
        key.1 = PruningContext::World;
        (self.views.get(&key).unwrap_or(base), "W")
    }
    /// Reduce each applicable parent view once, then share its incidence index
    /// with all trial children. Child propagation remains copy-on-write.
    pub fn trial_base(
        &self,
        classification: bool,
        hypothesis: bool,
        b: &mut Budget<'_>,
    ) -> Result<Self> {
        let mut out = self.clone();
        for context in [PruningContext::World, PruningContext::Hypothesis] {
            if context == PruningContext::Hypothesis && !hypothesis {
                continue;
            }
            let (state, _) = self.ranking(classification, context == PruningContext::Hypothesis);
            let reduced = state.analysis_cone(b)?;
            let key = (self.scope(classification), context, self.pins.clone());
            out.views.insert(key, State::new(reduced, b)?);
        }
        out.saturated.clear();
        Ok(out)
    }

    pub fn prune(
        &mut self,
        e: &Engine,
        classification: bool,
        heads: &BTreeSet<usize>,
        config: &mut QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<(usize, usize, Option<Inconclusive>)> {
        let Some(pool) = self.trials.clone() else {
            return Ok((0, 0, None));
        };
        let scope = if classification {
            "classification"
        } else {
            "processing"
        };
        if ![PruningContext::World, PruningContext::Hypothesis]
            .into_iter()
            .any(|c| pool.lock().unwrap().available(scope, c))
        {
            let pool = pool.lock().unwrap();
            let error = pool
                .cutoff(scope, PruningContext::World)
                .or_else(|| pool.cutoff(scope, PruningContext::Hypothesis));
            return Ok((0, 0, error.map(inconclusive).transpose()?));
        }
        let mut attempts = 0;
        let mut proved = 0;
        let mut cutoff = None;
        for context in [PruningContext::World, PruningContext::Hypothesis] {
            if context == PruningContext::World
                && self
                    .formulas
                    .iter()
                    .any(|p| p.certificate.context == PruningContext::Hypothesis)
            {
                continue;
            }
            if context == PruningContext::Hypothesis && e.classification.is_none() {
                continue;
            }
            if !pool.lock().unwrap().available(scope, context) {
                cutoff = cutoff.or(pool
                    .lock()
                    .unwrap()
                    .cutoff(scope, context)
                    .map(inconclusive)
                    .transpose()?);
                continue;
            }
            let hypothesis = context == PruningContext::Hypothesis;
            let (state, _) = self.ranking(classification, hypothesis);
            let answer = pruning::trial(
                e,
                scope,
                context,
                &pool,
                b,
                config,
                |local, query, used, report| {
                    let mut branch = self.engine(e, local)?;
                    branch.config = query.clone();
                    let scope_key = self.scope(classification);
                    let applicable: Vec<_> = self
                        .pins
                        .iter()
                        .copied()
                        .filter(|(i, _)| {
                            e.cone.input[*i]
                                || self.formulas.iter().any(|p| {
                                    p.certificate.atom == *i
                                        && *p.certificate.scope == scope_key
                                        && (p.certificate.context == PruningContext::World
                                            || context == PruningContext::Hypothesis)
                                })
                        })
                        .collect();
                    let base = state.proof_cone(&applicable, local)?;
                    let result = pruning::prove(
                        &branch, &base, scope, context, &self.pins, heads, local, used, report,
                    )?;
                    if report.removed > 0 || report.removed_literals > 0 {
                        State::new(result, local).map(Some)
                    } else {
                        Ok(None)
                    }
                },
            );
            let (state, report) = match answer {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(error) => {
                    e.limits.cancellation.check()?;
                    cutoff = Some(inconclusive(error)?);
                    continue;
                }
            };
            attempts += report.attempts;
            proved += report.records.len() + report.omitted;
            cutoff = cutoff
                .or_else(|| report.incomplete.first().copied())
                .or_else(|| report.components.iter().find_map(|c| c.cutoff));
            if let Some(state) = state {
                let mut key = if classification {
                    self.classification_key.as_ref().unwrap().clone()
                } else {
                    self.cone_key.clone()
                };
                key.1 = context;
                key.2 = self.pins.clone();
                self.views.insert(key, state);
                self.saturated.clear();
                self.proofs.push(report);
            }
        }
        Ok((attempts, proved, cutoff))
    }
    /// Exploration runs the whole current unit before considering a split.
    /// The ordinary trial path keeps its bounded target subset and one pass.
    fn prune_to_fixed_point(
        &mut self,
        e: &Engine,
        classification: bool,
        config: &mut QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<usize> {
        if self.trials.is_none() {
            return Ok(0);
        }
        if self.saturated.contains(&classification) {
            return Ok(0);
        }
        let started = Instant::now();
        let before = b.used();
        let phase = "completion unit pruning";
        e.exploration(phase, "started", 0, Duration::ZERO);
        let mut total = 0;
        loop {
            let mut heads = BTreeSet::new();
            for hypothesis in [false, true] {
                if hypothesis && e.classification.is_none() {
                    continue;
                }
                let (state, _) = self.ranking(classification, hypothesis);
                let view = state.cone(b)?;
                let graph = consistency::analyse(&view, None, b)?;
                heads.extend(
                    graph
                        .cyclic
                        .iter()
                        .enumerate()
                        .filter_map(|(i, c)| (*c && view.fixed[i].is_none()).then_some(i)),
                );
            }
            if heads.is_empty() {
                e.exploration(phase, "completed", b.used() - before, started.elapsed());
                self.saturated.insert(classification);
                return Ok(total);
            }
            let (_, proved, cutoff) = self.prune(e, classification, &heads, config, b)?;
            total += proved;
            if cutoff.is_none() && proved == 0 {
                self.saturated.insert(classification);
            }
            if cutoff.is_some() || proved == 0 {
                e.exploration(
                    phase,
                    if cutoff.is_some() {
                        "cut-off"
                    } else {
                        "completed"
                    },
                    b.used() - before,
                    started.elapsed(),
                );
                return Ok(total);
            }
        }
    }
    /// Optional work inside the caller's existing ranking allocation. Contexts
    /// receive equal shares; failures leave the previous equivalent view intact.
    pub fn settle(
        &mut self,
        e: &Engine,
        classification: bool,
        trial: bool,
        config: &mut QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<()> {
        if e.limits.completion_exploration {
            if self.prune_to_fixed_point(e, classification, config, b)? > 0 {
                let scope = self.scope(classification);
                self.forced_scopes.retain(|(s, _)| *s != scope);
            }
        }
        // Exploration forces only the selected partition's children (in their
        // own units): on the corpus, forcing inside every trial child found no
        // constants while costing most of each ranking. Trial scores stay
        // structural.
        if !e.forcing || (trial && e.limits.completion_exploration) {
            return Ok(());
        }
        let contexts: Vec<_> = [PruningContext::World, PruningContext::Hypothesis]
            .into_iter()
            .filter(|c| {
                !self
                    .forced_scopes
                    .contains(&(self.scope(classification), *c))
            })
            .filter(|c| {
                if *c == PruningContext::World {
                    !self
                        .formulas
                        .iter()
                        .any(|p| p.certificate.context == PruningContext::Hypothesis)
                } else {
                    e.classification.is_some()
                }
            })
            .collect();
        for (position, context) in contexts.iter().copied().enumerate() {
            let mut limits = e.limits.clone();
            limits.timeout = b.remaining_time()
                / e.limits.completion_share(2 * (contexts.len() - position)) as u32;
            limits.max_work =
                b.remaining() / e.limits.completion_share(2 * (contexts.len() - position));
            let end = Instant::now() + limits.timeout;
            limits.run_deadline = Some(if e.limits.completion_exploration {
                e.limits.run_deadline.map_or(end, |d| d.min(end))
            } else {
                end
            });
            let started = Instant::now();
            let phase = if context == PruningContext::World {
                "completion branch forcing W"
            } else {
                "completion branch forcing W+H"
            };
            e.exploration(phase, "started", 0, Duration::ZERO);
            let mut allowance = super::divided(
                config,
                e.limits.completion_share(2 * (contexts.len() - position)),
            );
            let before = allowance.clone();
            let mut local = Budget::new(&limits);
            let result: Result<()> = (|| {
                loop {
                    let mut engine = self.engine(e, &mut local)?;
                    engine.config = allowance.clone();
                    let (state, _) =
                        self.ranking(classification, context == PruningContext::Hypothesis);
                    let cone = state.cone(&mut local)?;
                    let (forced, mut report) = forcing::force(
                        &engine,
                        cone,
                        context,
                        &self.pins,
                        &mut local,
                        &mut allowance,
                    )?;
                    let changed = report.forced > 0;
                    let cutoff = report.cutoff.is_some();
                    if changed {
                        let state = match State::new(forced, &mut local) {
                            Ok(state) => state,
                            Err(error) => {
                                e.limits.cancellation.check()?;
                                report.not_installed(error)?;
                                self.forcing.push(report);
                                break;
                            }
                        };
                        self.views.insert(
                            (self.scope(classification), context, self.pins.clone()),
                            state,
                        );
                        self.saturated.clear();
                    }
                    // Installed first, then the optional discharge: a cutoff
                    // there keeps the installed constants and their equations.
                    // Dropping implied equations changes no value, rule or model,
                    // so it is not a change for pruning or another forcing round.
                    if !cutoff {
                        self.discharge(
                            &engine,
                            classification,
                            context,
                            &mut report,
                            &mut allowance,
                            &mut local,
                        )?;
                    }
                    let cutoff = report.cutoff.is_some();
                    self.forcing.push(report);
                    if cutoff {
                        break;
                    }
                    // Newly acyclic dependents enter the ordinary formula pool.
                    let proved = if e.limits.completion_exploration {
                        self.prune_to_fixed_point(e, classification, &mut allowance, &mut local)?
                    } else {
                        let (state, _) =
                            self.ranking(classification, context == PruningContext::Hypothesis);
                        let view = state.cone(&mut local)?;
                        let graph = consistency::analyse(&view, None, &mut local)?;
                        let heads: BTreeSet<_> = graph
                            .cyclic
                            .iter()
                            .enumerate()
                            .filter_map(|(i, cyclic)| {
                                (*cyclic && view.fixed[i].is_none()).then_some(i)
                            })
                            .take(32)
                            .collect();
                        if heads.is_empty() {
                            0
                        } else {
                            self.prune(e, classification, &heads, &mut allowance, &mut local)?
                                .1
                        }
                    };
                    if !changed && proved == 0 {
                        break;
                    }
                }
                Ok(())
            })();
            e.exploration(
                phase,
                if result.is_err() || self.forcing.last().is_some_and(|r| r.cutoff.is_some()) {
                    "cut-off"
                } else {
                    "completed"
                },
                local.used(),
                started.elapsed(),
            );
            config.max_solves = config
                .max_solves
                .saturating_sub(before.max_solves - allowance.max_solves);
            config.max_solver_polls = config
                .max_solver_polls
                .saturating_sub(before.max_solver_polls - allowance.max_solver_polls);
            config.max_conflicts = config
                .max_conflicts
                .saturating_sub(before.max_conflicts - allowance.max_conflicts);
            config.max_propagations = config
                .max_propagations
                .saturating_sub(before.max_propagations - allowance.max_propagations);
            self.forced_scopes
                .insert((self.scope(classification), context));
            if let Err(error) = result {
                e.limits.cancellation.check()?;
                self.forcing.push(forcing::ForcingRecord {
                    context: if context == PruningContext::World {
                        "W"
                    } else {
                        "W+H"
                    },
                    cutoff: Some(inconclusive(error)?),
                    ..Default::default()
                });
            }
            b.charge(local.used(), "completion forcing work")?;
        }
        Ok(())
    }

    /// Drop the context view's retained definitions (installed here or inherited
    /// from an ancestor or the W pass) when its constants imply them under this
    /// branch's pins: they block the structural existence certificate. A cutoff
    /// is recorded on `report` and keeps the view.
    fn discharge(
        &mut self,
        e: &Engine,
        classification: bool,
        context: PruningContext,
        report: &mut forcing::ForcingRecord,
        allowance: &mut QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<bool> {
        let (state, _) = self.ranking(classification, context == PruningContext::Hypothesis);
        if state.source().retained.is_empty() {
            return Ok(false);
        }
        let state = state.clone();
        let result = (|| {
            let cone = state.cone(b)?;
            if !forcing::implied(e, &cone, context, &self.pins, b, allowance)? {
                return Ok(None);
            }
            Ok(Some(state.without_retained(b)?))
        })();
        match result {
            Ok(Some(state)) => {
                self.views.insert(
                    (self.scope(classification), context, self.pins.clone()),
                    state,
                );
                report.discharged = true;
                Ok(true)
            }
            Ok(None) => Ok(false),
            Err(error) => {
                e.limits.cancellation.check()?;
                report.cutoff = Some(inconclusive(error)?);
                Ok(false)
            }
        }
    }
    #[cfg(test)]
    pub(super) fn discharge_for_test(
        &mut self,
        e: &Engine,
        classification: bool,
        report: &mut forcing::ForcingRecord,
        allowance: &mut QueryLimits,
        b: &mut Budget<'_>,
    ) -> Result<bool> {
        self.discharge(
            e,
            classification,
            PruningContext::World,
            report,
            allowance,
            b,
        )
    }
    pub fn publish(&mut self, e: &Engine) {
        if let Some(cache) = &e.pruning {
            let mut cache = cache.lock().unwrap();
            for mut report in self.proofs.drain(..) {
                // Trial details live with the candidate's branch context. Source
                // findings only come from selected partitions, never lost trials.
                report.components.clear();
                report.incomplete.clear();
                cache.merge(report);
            }
        }
    }
    pub fn engine(&self, e: &Engine, b: &mut Budget<'_>) -> Result<Engine> {
        let mut out = e.clone();
        out.formula_pins = self.formulas.clone();
        out.pruning = if e.pruning.is_some() || e.forcing || !self.formulas.is_empty() {
            let views = self
                .views
                .iter()
                .map(|(k, s)| Ok((k.clone(), s.cone(b)?)))
                .collect::<Result<_>>()?;
            Some(Arc::new(std::sync::Mutex::new(pruning::Cache::inherited(
                views,
                self.pins.clone(),
            ))))
        } else {
            None
        };
        out.branches = None;
        out.cone = self.cone.cone(b)?;
        out.world = self.world.cone(b)?;
        out.classification = e
            .classification
            .as_ref()
            .map(|(_, m, h)| -> Result<_> {
                Ok((
                    self.classification.as_ref().unwrap().cone(b)?,
                    m.clone(),
                    *h,
                ))
            })
            .transpose()?;
        Ok(out)
    }
}
