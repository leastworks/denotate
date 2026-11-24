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
                self.proofs.push(report);
            }
        }
        Ok((attempts, proved, cutoff))
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
        out.pruning = if e.pruning.is_some() || !self.formulas.is_empty() {
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
