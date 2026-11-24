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
}
impl Bundle {
    pub fn new(e: &Engine, b: &mut Budget<'_>) -> Result<Self> {
        let views = e
            .pruning
            .as_ref()
            .map(|c| c.lock().unwrap().branch_views(e))
            .unwrap_or_default();
        Ok(Self {
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
        Ok(Self {
            views: self
                .views
                .iter()
                .map(|(k, s)| Ok((k.clone(), s.child(pins, b)?)))
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
        if hypothesis {
            key.1 = PruningContext::Hypothesis;
            if let Some(s) = self.views.get(&key) {
                return (s, "W+H");
            }
        }
        key.1 = PruningContext::World;
        (self.views.get(&key).unwrap_or(base), "W")
    }
    pub fn engine(&self, e: &Engine, b: &mut Budget<'_>) -> Result<Engine> {
        let mut out = e.clone();
        out.pruning = if e.pruning.is_some() {
            let views = self
                .views
                .iter()
                .map(|(k, s)| Ok((k.clone(), s.cone(b)?)))
                .collect::<Result<_>>()?;
            Some(Arc::new(std::sync::Mutex::new(pruning::Cache::inherited(
                views,
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
