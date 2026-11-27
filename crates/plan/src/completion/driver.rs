//! The path driver. On each runtime path (input pins): sequence ready
//! expressions, substitute constants the checker proves on the path (under H for
//! classification and processing, keeping a runtime check where a definition is
//! not implied), split on an input when stuck, and end in a terminal.
use super::*;
use q::PathStep;

type Step<T> = Result<std::result::Result<T, Problem>>;

#[derive(Debug, Clone)]
pub(super) struct State {
    pins: BTreeMap<AtomKey, bool>,
    available: BTreeSet<AtomKey>,
    /// Classification constants substituted on this path. At the leaf, exactly
    /// this set is either shown implied or checked at runtime; their bodies are
    /// sequenced so the checks can be evaluated.
    substituted: BTreeMap<AtomKey, bool>,
}
impl State {
    pub(super) fn entry(inputs: &BTreeSet<AtomKey>) -> Self {
        Self {
            pins: BTreeMap::new(),
            available: inputs.clone(),
            substituted: BTreeMap::new(),
        }
    }
    fn path(&self) -> PathFacts {
        self.pins.iter().map(|(k, v)| (k.clone(), *v)).collect()
    }
    fn pinned(&self, on: &AtomKey, value: bool) -> Self {
        let mut s = self.clone();
        s.pins.insert(on.clone(), value);
        s
    }
}
pub(super) struct Driver<'e, 'o, 'w> {
    pub engine: &'e q::Engine,
    pub atoms: BTreeMap<AtomKey, GroundAtom>,
    pub keys_of: BTreeMap<GroundAtom, AtomKey>,
    pub rules: BTreeMap<AtomKey, Vec<Rule>>,
    pub inputs: BTreeSet<AtomKey>,
    pub hypothesis: Option<AtomKey>,
    pub class_targets: BTreeSet<AtomKey>,
    pub class_scope: BTreeSet<AtomKey>,
    pub output_scope: BTreeSet<AtomKey>,
    pub outputs: BTreeSet<AtomKey>,
    pub output_atoms: BTreeSet<GroundAtom>,
    pub options: &'o Options,
    pub work: Work<'w>,
    pub nodes: usize,
    pub calls: usize,
    pub splits: usize,
}
impl Driver<'_, '_, '_> {
    fn runtime(&self, s: &State) -> q::RuntimePath {
        s.pins
            .iter()
            .map(|(k, v)| (self.atoms[k].clone(), *v))
            .collect()
    }
    fn oracle(
        &mut self,
        s: &State,
        outputs: Option<&BTreeSet<GroundAtom>>,
        hypothesis: bool,
    ) -> Result<PathStep> {
        room(self.calls, self.options.max_oracle_calls, "oracle calls")?;
        self.calls += 1;
        let path = self.runtime(s);
        self.engine.planning_path_step(&path, outputs, hypothesis)
    }
    /// The rules of `k` on this path: a rule with a literal its pins falsify is
    /// dead, and literals they satisfy are dropped.
    fn simplified(&mut self, k: &AtomKey, s: &State) -> Result<Vec<Rule>> {
        let mut out = vec![];
        for r in self.rules.get(k).into_iter().flatten() {
            self.work.tick(r.body.len() + 1)?;
            if r.body
                .iter()
                .any(|(a, p)| s.pins.get(a).is_some_and(|v| v != p))
            {
                continue;
            }
            let mut r = r.clone();
            r.body.retain(|(a, _)| !s.pins.contains_key(a));
            out.push(r);
        }
        Ok(out)
    }
    fn emit(&mut self, nodes: &mut BTreeMap<AtomKey, Node>, node: Node) -> Result<()> {
        room(self.nodes, self.options.max_nodes, "nodes")?;
        self.nodes += 1;
        nodes.insert(node.id.clone(), node);
        Ok(())
    }
    /// Unavailable atoms the targets still need on this path.
    fn needed(&mut self, s: &State, targets: &BTreeSet<AtomKey>) -> Result<BTreeSet<AtomKey>> {
        let mut pending: Vec<_> = targets
            .iter()
            .filter(|k| !s.available.contains(*k))
            .cloned()
            .collect();
        let mut needed = BTreeSet::new();
        while let Some(k) = pending.pop() {
            self.work.tick(1)?;
            if s.available.contains(&k) || !needed.insert(k.clone()) {
                continue;
            }
            for r in self.simplified(&k, s)? {
                pending.extend(r.body.iter().map(|(a, _)| a.clone()));
            }
        }
        Ok(needed)
    }
    /// Substitute every proved constant not yet computed on this path, before
    /// sequencing: no atom of the substituted set is then computed from its
    /// rules, so `planning_discharged` is asked about exactly what the plan uses.
    fn substitute(
        &mut self,
        s: &mut State,
        constants: &BTreeMap<AtomKey, bool>,
        mut processing: Option<&mut BTreeMap<AtomKey, bool>>,
        nodes: &mut BTreeMap<AtomKey, Node>,
    ) -> Result<()> {
        for (k, v) in constants {
            if s.available.contains(k) {
                continue;
            }
            let rs = self.rules.get(k).cloned().unwrap_or_default();
            self.emit(nodes, constant_node(k, *v, &rs))?;
            s.available.insert(k.clone());
            match processing.as_deref_mut() {
                Some(map) => map.insert(k.clone(), *v),
                None => s.substituted.insert(k.clone(), *v),
            };
        }
        Ok(())
    }
    /// Sequence the targets (and, for classification, the bodies of the path's
    /// substituted constants, so their checks can be evaluated) by expressions.
    /// Returns the atoms still needed (empty when done).
    fn settle(
        &mut self,
        s: &mut State,
        targets: &BTreeSet<AtomKey>,
        classification: bool,
        nodes: &mut BTreeMap<AtomKey, Node>,
    ) -> Result<Vec<AtomKey>> {
        loop {
            let mut all = targets.clone();
            let bodies: Vec<_> = if classification {
                s.substituted.keys().cloned().collect()
            } else {
                vec![]
            };
            for k in bodies {
                for r in self.simplified(&k, s)? {
                    all.extend(r.body.iter().map(|(a, _)| a.clone()));
                }
            }
            let needed = self.needed(s, &all)?;
            if needed.is_empty() {
                return Ok(vec![]);
            }
            let mut progress = false;
            for k in &needed {
                let rs = self.simplified(k, s)?;
                if let Some(e) = crate::search::expression(&rs, &s.available, &mut self.work)? {
                    self.emit(nodes, compute_node(k, e, &rs))?;
                    s.available.insert(k.clone());
                    progress = true;
                }
            }
            if progress {
                continue;
            }
            return Ok(needed.into_iter().collect());
        }
    }
    /// Unsequenced atoms of `scope` on an odd loop (then no interpretation need
    /// extend the computed values).
    fn odd_remainder(&mut self, s: &State, scope: &BTreeSet<AtomKey>) -> Result<Vec<AtomKey>> {
        let rest: Vec<_> = scope
            .iter()
            .filter(|k| !s.available.contains(*k) && self.rules.contains_key(*k))
            .cloned()
            .collect();
        let index: BTreeMap<_, _> = rest
            .iter()
            .enumerate()
            .map(|(i, k)| (k.clone(), i))
            .collect();
        // Parity-doubled graph: (atom, parity) -> (body atom, parity ^ negative).
        let n = rest.len() * 2;
        let mut edges = vec![vec![]; n];
        for (i, k) in rest.iter().enumerate() {
            for r in self.simplified(k, s)? {
                for (a, p) in &r.body {
                    if let Some(j) = index.get(a) {
                        let flip = usize::from(!p);
                        for parity in 0..2 {
                            edges[2 * i + parity].push(2 * j + (parity ^ flip));
                        }
                    }
                }
            }
        }
        self.work
            .tick(n + edges.iter().map(Vec::len).sum::<usize>())?;
        let component = components(&edges);
        Ok(rest
            .iter()
            .enumerate()
            .filter(|(i, _)| component[2 * i] == component[2 * i + 1])
            .map(|(_, k)| k.clone())
            .collect())
    }
    fn dependencies(
        &mut self,
        s: &State,
        atoms: &[AtomKey],
    ) -> Result<Vec<(AtomKey, AtomKey, bool)>> {
        let mut out = vec![];
        for k in atoms {
            for r in self.simplified(k, s)? {
                out.extend(r.body.iter().map(|(a, p)| (k.clone(), a.clone(), *p)));
            }
        }
        Ok(out)
    }
    /// An unpinned input whose value lets stuck atoms sequence in at least one
    /// arm; the most such atoms over both arms, then the first in key order.
    fn split_input(&mut self, s: &State, stuck: &[AtomKey]) -> Result<Option<AtomKey>> {
        if s.pins.len() >= self.options.max_split_depth {
            return Ok(None);
        }
        let mut candidates = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut pending: Vec<_> = stuck.to_vec();
        while let Some(k) = pending.pop() {
            self.work.tick(1)?;
            if !seen.insert(k.clone()) {
                continue;
            }
            for r in self.simplified(&k, s)? {
                for (a, _) in &r.body {
                    if self.inputs.contains(a) {
                        if !s.pins.contains_key(a) {
                            candidates.insert(a.clone());
                        }
                    } else if !s.available.contains(a) {
                        pending.push(a.clone());
                    }
                }
            }
        }
        let stuck: BTreeSet<_> = stuck.iter().cloned().collect();
        let mut best: Option<(usize, AtomKey)> = None;
        for i in candidates
            .into_iter()
            .take(self.options.max_split_candidates)
        {
            let mut score = 0;
            for value in [true, false] {
                let mut child = s.pinned(&i, value);
                let mut scratch = BTreeMap::new();
                let before = child.available.len();
                // Structural only: no constants, no checker call.
                let saved = self.nodes;
                self.settle(&mut child, &stuck, false, &mut scratch)?;
                self.nodes = saved;
                score += child.available.len() - before;
            }
            if score > 0 && best.as_ref().is_none_or(|(b, _)| score > *b) {
                best = Some((score, i));
            }
        }
        Ok(best.map(|(_, i)| i))
    }
    fn unresolved(&mut self, phase: &'static str, s: &State, atoms: Vec<AtomKey>) -> Step<()> {
        let dependencies = self.dependencies(s, &atoms)?;
        Ok(Err(Problem::Unresolved {
            phase,
            path: s.path(),
            atoms,
            dependencies,
        }))
    }
    pub(super) fn classify(&mut self, mut s: State) -> Step<Region> {
        let mut nodes = BTreeMap::new();
        let Some(h) = self.hypothesis.clone() else {
            // No H: every permitted message is accepted.
            let accepted = match self.accept(s)? {
                Ok(a) => a,
                Err(p) => return Ok(Err(p)),
            };
            return Ok(Ok(Region {
                nodes,
                next: Next::Leaf {
                    checks: vec![],
                    terminal: Terminal::Accept,
                    accepted: Some(Box::new(accepted)),
                },
            }));
        };
        let constants = match self.oracle(&s, None, true)? {
            PathStep::Empty => {
                return Ok(Ok(Region {
                    nodes,
                    next: Next::Leaf {
                        checks: vec![],
                        terminal: Terminal::Reject,
                        accepted: None,
                    },
                }));
            }
            PathStep::Inconclusive(cause) => {
                return Ok(Err(Problem::PathInconclusive {
                    path: s.path(),
                    cause,
                }));
            }
            PathStep::Forced { constants } => self.keyed(constants)?,
        };
        self.substitute(&mut s, &constants, None, &mut nodes)?;
        let targets = self.class_targets.clone();
        let stuck = self.settle(&mut s, &targets, true, &mut nodes)?;
        if stuck.is_empty() {
            let scope = self.class_scope.clone();
            let odd = self.odd_remainder(&s, &scope)?;
            if !odd.is_empty() {
                return Ok(self
                    .unresolved("classification", &s, odd)?
                    .map(|()| unreachable!()));
            }
            // Exactly the substituted set: implied, or every definition checked.
            let substituted = s.substituted.clone();
            let checked = !substituted.is_empty()
                && match self.discharged(&s, None, true, &substituted)? {
                    q::Discharge::Implied => false,
                    q::Discharge::NotImplied => true,
                    q::Discharge::Inconclusive(cause) => {
                        return Ok(Err(Problem::PathInconclusive {
                            path: s.path(),
                            cause,
                        }));
                    }
                };
            let mut checks = vec![];
            for (k, v) in substituted.into_iter().filter(|_| checked) {
                let rs = self.simplified(&k, &s)?;
                match crate::search::expression(&rs, &s.available, &mut self.work)? {
                    Some(definition) => checks.push(Check {
                        atom: k,
                        value: v,
                        definition,
                    }),
                    None => {
                        return Ok(self
                            .unresolved("classification", &s, vec![k])?
                            .map(|()| unreachable!()));
                    }
                }
            }
            let accepted = match self.accept(s)? {
                Ok(a) => a,
                Err(p) => return Ok(Err(p)),
            };
            return Ok(Ok(Region {
                nodes,
                next: Next::Leaf {
                    checks,
                    terminal: Terminal::Test(h),
                    accepted: Some(Box::new(accepted)),
                },
            }));
        }
        let Some(on) = self.split_input(&s, &stuck)? else {
            return Ok(self
                .unresolved("classification", &s, stuck)?
                .map(|()| unreachable!()));
        };
        room(self.splits, self.options.max_splits, "splits")?;
        self.splits += 1;
        let then = match self.classify(s.pinned(&on, true))? {
            Ok(r) => r,
            Err(p) => return Ok(Err(p)),
        };
        let otherwise = match self.classify(s.pinned(&on, false))? {
            Ok(r) => r,
            Err(p) => return Ok(Err(p)),
        };
        Ok(Ok(Region {
            nodes,
            next: Next::Split {
                on,
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            },
        }))
    }
    /// Proved constants by key. H itself is never substituted: it is computed
    /// from its definition and tested.
    fn keyed(&mut self, constants: Vec<(GroundAtom, bool)>) -> Result<BTreeMap<AtomKey, bool>> {
        let mut out = BTreeMap::new();
        for (a, v) in constants {
            self.work.tick(1)?;
            if let Some(k) = self.keys_of.get(&a) {
                if !self.inputs.contains(k) && self.hypothesis.as_ref() != Some(k) {
                    out.insert(k.clone(), v);
                }
            }
        }
        Ok(out)
    }
    fn discharged(
        &mut self,
        s: &State,
        outputs: Option<&BTreeSet<GroundAtom>>,
        hypothesis: bool,
        substituted: &BTreeMap<AtomKey, bool>,
    ) -> Result<q::Discharge> {
        room(self.calls, self.options.max_oracle_calls, "oracle calls")?;
        self.calls += 1;
        let path = self.runtime(s);
        let constants: Vec<_> = substituted
            .iter()
            .map(|(k, v)| (self.atoms[k].clone(), *v))
            .collect();
        self.engine
            .planning_discharged(&path, outputs, hypothesis, &constants)
    }
    /// Processing for an accepted leaf's path; checks from classification stay
    /// in force, and only constants with implied definitions are substituted.
    fn accept(&mut self, mut s: State) -> Step<Accepted> {
        let mut nodes = BTreeMap::new();
        let outputs = self.output_atoms.clone();
        let hypothesis = self.hypothesis.is_some();
        let constants = match self.oracle(&s, Some(&outputs), hypothesis)? {
            PathStep::Empty => {
                // Reachable by an accepted message at all?
                let reach = if hypothesis {
                    self.oracle(&s, None, true)?
                } else {
                    self.oracle(&s, Some(&BTreeSet::new()), false)?
                };
                return Ok(match reach {
                    PathStep::Empty => Ok(Accepted {
                        nodes,
                        next: AcceptedNext::Unreachable,
                    }),
                    PathStep::Inconclusive(cause) => Err(Problem::PathInconclusive {
                        path: s.path(),
                        cause,
                    }),
                    PathStep::Forced { .. } => Err(Problem::MeaningFailure { path: s.path() }),
                });
            }
            PathStep::Inconclusive(cause) => {
                return Ok(Err(Problem::PathInconclusive {
                    path: s.path(),
                    cause,
                }));
            }
            PathStep::Forced { constants } => self.keyed(constants)?,
        };
        let targets = self.outputs.clone();
        // With the proved constants first; if their substitution is not implied
        // (nothing may reject after acceptance), again without them.
        let entry = (s.clone(), nodes.clone(), self.nodes);
        let mut stuck = vec![];
        for substitute in [true, false] {
            (s, nodes, self.nodes) = entry.clone();
            let mut substituted = BTreeMap::new();
            if substitute {
                if constants.is_empty() {
                    continue;
                }
                self.substitute(&mut s, &constants, Some(&mut substituted), &mut nodes)?;
            }
            stuck = self.settle(&mut s, &targets, false, &mut nodes)?;
            if !stuck.is_empty() {
                if substitute {
                    continue;
                }
                break;
            }
            let scope = self.output_scope.clone();
            let odd = self.odd_remainder(&s, &scope)?;
            if !odd.is_empty() {
                if substitute {
                    continue;
                }
                return Ok(self
                    .unresolved("processing", &s, odd)?
                    .map(|()| unreachable!()));
            }
            if !substituted.is_empty() {
                match self.discharged(&s, Some(&outputs), hypothesis, &substituted)? {
                    q::Discharge::Implied => {}
                    q::Discharge::NotImplied => continue,
                    q::Discharge::Inconclusive(cause) => {
                        return Ok(Err(Problem::PathInconclusive {
                            path: s.path(),
                            cause,
                        }));
                    }
                }
            }
            return Ok(Ok(Accepted {
                nodes,
                next: AcceptedNext::Return,
            }));
        }
        let Some(on) = self.split_input(&s, &stuck)? else {
            return Ok(self
                .unresolved("processing", &s, stuck)?
                .map(|()| unreachable!()));
        };
        room(self.splits, self.options.max_splits, "splits")?;
        self.splits += 1;
        let then = match self.accept(s.pinned(&on, true))? {
            Ok(a) => a,
            Err(p) => return Ok(Err(p)),
        };
        let otherwise = match self.accept(s.pinned(&on, false))? {
            Ok(a) => a,
            Err(p) => return Ok(Err(p)),
        };
        Ok(Ok(Accepted {
            nodes,
            next: AcceptedNext::Split {
                on,
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            },
        }))
    }
}
/// Strongly connected component per node (Kosaraju, iterative).
fn components(edges: &[Vec<usize>]) -> Vec<usize> {
    let n = edges.len();
    let mut order = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    for start in 0..n {
        if seen[start] {
            continue;
        }
        let mut stack = vec![(start, 0)];
        seen[start] = true;
        while let Some((v, i)) = stack.pop() {
            if i < edges[v].len() {
                stack.push((v, i + 1));
                let w = edges[v][i];
                if !seen[w] {
                    seen[w] = true;
                    stack.push((w, 0));
                }
            } else {
                order.push(v);
            }
        }
    }
    let mut reverse = vec![vec![]; n];
    for (v, ws) in edges.iter().enumerate() {
        for w in ws {
            reverse[*w].push(v);
        }
    }
    let mut component = vec![usize::MAX; n];
    let mut next = 0;
    for &start in order.iter().rev() {
        if component[start] != usize::MAX {
            continue;
        }
        let mut stack = vec![start];
        component[start] = next;
        while let Some(v) = stack.pop() {
            for w in &reverse[v] {
                if component[*w] == usize::MAX {
                    component[*w] = next;
                    stack.push(*w);
                }
            }
        }
        next += 1;
    }
    component
}
