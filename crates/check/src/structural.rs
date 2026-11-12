//! Assumption-blind syntactic reductions of the current, justified snapshot.
//! No BDD context is built. Certificates share a flat DAG rather than cloning
//! a settling chain into every removal (or recursively dropping a deep chain).
use crate::{
    limits::{Budget, Result},
    *,
};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

// Optimization cutoffs, not semantic allowances: exceeding one skips comparison.
const UNFOLD_DEPTH: usize = 32;
const UNFOLD_SIZE: usize = 128;
const SUBSET_CANDIDATES: usize = 64;

#[derive(Debug, Clone)]
pub enum StructuralReason {
    TrueHead {
        atom: GroundAtom,
    },
    Dead {
        literal: GroundLiteral,
    },
    Subsumed {
        by: GroundRuleId,
        unfolded: Vec<GroundRuleId>,
        settled: Vec<GroundAtom>,
    },
}
#[derive(Debug, Clone)]
struct Fact {
    value: bool,
    producer: Option<GroundRuleId>,
    removed: Vec<GroundRuleId>,
    // Concrete absence precedes private rule removal. In particular, a positive
    // cycle may be false before its own producers are marked dead. Preserve the
    // explanation's origin rather than inferring it from later removal reasons.
    concrete: bool,
}
#[derive(Debug)]
pub struct StructuralCertificate {
    facts: BTreeMap<GroundAtom, Fact>,
    reasons: BTreeMap<GroundRuleId, StructuralReason>,
    rules: BTreeMap<GroundRuleId, GroundRule>,
}
#[derive(Debug, Clone)]
pub struct StructuralProof {
    pub candidate: GroundRule,
    pub reason: StructuralReason,
    certificate: Arc<StructuralCertificate>,
}
/// A direct explanation of an already settled atom, read from its certificate.
/// Absence is not synonymous with having no authored producers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructuralSettlement {
    Producer,
    NoProducer,
    ProducersRemoved,
    NoDerivation,
}

#[cfg(any(test, feature = "test-support"))]
thread_local! {
    static SUPPORT_EXPANSIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn support_expansions() -> usize {
    SUPPORT_EXPANSIONS.get()
}

impl StructuralProof {
    pub fn settlement(&self, atom: &GroundAtom) -> (bool, StructuralSettlement) {
        let fact = &self.certificate.facts[atom];
        let reason = if fact.producer.is_some() {
            StructuralSettlement::Producer
        } else if fact.removed.is_empty() {
            StructuralSettlement::NoProducer
        } else if fact.concrete {
            StructuralSettlement::NoDerivation
        } else {
            StructuralSettlement::ProducersRemoved
        };
        (fact.value, reason)
    }

    /// Immediate settling producers, excluded producers and unfolding rules.
    /// Does not walk their premises or recursively expand removal reasons.
    pub fn direct_rules(&self) -> Vec<&GroundRule> {
        let mut atoms = Vec::new();
        let mut rules = Vec::new();
        reason_inputs(&self.reason, &mut atoms, &mut rules);
        for atom in atoms {
            if let Some(fact) = self.certificate.facts.get(&atom) {
                rules.extend(fact.producer);
                rules.extend(&fact.removed);
            }
        }
        let mut rules: Vec<_> = rules
            .into_iter()
            .filter_map(|id| self.certificate.rules.get(&id))
            .collect();
        rules.sort_by_key(|r| (r.source, r.id));
        rules.dedup_by_key(|r| r.id);
        rules
    }

    /// Current snapshot rules supporting this proof, including unfolding and
    /// transitive settling evidence. Never used as executable dependency edges.
    pub fn supporting_rules(&self) -> Vec<&GroundRule> {
        #[cfg(any(test, feature = "test-support"))]
        SUPPORT_EXPANSIONS.set(SUPPORT_EXPANSIONS.get() + 1);
        let (_, rules) = closure(
            &self.certificate.facts,
            &self.certificate.reasons,
            |id| self.certificate.rules.get(&id),
            std::iter::once(&self.reason),
            |_| Ok(()),
        )
        .expect("unbounded evidence traversal");
        let mut rules: Vec<_> = rules
            .into_iter()
            .filter_map(|id| self.certificate.rules.get(&id))
            .collect();
        // Fold binding can allocate different ground IDs. Source order keeps
        // related locations identical on both preparation paths.
        rules.sort_by_key(|r| (r.source, r.id));
        rules
    }
}
fn reason_inputs(
    reason: &StructuralReason,
    atoms: &mut Vec<GroundAtom>,
    rules: &mut Vec<GroundRuleId>,
) {
    match reason {
        StructuralReason::TrueHead { atom } => atoms.push(atom.clone()),
        StructuralReason::Dead { literal } => atoms.push(literal.term.atom.clone()),
        StructuralReason::Subsumed {
            by,
            unfolded,
            settled,
        } => {
            rules.push(*by);
            rules.extend(unfolded);
            atoms.extend(settled.iter().cloned());
        }
    }
}
fn closure<'a, 'r>(
    facts: &BTreeMap<GroundAtom, Fact>,
    reasons: &BTreeMap<GroundRuleId, StructuralReason>,
    rule_for: impl Fn(GroundRuleId) -> Option<&'a GroundRule>,
    roots: impl IntoIterator<Item = &'r StructuralReason>,
    mut tick: impl FnMut(&'static str) -> Result<()>,
) -> Result<(BTreeSet<GroundAtom>, BTreeSet<GroundRuleId>)> {
    let mut atoms = Vec::new();
    let mut pending_rules = Vec::new();
    for reason in roots {
        tick("structural certificate")?;
        reason_inputs(reason, &mut atoms, &mut pending_rules);
    }
    let mut seen = BTreeSet::new();
    let mut support = BTreeSet::new();
    loop {
        while let Some(atom) = atoms.pop() {
            tick("structural certificate")?;
            if !seen.insert(atom.clone()) {
                continue;
            }
            if let Some(fact) = facts.get(&atom) {
                if let Some(rule) = fact.producer {
                    pending_rules.push(rule);
                }
                pending_rules.extend(&fact.removed);
            }
        }
        let Some(id) = pending_rules.pop() else {
            break;
        };
        tick("structural certificate")?;
        if !support.insert(id) {
            continue;
        }
        if let Some(reason) = reasons.get(&id) {
            reason_inputs(reason, &mut atoms, &mut pending_rules);
        }
        if let Some(rule) = rule_for(id) {
            for literal in &rule.body {
                tick("structural certificate")?;
                if facts.contains_key(&literal.term.atom) {
                    atoms.push(literal.term.atom.clone());
                }
            }
        }
    }
    Ok((seen, support))
}

type Signed = (GroundAtom, bool);
#[derive(Default)]
struct Expanded {
    body: BTreeSet<Signed>,
    unfolded: BTreeSet<GroundRuleId>,
    settled: BTreeSet<GroundAtom>,
    visited: usize,
}
struct Pass<'a, 'b, 'l> {
    p: &'a GroundProgram,
    budget: &'b mut Budget<'l>,
    active: Vec<bool>,
    targets: BTreeSet<GroundRuleId>,
    producers: Vec<Vec<usize>>,
    count: Vec<usize>,
    readers: Vec<Vec<usize>>,
    facts: BTreeMap<GroundAtom, Fact>,
    reasons: BTreeMap<GroundRuleId, StructuralReason>,
    pending: VecDeque<usize>,
    queued: Vec<bool>,
    dirty: BTreeSet<usize>,
    changed: BTreeSet<usize>,
}
impl Pass<'_, '_, '_> {
    fn queue(&mut self, r: usize) {
        if self.active[r] && !self.queued[r] {
            self.pending.push_back(r);
            self.queued[r] = true;
        }
    }
    fn settle(&mut self, head: usize, value: bool, producer: Option<GroundRuleId>) -> Result<()> {
        let atom = &self.p.atoms[head];
        if self.p.inputs.contains(atom) || self.facts.contains_key(atom) {
            return Ok(());
        }
        self.budget.tick("structural propagation")?;
        let removed = if value {
            vec![]
        } else {
            self.producers[head]
                .iter()
                .map(|r| self.p.rules[*r].id)
                .collect()
        };
        self.facts.insert(
            atom.clone(),
            Fact {
                value,
                producer,
                removed,
                concrete: false,
            },
        );
        self.changed.insert(head);
        // Clone only this adjacency, avoiding a borrow of the entire worklist.
        for r in self.readers[head].clone() {
            self.budget.tick("structural propagation")?;
            self.queue(r);
        }
        if value {
            for r in self.producers[head].clone() {
                self.budget.tick("structural propagation")?;
                self.queue(r);
            }
        }
        Ok(())
    }
    fn value(&mut self, atom: &GroundAtom) -> Option<bool> {
        if let Some(f) = self.facts.get(atom) {
            return Some(f.value);
        }
        let value = self
            .p
            .fixed_value(atom)
            .or_else(|| (!self.p.atom_index.contains_key(atom)).then_some(false))?;
        self.facts.insert(
            atom.clone(),
            Fact {
                value,
                producer: None,
                removed: vec![],
                concrete: true,
            },
        );
        Some(value)
    }
    fn remove(&mut self, r: usize, reason: StructuralReason) -> Result<()> {
        self.budget.tick("structural removal")?;
        self.active[r] = false;
        self.reasons.insert(self.p.rules[r].id, reason);
        let head = self.p.atom_index[&self.p.rules[r].head.atom];
        self.count[head] -= 1;
        if self.count[head] == 0 {
            self.settle(head, false, None)?;
        }
        // Unfolding reads transitive positive producers. Invalidate before any
        // edges are removed; batch removals of one head share this pending set.
        self.changed.insert(head);
        Ok(())
    }
    fn propagate(&mut self) -> Result<()> {
        while let Some(r) = self.pending.pop_front() {
            self.queued[r] = false;
            self.budget.tick("structural propagation")?;
            if !self.active[r] {
                continue;
            }
            let rule = &self.p.rules[r];
            if let Some(f) = self.facts.get(&rule.head.atom) {
                if f.value && f.producer != Some(rule.id) {
                    self.remove(
                        r,
                        StructuralReason::TrueHead {
                            atom: rule.head.atom.clone(),
                        },
                    )?;
                    continue;
                }
            }
            let mut all = true;
            let mut dead = None;
            for literal in &rule.body {
                self.budget.tick("structural propagation")?;
                match self.value(&literal.term.atom) {
                    Some(v) if v != (literal.polarity == Polarity::Positive) => {
                        dead = Some(literal.clone());
                        break;
                    }
                    Some(_) => {}
                    None => all = false,
                }
            }
            if let Some(literal) = dead {
                self.remove(r, StructuralReason::Dead { literal })?;
            } else if all {
                self.settle(self.p.atom_index[&rule.head.atom], true, Some(rule.id))?;
            }
        }
        Ok(())
    }
    fn expand(
        &mut self,
        body: &[GroundLiteral],
        path: &mut BTreeSet<GroundAtom>,
        out: &mut Expanded,
        depth: usize,
    ) -> Result<bool> {
        if depth > UNFOLD_DEPTH {
            return Ok(false);
        }
        for literal in body {
            self.budget.tick("structural unfolding")?;
            out.visited += 1;
            if out.visited > UNFOLD_SIZE {
                return Ok(false);
            }
            let atom = &literal.term.atom;
            let positive = literal.polarity == Polarity::Positive;
            if let Some(v) = self.value(atom) {
                if v != positive {
                    return Ok(false);
                }
                out.settled.insert(atom.clone());
                continue;
            }
            let index = self.p.atom_index[atom];
            if positive && !self.p.inputs.contains(atom) && self.count[index] == 1 {
                if !path.insert(atom.clone()) {
                    return Ok(false);
                }
                let r = *self.producers[index]
                    .iter()
                    .find(|r| self.active[**r])
                    .unwrap();
                out.unfolded.insert(self.p.rules[r].id);
                if !self.expand(&self.p.rules[r].body, path, out, depth + 1)? {
                    return Ok(false);
                }
                path.remove(atom);
            } else {
                out.body.insert((atom.clone(), positive));
            }
        }
        Ok(true)
    }
    fn subsume(&mut self, head: usize) -> Result<bool> {
        if self.count[head] < 2 || self.facts.get(&self.p.atoms[head]).is_some_and(|f| f.value) {
            return Ok(false);
        }
        let mut candidates = Vec::new();
        for r in self.producers[head].clone() {
            self.budget.tick("structural subsumption")?;
            if !self.active[r] {
                continue;
            }
            let mut expanded = Expanded::default();
            if self.expand(
                &self.p.rules[r].body,
                &mut BTreeSet::new(),
                &mut expanded,
                0,
            )? {
                candidates.push((r, expanded));
            }
        }
        self.budget.charge(
            candidates
                .len()
                .saturating_mul(candidates.len().checked_ilog2().unwrap_or(0) as usize + 1),
            "structural candidate ordering",
        )?;
        candidates.sort_by_key(|(r, b)| (b.body.len(), *r));
        let mut exact = BTreeMap::<BTreeSet<Signed>, usize>::new();
        let mut anchors = BTreeMap::<Signed, Vec<usize>>::new();
        let mut removed = false;
        for i in 0..candidates.len() {
            self.budget.tick("structural subsumption")?;
            let (r, b) = &candidates[i];
            let mut cover = exact.get(&b.body).copied();
            let mut inspected = 0;
            if cover.is_none() {
                'search: for literal in &b.body {
                    self.budget.tick("structural subsumption")?;
                    for j in anchors.get(literal).into_iter().flatten() {
                        if inspected == SUBSET_CANDIDATES {
                            break 'search;
                        }
                        inspected += 1;
                        let smaller = &candidates[*j].1.body;
                        self.budget
                            .charge(1 + smaller.len(), "structural subsumption")?;
                        if smaller.is_subset(&b.body) {
                            cover = Some(*j);
                            break 'search;
                        }
                    }
                }
            }
            if let Some(j) = cover {
                let (by, small) = &candidates[j];
                self.remove(
                    *r,
                    StructuralReason::Subsumed {
                        by: self.p.rules[*by].id,
                        unfolded: b.unfolded.union(&small.unfolded).copied().collect(),
                        settled: b.settled.union(&small.settled).cloned().collect(),
                    },
                )?;
                removed = true;
            } else {
                if let Some(anchor) = b.body.first() {
                    anchors.entry(anchor.clone()).or_default().push(i);
                }
                exact.insert(b.body.clone(), i);
            }
        }
        Ok(removed)
    }
    fn fixed_evidence(&mut self, needed: &BTreeSet<GroundAtom>) -> Result<()> {
        let Some(fixed) = &self.p.fixed else {
            return Ok(());
        };
        let mut pending: Vec<_> = needed
            .iter()
            .filter(|a| self.p.fixed_value(a).is_some())
            .cloned()
            .collect();
        let mut seen = BTreeSet::new();
        let mut indexed = BTreeSet::new();
        let mut producers = BTreeMap::<GroundAtom, Vec<GroundRuleId>>::new();
        while let Some(atom) = pending.pop() {
            self.budget.tick("structural fixed evidence")?;
            if !seen.insert(atom.clone()) {
                continue;
            }
            let value = self.p.fixed_value(&atom).expect("fixed boundary");
            let producer = fixed.derivations.get(&atom).and_then(|d| match d.evidence {
                Evidence::Derived { rule, .. } => Some(rule),
                Evidence::Input => None,
            });
            let removed = if value {
                vec![]
            } else {
                let component = fixed.program.component_for(&atom)?;
                if indexed.insert(component.id) {
                    for r in &fixed.program.component_rules[component.id.index] {
                        self.budget.tick("structural fixed evidence")?;
                        let rule = &fixed.program.rules[*r];
                        producers
                            .entry(rule.head.atom.clone())
                            .or_default()
                            .push(rule.id);
                    }
                }
                producers.get(&atom).cloned().unwrap_or_default()
            };
            for id in producer.iter().chain(&removed) {
                let rule = fixed.program.original_rule(*id).expect("fixed producer");
                for l in &rule.body {
                    self.budget.tick("structural fixed evidence")?;
                    if self.p.fixed_value(&l.term.atom).is_some() {
                        pending.push(l.term.atom.clone());
                    } else {
                        self.facts.entry(l.term.atom.clone()).or_insert(Fact {
                            value: false,
                            producer: None,
                            removed: vec![],
                            concrete: true,
                        });
                    }
                }
            }
            self.facts.insert(
                atom,
                Fact {
                    value,
                    producer,
                    removed,
                    concrete: true,
                },
            );
        }
        Ok(())
    }
    fn run(mut self) -> Result<Vec<StructuralProof>> {
        for head in 0..self.p.atoms.len() {
            if self.count[head] == 0 {
                self.settle(head, false, None)?;
            }
        }
        loop {
            self.propagate()?;
            let mut todo: Vec<_> = std::mem::take(&mut self.changed).into_iter().collect();
            let mut seen = BTreeSet::new();
            while let Some(a) = todo.pop() {
                self.budget.tick("structural invalidation")?;
                if !seen.insert(a) {
                    continue;
                }
                self.dirty.insert(a);
                for r in &self.readers[a] {
                    self.budget.tick("structural invalidation")?;
                    if self.active[*r] {
                        todo.push(self.p.atom_index[&self.p.rules[*r].head.atom]);
                    }
                }
            }
            let Some(head) = self.dirty.pop_first() else {
                break;
            };
            self.subsume(head)?;
        }
        if !self.reasons.keys().any(|id| self.targets.contains(id)) {
            return Ok(vec![]);
        }
        let (needed, _) = closure(
            &self.facts,
            &self.reasons,
            |id| self.p.original_rule(id),
            self.reasons
                .iter()
                .filter(|(id, _)| self.targets.contains(id))
                .map(|(_, r)| r),
            |p| self.budget.tick(p),
        )?;
        self.fixed_evidence(&needed)?;
        // Retain one shared certificate, trimmed to the facts/rules reachable
        // from actual removals. Grounded execution/evidence remains untouched.
        // One traversal from all reasons avoids repeating long settling chains.
        let (needed_facts, needed_rules) = closure(
            &self.facts,
            &self.reasons,
            |id| self.p.original_rule(id),
            self.reasons
                .iter()
                .filter(|(id, _)| self.targets.contains(id))
                .map(|(_, r)| r),
            |p| self.budget.tick(p),
        )?;
        let mut rules = BTreeMap::new();
        for id in needed_rules {
            let rule = self.p.original_rule(id).expect("structural source rule");
            self.budget
                .charge(1 + rule.body.len(), "structural certificate storage")?;
            rules.insert(id, rule.clone());
        }
        self.facts.retain(|a, _| needed_facts.contains(a));
        self.reasons
            .retain(|id, _| self.targets.contains(id) || rules.contains_key(id));
        let certificate = Arc::new(StructuralCertificate {
            facts: self.facts,
            reasons: self.reasons,
            rules,
        });
        let mut proofs = Vec::new();
        for (id, reason) in &certificate.reasons {
            if !self.targets.contains(id) {
                continue;
            }
            let candidate = self.p.rules[id.index].clone();
            self.budget
                .charge(1 + candidate.body.len(), "structural proof storage")?;
            proofs.push(StructuralProof {
                candidate,
                reason: reason.clone(),
                certificate: certificate.clone(),
            });
        }
        Ok(proofs)
    }
}

pub(crate) fn reduce(p: &GroundProgram, budget: &mut Budget<'_>) -> Result<Vec<StructuralProof>> {
    // This increment removes only rules whose heads were blocked in this
    // snapshot. Settled regions supply premises, not new rewrite warnings.
    let mut targets = BTreeSet::new();
    for component in &p.components {
        budget.tick("structural targets")?;
        if !component.blocked_by.is_empty() {
            budget.charge(
                p.component_rules[component.id.index].len(),
                "structural targets",
            )?;
            targets.extend(
                p.component_rules[component.id.index]
                    .iter()
                    .map(|r| p.rules[*r].id),
            );
        }
    }
    if targets.is_empty() {
        return Ok(vec![]);
    }
    let mut producers = vec![Vec::new(); p.atoms.len()];
    let mut readers = vec![Vec::new(); p.atoms.len()];
    let mut count = vec![0; p.atoms.len()];
    let mut active = vec![false; p.rules.len()];
    let mut pending = VecDeque::new();
    let mut dirty = BTreeSet::new();
    for (r, rule) in p.rules.iter().enumerate() {
        budget.tick("structural index")?;
        let head = p.atom_index[&rule.head.atom];
        producers[head].push(r);
        if p.rewrites.dropped.contains(&rule.id) {
            continue;
        }
        active[r] = true;
        count[head] += 1;
        pending.push_back(r);
        dirty.insert(head);
        for literal in &rule.body {
            budget.tick("structural index")?;
            if let Some(index) = p.atom_index.get(&literal.term.atom) {
                readers[*index].push(r);
            }
        }
    }
    let (independent, boundary) = p.structural_boundaries(budget)?;
    let mut facts = BTreeMap::new();
    for id in independent {
        for atom in &p.components[id.index].atoms {
            budget.tick("structural boundaries")?;
            let FactState::Settled(value) = boundary.fact(atom)? else {
                unreachable!()
            };
            let producer = boundary.derivation(atom).and_then(|d| match d.evidence {
                Evidence::Derived { rule, .. } => Some(rule),
                Evidence::Input => None,
            });
            let removed = if value {
                vec![]
            } else {
                producers[p.atom_index[atom]]
                    .iter()
                    .map(|r| p.rules[*r].id)
                    .collect()
            };
            facts.insert(
                atom.clone(),
                Fact {
                    value,
                    producer,
                    removed,
                    concrete: true,
                },
            );
        }
    }
    let queued = active.clone();
    Pass {
        p,
        budget,
        active,
        targets,
        producers,
        count,
        readers,
        facts,
        reasons: BTreeMap::new(),
        pending,
        queued,
        dirty,
        changed: BTreeSet::new(),
    }
    .run()
}
