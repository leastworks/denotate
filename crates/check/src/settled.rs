//! Assumption-independent propagation on the already grounded residual graph.
//! This view is never installed as an ordinary admission rewrite.
use crate::{
    graph,
    limits::{Budget, Result},
    *,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone)]
pub enum SettledReason {
    /// Valid only under the explicit input context used for this view.
    InputPin,
    Producer(GroundRuleId),
    /// One independently violated premise for every original producer.
    DeadProducers(Vec<(GroundRuleId, usize)>),
}
#[derive(Debug, Clone)]
pub struct SettledAtom {
    pub value: bool,
    pub reason: SettledReason,
}
#[derive(Debug, Clone)]
pub struct SubsumedProducer {
    pub rule: denotate_ir::RuleId,
    pub total_instances: usize,
    pub syntactic: bool,
    /// Original instance and its settling or syntactically subsuming producer.
    pub instances: Vec<(GroundRuleId, GroundRuleId)>,
}
#[derive(Debug, Clone)]
pub(crate) struct SettledView {
    pub program: GroundProgram,
    pub values: BTreeMap<GroundAtom, SettledAtom>,
    pub origins: Vec<GroundRuleId>,
    pub receipt: WorkReceipt,
    pub syntactic: Vec<(GroundRuleId, GroundRuleId)>,
}
impl GroundProgram {
    #[cfg(test)]
    pub(crate) fn settle_atoms(&self, limits: &Limits) -> Result<SettledView> {
        self.settle_atoms_accounted(None, limits).0
    }
    pub(crate) fn settle_atoms_accounted(
        &self,
        keys: Option<&denotate_ir::SemanticKeys>,
        limits: &Limits,
    ) -> (Result<SettledView>, WorkReceipt) {
        let mut b = Budget::tracked(limits);
        let _span = limits.profile.span("settled-atoms", None);
        let result = self
            .settle_atoms_inner(keys, &mut b)
            .map_err(|e| e.in_phase("settled atoms", None));
        if let Err(e) = &result {
            b.failure(e);
        }
        let receipt = WorkReceipt {
            allowance: limits.into(),
            own: b.snapshot(),
            dependencies: BTreeSet::from([QueryKey::ResidualPreparation]),
        };
        (
            result.map(|(program, values, origins, syntactic)| SettledView {
                syntactic,
                program,
                values,
                origins,
                receipt: receipt.clone(),
            }),
            receipt,
        )
    }
    fn settle_atoms_inner(
        &self,
        keys: Option<&denotate_ir::SemanticKeys>,
        b: &mut Budget<'_>,
    ) -> Result<(
        GroundProgram,
        BTreeMap<GroundAtom, SettledAtom>,
        Vec<GroundRuleId>,
        Vec<(GroundRuleId, GroundRuleId)>,
    )> {
        self.settle_atoms_with_inputs(keys, &BTreeMap::new(), b)
    }
    pub(crate) fn settle_atoms_with_inputs(
        &self,
        keys: Option<&denotate_ir::SemanticKeys>,
        pins: &BTreeMap<GroundAtom, bool>,
        b: &mut Budget<'_>,
    ) -> Result<(
        GroundProgram,
        BTreeMap<GroundAtom, SettledAtom>,
        Vec<GroundRuleId>,
        Vec<(GroundRuleId, GroundRuleId)>,
    )> {
        for atom in pins.keys() {
            b.tick("settled input pins")?;
            if !self.inputs.contains(atom) {
                return Err(CheckError::InvalidRequest(
                    "settlement pins must be represented inputs",
                ));
            }
        }
        b.charge(
            self.core.atoms.len() + self.core.rules.len(),
            "settled index",
        )?;
        let n = self.core.atoms.len();
        let mut values: Vec<Option<SettledAtom>> = vec![None; n];
        let mut producers = vec![Vec::new(); n];
        let mut readers = vec![Vec::new(); n];
        let mut pending = vec![0usize; self.core.rules.len()];
        let mut dead = vec![None; self.core.rules.len()];
        let mut alive = vec![0usize; n];
        for (i, r) in self.core.rules.iter().enumerate() {
            b.tick("settled producers")?;
            let head = self.atom_index[&r.head.atom];
            producers[head].push(i);
            for (j, l) in r.body.iter().enumerate() {
                b.tick("settled premises")?;
                let known = self
                    .fixed_value(&l.term.atom)
                    .or_else(|| (!self.atom_index.contains_key(&l.term.atom)).then_some(false));
                if let Some(v) = known {
                    if v != (l.polarity == Polarity::Positive) && dead[i].is_none() {
                        dead[i] = Some(j);
                    }
                } else {
                    let atom = self.atom_index[&l.term.atom];
                    readers[atom].push((i, j));
                    pending[i] += 1;
                }
            }
            if dead[i].is_none() {
                alive[head] += 1;
            }
        }
        let mut queue = VecDeque::new();
        for i in 0..n {
            b.tick("settled seeds")?;
            if self.inputs.contains(&self.core.atoms[i]) {
                if let Some(value) = pins.get(&self.core.atoms[i]) {
                    values[i] = Some(SettledAtom {
                        value: *value,
                        reason: SettledReason::InputPin,
                    });
                    queue.push_back(i);
                }
                continue;
            }
            if let Some(r) = producers[i]
                .iter()
                .find(|r| dead[**r].is_none() && pending[**r] == 0)
            {
                values[i] = Some(SettledAtom {
                    value: true,
                    reason: SettledReason::Producer(self.core.rules[*r].id),
                });
            } else if alive[i] == 0 {
                values[i] = Some(SettledAtom {
                    value: false,
                    reason: SettledReason::DeadProducers(
                        producers[i]
                            .iter()
                            .map(|r| (self.core.rules[*r].id, dead[*r].unwrap()))
                            .collect(),
                    ),
                });
            }
            if values[i].is_some() {
                queue.push_back(i);
            }
        }
        while let Some(atom) = queue.pop_front() {
            let v = values[atom].as_ref().unwrap().value;
            for &(r, occurrence) in &readers[atom] {
                b.tick("settled propagation")?;
                if dead[r].is_some() {
                    continue;
                }
                let rule = &self.core.rules[r];
                let head = self.atom_index[&rule.head.atom];
                if v != (rule.body[occurrence].polarity == Polarity::Positive) {
                    dead[r] = Some(occurrence);
                    alive[head] -= 1;
                } else {
                    pending[r] -= 1;
                }
                if values[head].is_some() || self.inputs.contains(&self.core.atoms[head]) {
                    continue;
                }
                let reason = if alive[head] == 0 {
                    Some(SettledAtom {
                        value: false,
                        reason: SettledReason::DeadProducers(
                            producers[head]
                                .iter()
                                .map(|r| (self.core.rules[*r].id, dead[*r].unwrap()))
                                .collect(),
                        ),
                    })
                } else if dead[r].is_none() && pending[r] == 0 {
                    Some(SettledAtom {
                        value: true,
                        reason: SettledReason::Producer(rule.id),
                    })
                } else {
                    None
                };
                if reason.is_some() {
                    values[head] = reason;
                    queue.push_back(head);
                }
            }
        }
        let values: BTreeMap<_, _> = self
            .core
            .atoms
            .iter()
            .cloned()
            .zip(values)
            .filter_map(|(a, v)| v.map(|v| (a, v)))
            .collect();
        b.charge(
            self.core.rules.iter().map(|r| r.body.len() + 1).sum(),
            "settled view",
        )?;
        let mut view = self.clone();
        let original = std::mem::take(&mut view.rules);
        let mut origins = Vec::new();
        for mut r in original {
            if let Some(v) = values.get(&r.head.atom) {
                if !matches!(v.reason, SettledReason::Producer(id) if id == r.id) {
                    continue;
                }
                r.body.clear();
            } else {
                if dead[r.id.index].is_some() {
                    continue;
                }
                r.body.retain(|l| {
                    !values.contains_key(&l.term.atom)
                        && self.fixed_value(&l.term.atom).is_none()
                        && self.atom_index.contains_key(&l.term.atom)
                });
            }
            origins.push(r.id);
            r.id.index = view.rules.len();
            view.rules.push(r);
        }
        let syntactic = subsume(&mut view, &mut origins, self, keys, b)?;
        // Keep atoms, including settled false atoms, in the same order. Original
        // interpretations and query pins keep their indices; no truth is lost by deletion.
        graph::analyze(&mut view, b)?;
        b.check("settled view")?;
        Ok((view, values, origins, syntactic))
    }
}

/// Subset elimination on the propagated bodies. Shortest bodies first means a
/// retained survivor cannot itself be removed later. Equal bodies keep the first
/// semantic source/grounding key. No correlation or selected assumptions enter.
fn subsume(
    view: &mut GroundProgram,
    origins: &mut Vec<GroundRuleId>,
    original: &GroundProgram,
    keys: Option<&denotate_ir::SemanticKeys>,
    b: &mut Budget<'_>,
) -> Result<Vec<(GroundRuleId, GroundRuleId)>> {
    let mut heads = BTreeMap::<_, Vec<_>>::new();
    for (i, r) in view.rules.iter().enumerate() {
        b.tick("syntactic subsumption index")?;
        heads.entry(r.head.atom.clone()).or_default().push(i);
    }
    let mut dropped = BTreeMap::new();
    // Optional optimization: stop comparing after this aggregate pair allowance.
    // Already established subset removals remain sound; unvisited rules survive.
    let mut pairs = 100_000usize;
    let mut ordered = Vec::new();
    for (a, candidates) in heads {
        if candidates.len() < 2 {
            continue;
        }
        // Bare stable queries historically accept partially keyed corpora. This
        // optional optimization cannot turn missing presentation keys into a
        // preparation error or choose an arena-order duplicate survivor.
        let key = match keys.map(|keys| AtomKey::from_atom(keys, &a)).transpose() {
            Ok(key) => key,
            Err(denotate_ir::KeyError::MissingBinding(_)) => continue,
            Err(e) => return Err(e.into()),
        };
        ordered.push((key, a, candidates));
    }
    ordered.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    'heads: for (_, _, indices) in ordered {
        if pairs == 0 {
            break;
        }
        // Only one head's body sets and grounding keys are live at a time.
        let mut candidates = Vec::new();
        for i in indices {
            let r = &view.rules[i];
            b.charge(r.body.len() + 1, "syntactic subsumption bodies")?;
            let body = r
                .body
                .iter()
                .map(|l| (l.term.atom.clone(), l.polarity == Polarity::Positive))
                .collect::<BTreeSet<_>>();
            candidates.push((i, body));
        }
        let mut order = BTreeMap::new();
        for (i, _) in candidates.iter() {
            let r = original.original_rule(origins[*i]).unwrap();
            b.charge(r.body.len() + 1, "syntactic subsumption keys")?;
            let key = keys
                .map(|keys| -> Result<_> {
                    Ok((
                        keys.rule(r.source)?.clone(),
                        std::iter::once(&r.head.atom)
                            .chain(r.body.iter().map(|l| &l.term.atom))
                            .map(|a| AtomKey::from_atom(keys, a).map_err(CheckError::from))
                            .collect::<Result<Vec<_>>>()?,
                    ))
                })
                .transpose();
            let key = match key {
                Ok(key) => key,
                Err(CheckError::Keys(denotate_ir::KeyError::MissingBinding(_))) => continue 'heads,
                Err(e) => return Err(e),
            };
            order.insert(*i, key);
        }
        candidates.sort_by(|(i, a), (j, c)| {
            a.len()
                .cmp(&c.len())
                .then_with(|| order[i].cmp(&order[j]))
                .then(i.cmp(j))
        });
        let mut survivors: Vec<usize> = Vec::new();
        for n in 0..candidates.len() {
            let (i, body) = &candidates[n];
            let mut support = None;
            for &s in &survivors {
                if pairs == 0 {
                    break;
                }
                pairs -= 1;
                let (j, other) = &candidates[s];
                b.charge(other.len() + 1, "syntactic subsumption")?;
                if other.is_subset(body) {
                    support = Some(*j);
                    break;
                }
            }
            if let Some(j) = support {
                dropped.insert(*i, j);
            } else {
                survivors.push(n);
            }
        }
    }
    let evidence = dropped
        .iter()
        .map(|(i, j)| (origins[*i], origins[*j]))
        .collect();
    if !dropped.is_empty() {
        let old = std::mem::take(&mut view.rules);
        let old_origins = std::mem::take(origins);
        for (i, mut r) in old.into_iter().enumerate() {
            if dropped.contains_key(&i) {
                continue;
            }
            r.id.index = view.rules.len();
            view.rules.push(r);
            origins.push(old_origins[i]);
        }
    }
    Ok(evidence)
}

impl SettledView {
    /// Diagnostic work only. Losing this allowance never changes semantic results.
    pub(crate) fn subsumed(
        &self,
        original: &GroundProgram,
        limits: &Limits,
    ) -> Result<(Vec<SubsumedProducer>, Option<Inconclusive>)> {
        let mut b = Budget::new(limits);
        let mut totals = BTreeMap::new();
        let mut found = BTreeMap::<_, Vec<_>>::new();
        let mut syntactic_sources = BTreeSet::new();
        let result = (|| {
            for r in &original.core.rules {
                b.tick("subsumed producers")?;
                *totals.entry(r.source).or_insert(0) += 1;
            }
            for (candidate, survivor) in &self.syntactic {
                b.tick("subsumed producers")?;
                let r = original.original_rule(*candidate).unwrap();
                syntactic_sources.insert(r.source);
                found
                    .entry(r.source)
                    .or_default()
                    .push((*candidate, *survivor));
            }
            for r in &original.core.rules {
                b.tick("subsumed producers")?;
                let Some(SettledAtom {
                    value: true,
                    reason: SettledReason::Producer(producer),
                }) = self.values.get(&r.head.atom)
                else {
                    continue;
                };
                if *producer == r.id || r.body.is_empty() {
                    continue;
                }
                let mut seen = BTreeSet::new();
                let mut todo = vec![r.head.atom.clone()];
                let mut independent = true;
                while let Some(a) = todo.pop() {
                    b.tick("subsumption support")?;
                    if !seen.insert(a.clone()) {
                        continue;
                    }
                    let Some(value) = self.values.get(&a) else {
                        continue;
                    }; // independent fixed cone
                    match &value.reason {
                        SettledReason::InputPin => {
                            independent = false;
                            break;
                        }
                        SettledReason::Producer(id) => {
                            let support = original
                                .original_rule(*id)
                                .ok_or(CheckError::Internal("missing settlement producer"))?;
                            if support.source == r.source {
                                independent = false;
                                break;
                            }
                            b.charge(support.body.len(), "subsumption support")?;
                            todo.extend(support.body.iter().map(|l| l.term.atom.clone()));
                        }
                        SettledReason::DeadProducers(dead) => {
                            for (id, premise) in dead {
                                b.tick("subsumption support")?;
                                let support = original
                                    .original_rule(*id)
                                    .ok_or(CheckError::Internal("missing dead producer"))?;
                                if support.source == r.source {
                                    independent = false;
                                    break;
                                }
                                todo.push(support.body[*premise].term.atom.clone());
                            }
                        }
                    }
                    if !independent {
                        break;
                    }
                }
                if independent {
                    found.entry(r.source).or_default().push((r.id, *producer));
                }
            }
            Ok(())
        })();
        let incomplete = match result {
            Ok(()) => None,
            Err(CheckError::Deadline { phase, details }) => Some(Inconclusive {
                phase,
                resource: "deadline",
                details,
            }),
            Err(e) => Some(Inconclusive::from_error(e)?),
        };
        Ok((
            found
                .into_iter()
                .map(|(rule, instances)| SubsumedProducer {
                    rule,
                    total_instances: totals[&rule],
                    syntactic: syntactic_sources.contains(&rule),
                    instances,
                })
                .collect(),
            incomplete,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule, stable_models, subsets};
    use denotate_ir::Corpus;
    #[test]
    fn propagation_preserves_every_stable_model_in_a_tiny_family() {
        for shape in 0..128 {
            let mut c = Corpus::new();
            let x = rel(&mut c, "x", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let candidates = [
                (p, vec![]),
                (p, vec![(x, false)]),
                (p, vec![(q, true)]),
                (q, vec![(p, true)]),
                (q, vec![(p, false)]),
                (q, vec![(q, true)]),
                (p, vec![(p, false)]),
            ];
            for (i, (head, body)) in candidates.iter().enumerate() {
                if shape & (1 << i) != 0 {
                    rule(&mut c, *head, body);
                }
            }
            let original = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
            let view = original.settle_atoms(&Limits::default()).unwrap();
            let atoms: Vec<_> = original.atoms().cloned().collect();
            let inputs: BTreeSet<_> = original.input_atoms().cloned().collect();
            let before: Vec<_> = original.rules().cloned().collect();
            let after: Vec<_> = view.program.rules().cloned().collect();
            for world in subsets(&[atom(x)]) {
                let left = stable_models(&atoms, &inputs, &before, &world);
                let right = stable_models(&atoms, &inputs, &after, &world);
                assert_eq!(left, right, "shape {shape}, world {world:?}");
                for model in left {
                    for (a, value) in &view.values {
                        assert_eq!(model.contains(a), value.value);
                    }
                }
            }
        }
    }
    #[test]
    fn subset_removal_preserves_stable_models_including_recursive_survivors() {
        for shape in 0..256 {
            let mut c = Corpus::new();
            let x = rel(&mut c, "x", true);
            let p = rel(&mut c, "p", false);
            let q = rel(&mut c, "q", false);
            let candidates = [
                (p, vec![(x, false), (q, true)]),
                (p, vec![(x, false)]),
                (p, vec![(x, false)]), // duplicate producer
                (q, vec![(p, true)]),
                (p, vec![(x, false), (q, false)]),
                (p, vec![(q, false)]), // recursive survivor
                (q, vec![(p, false)]),
                (q, vec![(x, true), (p, false)]),
            ];
            for (i, (head, body)) in candidates.iter().enumerate() {
                if shape & (1 << i) != 0 {
                    rule(&mut c, *head, body);
                }
            }
            let original = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
            let view = original.settle_atoms(&Limits::default()).unwrap();
            let atoms: Vec<_> = original.atoms().cloned().collect();
            let inputs: BTreeSet<_> = original.input_atoms().cloned().collect();
            let before: Vec<_> = original.rules().cloned().collect();
            let after: Vec<_> = view.program.rules().cloned().collect();
            for world in subsets(&[atom(x)]) {
                assert_eq!(
                    stable_models(&atoms, &inputs, &before, &world),
                    stable_models(&atoms, &inputs, &after, &world),
                    "shape {shape}, world {world:?}"
                );
            }
            let dropped: BTreeSet<_> = view.syntactic.iter().map(|(i, _)| *i).collect();
            assert!(view.syntactic.iter().all(|(_, s)| !dropped.contains(s)));
        }
    }
    #[test]
    fn negative_cycle_is_cut_by_an_independent_producer_but_unknowns_stay_unknown() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        let r = rel(&mut c, "r", false);
        rule(&mut c, p, &[]);
        rule(&mut c, p, &[(x, false)]);
        rule(&mut c, q, &[(p, true), (r, true)]);
        rule(&mut c, r, &[(q, true)]);
        let original = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let v = original.settle_atoms(&Limits::default()).unwrap();
        assert!(v.values[&atom(p)].value);
        assert!(!v.values[&atom(q)].value);
        assert!(v.values[&atom(r)].value);
        assert!(original.components().any(|c| c.cycle.is_some()));
        assert!(v.program.components().all(|c| c.cycle.is_none()));
        assert!(!v.values.contains_key(&atom(x)));
        let mut c = Corpus::new();
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, p, &[(q, true)]);
        rule(&mut c, q, &[(p, true)]);
        let original = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        let v = original.settle_atoms(&Limits::default()).unwrap();
        assert!(v.values.is_empty());
        assert!(v.program.components().any(|c| c.cycle.is_some()));
    }
    #[test]
    fn exhausted_or_cancelled_propagation_publishes_no_view() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let p = rel(&mut c, "p", false);
        rule(&mut c, p, &[(x, false)]);
        let p = GroundProgram::prepare(&c, &Domains::new(), &Limits::default()).unwrap();
        assert!(matches!(
            p.settle_atoms(&Limits {
                max_work: 0,
                ..Limits::default()
            }),
            Err(CheckError::LimitExceeded {
                phase: "settled atoms",
                ..
            })
        ));
        assert!(matches!(
            p.settle_atoms(&Limits {
                timeout: std::time::Duration::ZERO,
                ..Limits::default()
            }),
            Err(CheckError::Deadline { .. })
        ));
        let l = Limits::default();
        l.cancellation.cancel();
        assert!(matches!(p.settle_atoms(&l), Err(CheckError::Cancelled)));
        let complete = p.settle_atoms(&Limits::default()).unwrap();
        let (_, incomplete) = complete
            .subsumed(
                &p,
                &Limits {
                    max_work: 0,
                    ..Limits::default()
                },
            )
            .unwrap();
        assert!(incomplete.is_some());
        assert!(complete.values.is_empty()); // input-dependent p remains unknown
    }
}
