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
    /// Original instance and its independently settling producer.
    pub instances: Vec<(GroundRuleId, GroundRuleId)>,
}
#[derive(Debug, Clone)]
pub(crate) struct SettledView {
    pub program: GroundProgram,
    pub values: BTreeMap<GroundAtom, SettledAtom>,
    pub origins: Vec<GroundRuleId>,
    pub receipt: WorkReceipt,
}
impl GroundProgram {
    #[cfg(test)]
    pub(crate) fn settle_atoms(&self, limits: &Limits) -> Result<SettledView> {
        self.settle_atoms_accounted(limits).0
    }
    pub(crate) fn settle_atoms_accounted(
        &self,
        limits: &Limits,
    ) -> (Result<SettledView>, WorkReceipt) {
        let mut b = Budget::tracked(limits);
        let _span = limits.profile.span("settled-atoms", None);
        let result = self
            .settle_atoms_inner(&mut b)
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
            result.map(|(program, values, origins)| SettledView {
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
        b: &mut Budget<'_>,
    ) -> Result<(
        GroundProgram,
        BTreeMap<GroundAtom, SettledAtom>,
        Vec<GroundRuleId>,
    )> {
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
        // Keep atoms, including settled false atoms, in the same order. Original
        // interpretations and query pins keep their indices; no truth is lost by deletion.
        graph::analyze(&mut view, b)?;
        b.check("settled view")?;
        Ok((view, values, origins))
    }
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
        let result = (|| {
            for r in &original.core.rules {
                b.tick("subsumed producers")?;
                *totals.entry(r.source).or_insert(0) += 1;
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
