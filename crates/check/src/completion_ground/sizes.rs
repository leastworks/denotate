use super::*;
use crate::{CompletionPreparationSize, CompletionSizes, PossibilityRelation};
use std::collections::HashSet;

pub(super) struct Measurement {
    sink: Option<CompletionSizes>,
    pub data: CompletionPreparationSize,
    least: BTreeMap<RelationId, HashSet<GroundAtom>>,
    work_at: usize,
    work_stage: &'static str,
}
impl Measurement {
    pub fn new(b: &Budget<'_>, static_provider: bool) -> Self {
        Self {
            sink: b.limits.completion_sizes.clone(),
            data: CompletionPreparationSize {
                static_provider,
                ..Default::default()
            },
            least: BTreeMap::new(),
            work_at: b.used(),
            work_stage: "domains",
        }
    }
    pub fn stage(&mut self, name: &'static str, b: &Budget<'_>) {
        if self.enabled() {
            let delta = b.used().saturating_sub(self.work_at);
            self.data.work += delta;
            *self.data.work_by_stage.entry(self.work_stage).or_default() += delta;
            self.work_at = b.used();
            self.work_stage = name;
        }
    }
    pub fn enabled(&self) -> bool {
        self.sink.is_some()
    }
    pub fn least(
        &mut self,
        corpus: &Corpus,
        domains: &Domains,
        inputs: &BTreeSet<GroundAtom>,
        scope: Option<&BTreeSet<RelationId>>,
        b: &mut Budget<'_>,
    ) {
        if !self.enabled() {
            return;
        }
        let mut limits = b.limits.clone();
        limits.completion_sizes = None;
        limits.profile = Default::default();
        // Optional measurement must not inherit a production run's long deadline.
        limits.timeout = limits.timeout.min(std::time::Duration::from_secs(5));
        let profile = b.limits.profile.clone();
        let (tables, seen, result) = b.excluding_time(|| {
            let _span = profile.span("completion size LFP", None);
            let _progress = limits.progress.diagnostic("completion size LFP");
            let mut diagnostic = Budget::new(&limits);
            let mut tables: Upper = corpus
                .relations()
                .map(|r| (r.id, Some(Table::new([]))))
                .collect();
            // Hash membership is never iterated to choose work or examples.
            let mut seen = BTreeMap::<RelationId, HashSet<GroundAtom>>::new();
            let result: Result<()> = (|| {
                for atom in inputs {
                    diagnostic.charge(atom.arguments.len() + 1, "completion size inputs")?;
                    tables
                        .get_mut(&atom.relation)
                        .unwrap()
                        .as_mut()
                        .unwrap()
                        .rows
                        .push(atom.clone());
                    seen.entry(atom.relation).or_default().insert(atom.clone());
                }
                let components = positive_components(corpus, &mut diagnostic)?;
                self.data.components = components.clone();
                let mut producers = BTreeMap::<_, Vec<_>>::new();
                for rule in corpus.rules() {
                    diagnostic.tick("completion size rule index")?;
                    if scope.is_none_or(|s| s.contains(&rule.head.relation())) {
                        producers
                            .entry(rule.head.relation())
                            .or_default()
                            .push(rule);
                    }
                }
                let mut fixed = inputs.len();
                let total = components.len();
                for (index, component) in components.into_iter().enumerate() {
                    if component
                        .iter()
                        .all(|r| corpus.relation(*r).unwrap().role == RelationRole::Input)
                    {
                        continue;
                    }
                    let members: BTreeSet<_> = component.iter().copied().collect();
                    let mut seeds = Vec::new();
                    let mut readers = BTreeMap::<RelationId, Vec<(&Rule, usize)>>::new();
                    for relation in &component {
                        for rule in producers.get(relation).into_iter().flatten() {
                            let mut occurrences = Vec::new();
                            for (i, l) in rule.body.iter().enumerate() {
                                diagnostic.tick("completion size rule partition")?;
                                if let Literal::Positive(a) = l {
                                    if members.contains(&a.relation()) {
                                        occurrences.push((i, a.relation()));
                                    }
                                }
                            }
                            if occurrences.is_empty() {
                                seeds.push(*rule);
                            } else {
                                for (position, relation) in occurrences {
                                    readers.entry(relation).or_default().push((*rule, position));
                                }
                            }
                        }
                    }
                    let mut delta = BTreeMap::<RelationId, Table>::new();
                    let mut round = 0;
                    loop {
                        limits
                            .progress
                            .completion_size(index + 1, total, round + 1, fixed);
                        let mut next = BTreeMap::<RelationId, BTreeSet<GroundAtom>>::new();
                        let mut evaluate =
                            |rule: &Rule, pivot: Option<(usize, &Table)>| -> Result<()> {
                                join_bindings(
                                    rule,
                                    &tables,
                                    domains,
                                    &mut diagnostic,
                                    false,
                                    pivot,
                                    |binding, b| {
                                        let a = ground_atom(&rule.head, binding, b)?.atom;
                                        let present = seen.entry(a.relation).or_default();
                                        if !present.contains(&a) {
                                            b.room(
                                                fixed,
                                                b.limits.max_atoms,
                                                "completion size LFP",
                                                "atoms",
                                            )?;
                                            present.insert(a.clone());
                                            next.entry(a.relation).or_default().insert(a);
                                            fixed += 1;
                                            if fixed % 1024 == 0 {
                                                limits.progress.completion_size(
                                                    index + 1,
                                                    total,
                                                    round + 1,
                                                    fixed,
                                                );
                                            }
                                        }
                                        Ok(())
                                    },
                                )
                            };
                        if round == 0 {
                            for rule in &seeds {
                                evaluate(rule, None)?;
                            }
                        } else {
                            for (relation, new) in &delta {
                                for (rule, position) in readers.get(relation).into_iter().flatten()
                                {
                                    evaluate(rule, Some((*position, new)))?;
                                }
                            }
                        }
                        if next.is_empty() {
                            break;
                        }
                        delta.clear();
                        for (relation, atoms) in next {
                            let table = tables.get_mut(&relation).unwrap().as_mut().unwrap();
                            for atom in &atoms {
                                table.append(atom.clone(), &mut diagnostic)?;
                            }
                            delta.insert(relation, Table::new(atoms));
                        }
                        round += 1;
                    }
                }
                Ok(())
            })();
            if let Err(error) = &result {
                limits.progress.failure(error);
            }
            (tables, seen, result)
        });
        b.excluding_time(|| {
            self.data.least_complete = result.is_ok();
            self.data.least_error = result.err();
            for r in tables.keys() {
                self.data.relations.insert(
                    *r,
                    PossibilityRelation {
                        least: seen.get(r).map_or(0, HashSet::len),
                        circular: self.data.least_complete.then_some(0),
                        ..Default::default()
                    },
                );
            }
            self.least = seen;
            drop(tables);
            for a in inputs {
                self.observe(a);
            }
            for r in corpus.relations().filter(|r| r.role == RelationRole::Input) {
                self.data.relations.get_mut(&r.id).unwrap().fixed = true;
            }
        });
    }
    pub fn round(&mut self, component: &[RelationId]) {
        if !self.enabled() {
            return;
        }
        for r in component {
            let row = self.data.relations.entry(*r).or_default();
            row.observed = 0;
            row.round += 1;
            row.fixed = false;
            row.circular = self.data.least_complete.then_some(0);
            row.example = None;
        }
    }
    // Called once per relation/round, also on a failed join. A complete
    // descending relation table contains the LFP, so cardinalities give the
    // difference without rescanning either table. Partial tables do not.
    pub fn relation(&mut self, relation: RelationId, atoms: &BTreeSet<GroundAtom>, complete: bool) {
        let row = self.data.relations.entry(relation).or_default();
        row.observed = atoms.len();
        row.circular = if self.data.least_complete && (complete || row.least == 0) {
            debug_assert!(atoms.len() >= row.least);
            Some(atoms.len().saturating_sub(row.least))
        } else {
            None
        };
        row.example = None;
        if self.data.least_complete && row.circular != Some(0) {
            // Examples are optional. Bound even this lookup so measurement
            // never scans a huge table hidden from the preparation deadline.
            row.example = atoms
                .iter()
                .take(1024)
                .find(|a| !self.least.get(&relation).is_some_and(|s| s.contains(*a)))
                .cloned();
        }
    }
    pub fn observe(&mut self, atom: &GroundAtom) {
        let row = self.data.relations.entry(atom.relation).or_default();
        row.observed += 1;
        // This helper is only for the already-enumerated eligible input atoms.
        row.circular = self.data.least_complete.then_some(0);
    }
    pub fn fixed(&mut self, component: &[RelationId]) {
        if !self.enabled() {
            return;
        }
        for r in component {
            self.data.relations.get_mut(r).unwrap().fixed = true;
        }
    }
}
impl Drop for Measurement {
    fn drop(&mut self) {
        if let Some(s) = &self.sink {
            s.preparation(std::mem::take(&mut self.data));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    #[test]
    fn diagnostic_deadline_reports_recoverable_cutoff() {
        let mut corpus = Corpus::new();
        corpus
            .declare_relation("p", RelationRole::Derived, [])
            .unwrap();
        let events = Arc::new(Mutex::new(Vec::new()));
        let captured = events.clone();
        let limits = Limits {
            timeout: std::time::Duration::ZERO,
            completion_sizes: Some(CompletionSizes::default()),
            progress: crate::CheckingProgress::new(move |e| captured.lock().unwrap().push(e)),
            ..Default::default()
        };
        let mut budget = Budget::new(&limits);
        let mut measurement = Measurement::new(&budget, false);
        measurement.least(
            &corpus,
            &Domains::new(),
            &BTreeSet::new(),
            None,
            &mut budget,
        );
        assert!(!measurement.data.least_complete);
        assert!(matches!(
            measurement.data.least_error,
            Some(CheckError::Deadline { .. })
        ));
        let events = events.lock().unwrap();
        assert!(
            events
                .iter()
                .any(|e| e.stage == "completion size LFP" && e.state == "started")
        );
        assert!(
            events
                .iter()
                .any(|e| e.stage == "completion size LFP" && e.state == "exhausted" && e.continues)
        );
        assert!(
            events
                .iter()
                .any(|e| e.stage == "completion size LFP" && e.state == "finished")
        );
    }

    #[test]
    fn diagnostic_joins_sparse_anchors_without_expanding_loop_domains() {
        let mut c = Corpus::new();
        let sort = c.declare_sort("S").unwrap();
        let values: Vec<_> = (0..1000)
            .map(|i| c.declare_constant(format!("v{i}"), sort).unwrap())
            .collect();
        let params = || [Parameter::new("x", sort), Parameter::new("y", sort)];
        let input = c
            .declare_relation("anchor", RelationRole::Input, params())
            .unwrap();
        let looping = c
            .declare_relation("loop", RelationRole::Derived, params())
            .unwrap();
        let args = || [Term::variable("X", sort), Term::variable("Y", sort)];
        for source in [looping, input] {
            let head = c.atom(looping, args()).unwrap();
            let body = c.atom(source, args()).unwrap();
            c.add_rule(head, [Literal::Positive(body)]).unwrap();
        }
        let inputs = BTreeSet::from([GroundAtom::new(input, [values[0], values[1]])]);
        let limits = Limits {
            max_atoms: 10,
            max_work: 10_000,
            completion_sizes: Some(CompletionSizes::default()),
            ..Default::default()
        };
        let mut budget = Budget::new(&limits);
        let mut m = Measurement::new(&budget, false);
        m.least(
            &c,
            &Domains::from([(sort, values)]),
            &inputs,
            None,
            &mut budget,
        );
        assert!(m.data.least_complete, "{:?}", m.data.least_error);
        assert_eq!(m.data.relations[&looping].least, 1);
    }

    #[test]
    fn diagnostic_join_refuses_unbound_domain_expansion() {
        let mut c = Corpus::new();
        let s = c.declare_sort("S").unwrap();
        let v = c.declare_constant("v", s).unwrap();
        let r = c
            .declare_relation("r", RelationRole::Derived, [Parameter::new("x", s)])
            .unwrap();
        let a = c.atom(r, [Term::variable("X", s)]).unwrap();
        let body = c.atom(r, [Term::variable("X", s)]).unwrap();
        let id = c.add_rule(a, [Literal::Positive(body)]).unwrap();
        let limits = Limits::default();
        let mut budget = Budget::new(&limits);
        // A symbolic-full table must never slip through the diagnostic path.
        let tables = BTreeMap::from([(r, None)]);
        let mut emitted = false;
        let result = join_bindings(
            c.rule(id).unwrap(),
            &tables,
            &Domains::from([(s, vec![v])]),
            &mut budget,
            false,
            None,
            |_, _| {
                emitted = true;
                Ok(())
            },
        );
        assert!(matches!(
            result,
            Err(CheckError::LimitExceeded {
                resource: "unbound domain enumeration",
                ..
            })
        ));
        assert!(!emitted);
    }
    #[test]
    fn large_sparse_provider_propagates_many_rounds_under_default_limits() {
        let mut c = Corpus::new();
        let s = c.declare_sort("Node").unwrap();
        let values: Vec<_> = (0..8193)
            .map(|i| c.declare_constant(format!("n{i}"), s).unwrap())
            .collect();
        let edge = c
            .declare_relation(
                "edge",
                RelationRole::Derived,
                [Parameter::new("from", s), Parameter::new("to", s)],
            )
            .unwrap();
        let reachable = c
            .declare_relation(
                "reachable",
                RelationRole::Derived,
                [Parameter::new("node", s)],
            )
            .unwrap();
        for pair in values.windows(2) {
            let head = c
                .atom(edge, pair.iter().copied().map(Term::Constant))
                .unwrap();
            c.add_rule(head, []).unwrap();
        }
        let seed = c.atom(reachable, [Term::Constant(values[0])]).unwrap();
        c.add_rule(seed, []).unwrap();
        let x = || Term::variable("X", s);
        let y = || Term::variable("Y", s);
        let head = c.atom(reachable, [y()]).unwrap();
        let previous = c.atom(reachable, [x()]).unwrap();
        let step = c.atom(edge, [x(), y()]).unwrap();
        c.add_rule(head, [Literal::Positive(previous), Literal::Positive(step)])
            .unwrap();
        let limits = Limits {
            completion_sizes: Some(CompletionSizes::default()),
            ..Default::default()
        };
        let mut budget = Budget::new(&limits);
        let mut m = Measurement::new(&budget, true);
        m.least(
            &c,
            &Domains::from([(s, values.clone())]),
            &BTreeSet::new(),
            Some(&BTreeSet::from([edge, reachable])),
            &mut budget,
        );
        assert!(m.data.least_complete, "{:?}", m.data.least_error);
        assert_eq!(m.data.relations[&edge].least, values.len() - 1);
        assert_eq!(m.data.relations[&reachable].least, values.len());
    }

    #[test]
    fn delta_joins_match_exhaustive_transitive_closure_with_two_recursive_occurrences() {
        for bits in 0..16 {
            let mut c = Corpus::new();
            let s = c.declare_sort("S").unwrap();
            let values: Vec<_> = (0..3)
                .map(|i| c.declare_constant(format!("n{i}"), s).unwrap())
                .collect();
            let r = c
                .declare_relation(
                    "reach",
                    RelationRole::Derived,
                    [Parameter::new("x", s), Parameter::new("y", s)],
                )
                .unwrap();
            let mut expected = BTreeSet::new();
            for (i, (a, b)) in [(0, 1), (1, 2), (2, 0), (1, 1)].into_iter().enumerate() {
                if bits & (1 << i) != 0 {
                    expected.insert((a, b));
                    let fact = c
                        .atom(r, [Term::Constant(values[a]), Term::Constant(values[b])])
                        .unwrap();
                    c.add_rule(fact, []).unwrap();
                }
            }
            loop {
                let mut next = expected.clone();
                for &(a, b) in &expected {
                    for &(c, d) in &expected {
                        if b == c {
                            next.insert((a, d));
                        }
                    }
                }
                if next == expected {
                    break;
                }
                expected = next;
            }
            let x = || Term::variable("X", s);
            let y = || Term::variable("Y", s);
            let z = || Term::variable("Z", s);
            let head = c.atom(r, [x(), z()]).unwrap();
            let left = c.atom(r, [x(), y()]).unwrap();
            let right = c.atom(r, [y(), z()]).unwrap();
            c.add_rule(head, [Literal::Positive(left), Literal::Positive(right)])
                .unwrap();
            let limits = Limits {
                completion_sizes: Some(CompletionSizes::default()),
                ..Default::default()
            };
            let mut budget = Budget::new(&limits);
            let mut m = Measurement::new(&budget, false);
            m.least(
                &c,
                &Domains::from([(s, values.clone())]),
                &BTreeSet::new(),
                None,
                &mut budget,
            );
            assert!(m.data.least_complete, "{:?}", m.data.least_error);
            let actual: BTreeSet<_> = m.least.get(&r).into_iter().flatten().cloned().collect();
            assert_eq!(
                actual,
                expected
                    .into_iter()
                    .map(|(a, b)| GroundAtom::new(r, [values[a], values[b]]))
                    .collect()
            );
        }
    }
}
