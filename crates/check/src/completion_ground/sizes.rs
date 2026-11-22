use super::*;
use crate::{CompletionPreparationSize, CompletionSizes, PossibilityRelation};

pub(super) struct Measurement {
    sink: Option<CompletionSizes>,
    pub data: CompletionPreparationSize,
    least: Upper,
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
        limits.progress = Default::default();
        let profile = b.limits.profile.clone();
        let (tables, result) = b.excluding_time(|| {
            let _span = profile.span("completion size LFP", None);
            let mut diagnostic = Budget::new(&limits);
            let mut tables: Upper = corpus
                .relations()
                .map(|r| (r.id, Some(Table::new([]))))
                .collect();
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
                }
                let components = positive_components(corpus, &mut diagnostic)?;
                self.data.components = components.clone();
                let mut fixed = inputs.len();
                for component in components {
                    if component
                        .iter()
                        .all(|r| corpus.relation(*r).unwrap().role == RelationRole::Input)
                    {
                        continue;
                    }
                    loop {
                        let mut next = BTreeMap::<RelationId, BTreeSet<GroundAtom>>::new();
                        let mut count = 0;
                        for relation in &component {
                            let out = next.entry(*relation).or_default();
                            for rule in corpus.rules().filter(|r| {
                                r.head.relation() == *relation
                                    && scope.is_none_or(|s| s.contains(relation))
                            }) {
                                bindings(rule, &tables, domains, &mut diagnostic, |binding, b| {
                                    let a = ground_atom(&rule.head, binding, b)?.atom;
                                    if !out.contains(&a) {
                                        b.room(
                                            fixed + count,
                                            b.limits.max_atoms,
                                            "completion size LFP",
                                            "atoms",
                                        )?;
                                        out.insert(a);
                                        count += 1;
                                    }
                                    Ok(())
                                })?;
                            }
                        }
                        let mut equal = true;
                        for (r, atoms) in next {
                            diagnostic.charge(atoms.len() + 1, "completion size LFP")?;
                            equal &= tables[&r].as_ref().unwrap().rows.iter().eq(atoms.iter());
                            tables.insert(r, Some(Table::new(atoms)));
                        }
                        if equal {
                            fixed += count;
                            break;
                        }
                    }
                }
                Ok(())
            })();
            (tables, result)
        });
        b.excluding_time(|| {
            self.data.least_complete = result.is_ok();
            self.data.least_error = result.err();
            for (r, t) in &tables {
                self.data.relations.insert(
                    *r,
                    PossibilityRelation {
                        least: t.as_ref().unwrap().rows.len(),
                        circular: self.data.least_complete.then_some(0),
                        ..Default::default()
                    },
                );
            }
            self.least = tables;
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
    pub fn observe(&mut self, atom: &GroundAtom) {
        if !self.enabled() {
            return;
        }
        let row = self.data.relations.entry(atom.relation).or_default();
        row.observed += 1;
        if self.data.least_complete {
            row.circular.get_or_insert(0);
            let rows = &self.least[&atom.relation].as_ref().unwrap().rows;
            if rows.binary_search(atom).is_err() {
                *row.circular.get_or_insert(0) += 1;
                if row.example.is_none() {
                    row.example = Some(atom.clone());
                }
            }
        }
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
