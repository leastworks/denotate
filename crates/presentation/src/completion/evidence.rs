use super::*;
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

/// Presentation bounds never participate in validation or verdicts. Full models
/// are an explicit diagnostic request; verbose source locations do not enable it.
#[derive(Clone, Copy, Debug)]
pub struct CompletionEvidenceOptions {
    pub full_models: bool,
    pub max_atoms: usize,
}
impl Default for CompletionEvidenceOptions {
    fn default() -> Self {
        Self {
            full_models: false,
            max_atoms: 64,
        }
    }
}
struct Entry {
    model: Model,
    hypothesis: Option<RelationId>,
    targets: BTreeMap<AtomKey, GroundAtom>,
}
pub(super) struct Evidence<'a> {
    options: CompletionEvidenceOptions,
    decisions: Option<&'a BTreeSet<RelationId>>,
    references: bool,
    entries: RefCell<Vec<Entry>>,
}
impl<'a> Evidence<'a> {
    pub fn new(
        options: CompletionEvidenceOptions,
        decisions: Option<&'a BTreeSet<RelationId>>,
        references: bool,
    ) -> Self {
        Self {
            options,
            decisions,
            references,
            entries: RefCell::new(Vec::new()),
        }
    }
    pub fn cap(&self) -> usize {
        if self.options.full_models {
            usize::MAX
        } else {
            self.options.max_atoms
        }
    }
    pub fn observation(&self, w: &Observation, keys: &SemanticKeys) -> Result<Value> {
        let select = |atoms: &BTreeSet<GroundAtom>| -> Result<Vec<Value>> {
            let mut kept = BTreeSet::new();
            for a in atoms {
                kept.insert(AtomKey::from_atom(keys, a)?);
                if kept.len() > self.cap() {
                    kept.pop_last();
                }
            }
            Ok(kept.iter().map(atom_data).collect())
        };
        let present = select(&w.present)?;
        let absent = select(&w.absent)?;
        Ok(
            json!({"omittedPresent":w.present.len()-present.len(),"omittedAbsent":w.absent.len()-absent.len(),"present":present,"absent":absent}),
        )
    }
    pub fn relevant_observation(&self, m: &Model) -> Observation {
        let mut w = m.observation();
        if !self.options.full_models {
            if let Some(scope) = m.scope_atoms() {
                w.present.retain(|a| scope.contains(a));
                w.absent.retain(|a| scope.contains(a));
            }
        }
        w
    }
    pub fn difference(&self, p: &Pair) -> Option<GroundAtom> {
        p.first
            .differing_atoms(&p.second)
            .find(|a| self.decisions.is_none_or(|d| d.contains(&a.relation)))
            .cloned()
    }
    fn select_targets(
        &self,
        selected: &mut BTreeMap<AtomKey, GroundAtom>,
        targets: &[GroundAtom],
        keys: &SemanticKeys,
    ) -> Result<()> {
        for atom in targets {
            selected.insert(AtomKey::from_atom(keys, atom)?, atom.clone());
            if selected.len() > self.cap() {
                selected.pop_last();
            }
        }
        Ok(())
    }
    pub fn model(
        &self,
        m: &Model,
        keys: &SemanticKeys,
        h: Option<RelationId>,
        targets: &[GroundAtom],
    ) -> Result<Value> {
        if !self.references {
            let mut selected = BTreeMap::new();
            self.select_targets(&mut selected, targets, keys)?;
            return self.data(m, keys, h, &selected.into_values().collect());
        }
        let mut entries = self.entries.borrow_mut();
        let index = entries
            .iter()
            .position(|e| e.hypothesis == h && e.model.same_interpretation(m))
            .unwrap_or_else(|| {
                entries.push(Entry {
                    model: m.clone(),
                    hypothesis: h,
                    targets: BTreeMap::new(),
                });
                entries.len() - 1
            });
        self.select_targets(&mut entries[index].targets, targets, keys)?;
        Ok(json!({"kind":"completion-model-reference","modelRef":format!("m{index}")}))
    }
    pub fn finish(&self, keys: &SemanticKeys) -> Result<Value> {
        let models = self
            .entries
            .borrow()
            .iter()
            .enumerate()
            .map(|(i, e)| {
                Ok((
                    format!("m{i}"),
                    self.data(
                        &e.model,
                        keys,
                        e.hypothesis,
                        &e.targets.values().cloned().collect(),
                    )?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        Ok(
            json!({"version":1,"fullModels":self.options.full_models,"maxAtoms":if self.options.full_models{None}else{Some(self.options.max_atoms)},"models":models}),
        )
    }
    fn data(
        &self,
        m: &Model,
        keys: &SemanticKeys,
        h: Option<RelationId>,
        targets: &BTreeSet<GroundAtom>,
    ) -> Result<Value> {
        // Keep only the selected decisions and relevant cone in the default
        // view. Even a large cone stays bounded without allocating all AtomKeys.
        let observation = m.observation();
        let input =
            |a: &GroundAtom| observation.present.contains(a) || observation.absent.contains(a);
        let mut kept = BTreeMap::new();
        let mut total = 0usize;
        let mut projected_out = 0usize;
        for (a, v) in m.interpretation() {
            let is_input = input(a);
            let relevant_input = m.scope_atoms().is_none_or(|s| s.contains(a));
            let selected = self.decisions.is_none_or(|s| s.contains(&a.relation));
            let decision_scope = matches!(
                m.scope(),
                ModelScope::Classification
                    | ModelScope::ClassificationWithoutHypothesis
                    | ModelScope::Processing
            );
            if !self.options.full_models
                && !targets.contains(a)
                && ((is_input && !relevant_input) || (!is_input && decision_scope && !selected))
            {
                projected_out += 1;
                continue;
            }
            total += 1;
            let key = AtomKey::from_atom(keys, a)?;
            kept.insert((!targets.contains(a), key), v);
            if kept.len() > self.cap() {
                kept.pop_last();
            }
        }
        let mut rows: Vec<_> = kept.into_iter().map(|((_, k), v)| (k, v)).collect();
        rows.sort_by(|a, b| a.0.cmp(&b.0));
        let w = Observation {
            present: observation
                .present
                .into_iter()
                .filter(|a| {
                    self.options.full_models || m.scope_atoms().is_none_or(|s| s.contains(a))
                })
                .collect(),
            absent: observation
                .absent
                .into_iter()
                .filter(|a| {
                    self.options.full_models || m.scope_atoms().is_none_or(|s| s.contains(a))
                })
                .collect(),
        };
        Ok(
            json!({"kind":"completion-model","scope":match m.scope(){ModelScope::Classification=>"hypothesis-cone",ModelScope::ClassificationWithoutHypothesis=>"classification-without-hypothesis",ModelScope::Processing=>"accepted-processing",ModelScope::Property=>"property-cone",ModelScope::WholeProgram=>"whole-program",ModelScope::Assumption=>"assumption-cone",ModelScope::InputDomain=>"input-domain-cone"},
                "hypothesis":h.map(|r|atom(&GroundAtom::new(r,[]),keys)).transpose()?,
                "observation":self.observation(&w,keys)?,
                "omittedInputRelations":m.omitted_input_relations().iter().map(|r|keys.relation(*r).map(crate::identity::relation)).collect::<std::result::Result<Vec<_>,_>>()?,
                "projection":if self.options.full_models{"full-scope"}else{"relevant-cone-and-decisions"},
                "projectedOutAtoms":projected_out,"omittedAtoms":total-rows.len(),
                "interpretation":rows.iter().map(|(a,v)|json!({"atom":atom_data(a),"value":v})).collect::<Vec<_>>(),
                "scopeAtoms": if self.options.full_models {m.scope_atoms().map(|s|s.iter().map(|a|atom(a,keys)).collect::<Result<Vec<_>>>()).transpose()?} else {None},
                "scopeAtomsComplete":self.options.full_models,
            }),
        )
    }
}
