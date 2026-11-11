//! Run-scoped, assumption-independent facts. The original fixed graph is retained
//! as evidence; only the residual graph is executed by admission and checking.
use super::*;
use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

#[path = "fixed_owned.rs"]
mod owned;
pub use owned::*;

#[derive(Debug)]
pub(crate) struct FixedFacts {
    pub program: GroundProgram,
    pub derivations: BTreeMap<GroundAtom, Derivation>,
    pub relations: BTreeSet<denotate_ir::RelationId>,
}

/// A single program snapshot's fold, shared across verifications in this run.
/// This is not a cross-edit cache: handles and provenance belong to `corpus`.
pub struct FixedPreparation<'a> {
    pub(crate) contexts: std::cell::RefCell<Vec<crate::request::SharedContext<'a>>>,
    pub(crate) corpus: &'a denotate_ir::Corpus,
    pub(crate) domains: Domains,
    pub(crate) limits: DeterministicLimits,
    pub(crate) facts: Option<Arc<FixedFacts>>,
    pub(crate) input_domains: BTreeMap<denotate_ir::RelationId, BTreeSet<GroundAtom>>,
    pub(crate) receipt: WorkReceipt,
    pub(crate) transfer_receipts: WorkReceipts,
    pub(super) validation: OnceCell<(
        &'a denotate_ir::SemanticKeys,
        Arc<OriginalAssumptionValidation>,
    )>,
}
impl<'a> FixedPreparation<'a> {
    pub fn prepare(
        corpus: &'a denotate_ir::Corpus,
        domains: &Domains,
        limits: &Limits,
    ) -> Result<Self> {
        let _profile = limits.profile.span("fixed-evaluation", None);
        let mut budget = Budget::tracked(limits);
        // Keep provider validation and its established failure phase intact.
        let domains = validate_domains(corpus, domains, &mut budget)?;
        let input_domains = input_domains::evaluate(corpus, &domains, &mut budget)?;
        let result = (|| {
            let cone = fixed_relations(corpus, &mut budget)?;
            let mut program = GroundProgram::empty(corpus, domains.clone());
            sparse::populate_domain_cone(corpus, &mut program, &mut budget, &cone)?;
            graph::analyze(&mut program, &mut budget)?;
            // Blocked atoms and their consumers stay in the residual program.
            // In particular a fixed-false guard does not prune a negative cycle.
            let settled: BTreeSet<_> = program
                .components
                .iter()
                .filter(|c| c.blocked_by.is_empty())
                .flat_map(|c| c.atoms.iter().cloned())
                .collect();
            let mut relations = cone;
            for atom in &program.atoms {
                if !settled.contains(atom) {
                    relations.remove(&atom.relation);
                }
            }
            if settled.is_empty() {
                return Ok(Self {
                    contexts: Default::default(),
                    transfer_receipts: Default::default(),
                    corpus,
                    domains,
                    limits: limits.into(),
                    facts: None,
                    input_domains,
                    validation: OnceCell::new(),
                    receipt: WorkReceipt {
                        allowance: limits.into(),
                        own: budget.snapshot(),
                        dependencies: BTreeSet::new(),
                    },
                });
            }
            if settled.len() != program.atoms.len() {
                program.atoms.retain(|a| settled.contains(a));
                program.atom_index = program
                    .atoms
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, a)| (a, i))
                    .collect();
                program.rules.retain(|r| settled.contains(&r.head.atom));
                for (i, rule) in program.rules.iter_mut().enumerate() {
                    rule.id.index = i;
                }
                graph::analyze(&mut program, &mut budget)?;
            }
            let derivations = program
                .evaluate_selected([], None, &mut budget)?
                .into_derivations();
            Ok(Self {
                contexts: Default::default(),
                transfer_receipts: Default::default(),
                corpus,
                domains,
                limits: limits.into(),
                facts: Some(Arc::new(FixedFacts {
                    program,
                    derivations,
                    relations,
                })),
                input_domains,
                validation: OnceCell::new(),
                receipt: WorkReceipt {
                    allowance: limits.into(),
                    own: budget.snapshot(),
                    dependencies: BTreeSet::new(),
                },
            })
        })();
        result.map_err(|e: CheckError| e.in_phase("fixed facts", None))
    }

    /// Reuse the sealed original-graph check already performed for this run.
    /// The public, editable diagnostic result is deliberately not accepted here.
    pub fn prepare_with_validation(
        validation: &ValidatedAssumptions<'a>,
        limits: &Limits,
    ) -> Result<Self> {
        if validation.limits != DeterministicLimits::from(limits) {
            return Err(CheckError::InvalidRequest(
                "assumption validation limits do not match fixed preparation",
            ));
        }
        let fixed = Self::prepare(validation.corpus, &validation.domains, limits)?;
        if let Some(original) = &validation.original {
            fixed
                .validation
                .set((validation.keys, original.clone()))
                .expect("new validation cell");
        }
        Ok(fixed)
    }

    pub(crate) fn validate_snapshot(
        &self,
        corpus: &denotate_ir::Corpus,
        domains: &Domains,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        if !std::ptr::eq(corpus, self.corpus)
            || DeterministicLimits::from(budget.limits) != self.limits
            || validate_domains(corpus, domains, budget)? != self.domains
        {
            return Err(CheckError::InvalidRequest(
                "fixed preparation does not match this snapshot, domains or limits",
            ));
        }
        Ok(())
    }

    /// A caller that did not validate declarations still gets exactly the same
    /// original-graph query, initialized on first use and shared by later requests.
    pub(crate) fn original_validation(
        &self,
        keys: &'a denotate_ir::SemanticKeys,
        limits: &Limits,
    ) -> Result<&OriginalAssumptionValidation> {
        limits.cancellation.check()?;
        if self.validation.get().is_none() {
            let original =
                OriginalAssumptionValidation::prepare(self.corpus, &self.domains, keys, limits)?;
            self.validation
                .set((keys, Arc::new(original)))
                .expect("uninitialized validation cell");
        }
        let (source_keys, original) = self.validation.get().unwrap();
        if !std::ptr::eq(*source_keys, keys) {
            return Err(CheckError::InvalidRequest(
                "assumption validation keys do not match this snapshot",
            ));
        }
        Ok(original)
    }
}

fn fixed_relations(
    corpus: &denotate_ir::Corpus,
    budget: &mut Budget<'_>,
) -> Result<BTreeSet<denotate_ir::RelationId>> {
    // Input dependence follows BOTH signs. The possible-tuple grounding
    // SCC graph deliberately follows only positive edges and cannot serve
    // as this classifier.
    let mut readers = BTreeMap::<_, BTreeSet<_>>::new();
    let mut dependent = BTreeSet::new();
    let mut pending = VecDeque::new();
    for relation in corpus.relations() {
        budget.tick("fixed classification")?;
        if relation.role == denotate_ir::RelationRole::Input {
            dependent.insert(relation.id);
            pending.push_back(relation.id);
        }
    }
    for rule in corpus.rules() {
        for literal in &rule.body {
            budget.tick("fixed classification")?;
            readers
                .entry(literal.atom().relation())
                .or_default()
                .insert(rule.head.relation());
        }
    }
    while let Some(provider) = pending.pop_front() {
        for consumer in readers.get(&provider).into_iter().flatten() {
            budget.tick("fixed classification")?;
            if dependent.insert(*consumer) {
                pending.push_back(*consumer);
            }
        }
    }
    let cone: BTreeSet<_> = corpus
        .relations()
        .filter(|r| !dependent.contains(&r.id))
        .map(|r| r.id)
        .collect();
    Ok(cone)
}

impl GroundCore {
    pub(crate) fn fixed_value(&self, atom: &GroundAtom) -> Option<bool> {
        let fixed = self.fixed.as_ref()?;
        fixed
            .program
            .atom_index
            .contains_key(atom)
            .then(|| fixed.derivations.contains_key(atom))
    }
    pub(crate) fn fixed_derivation(&self, atom: &GroundAtom) -> Option<&Derivation> {
        self.fixed.as_ref()?.derivations.get(atom)
    }
    pub(crate) fn fixed_derivations(&self) -> impl Iterator<Item = (&GroundAtom, &Derivation)> {
        self.fixed.iter().flat_map(|f| f.derivations.iter())
    }
    pub fn residual_size(&self) -> (usize, usize, usize) {
        (self.atoms.len(), self.rules.len(), self.components.len())
    }
    /// Retained evidence counts, not a heap measurement. Includes original false
    /// producers and dependencies, which never become executable residual rules.
    pub fn fixed_size(&self) -> (usize, usize, usize, usize, usize) {
        self.fixed.as_ref().map_or((0, 0, 0, 0, 0), |f| {
            (
                f.program.atoms.len(),
                f.derivations.len(),
                f.program.rules.len(),
                f.program.components.len(),
                f.program.dependencies.len(),
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, compare, rel, rule, subsets};
    use denotate_ir::Corpus;

    #[test]
    fn folded_small_programs_agree_with_original_stable_models_and_worlds() {
        for mask in 0..128 {
            let mut c = Corpus::new();
            let i = rel(&mut c, "input", true);
            let a = rel(&mut c, "a", false);
            let b = rel(&mut c, "b", false);
            let r = rel(&mut c, "r", false);
            let s = rel(&mut c, "s", false);
            let candidates = [
                (a, vec![]),
                (a, vec![(b, false)]),
                (b, vec![(a, false)]),
                (a, vec![(b, true)]),
                (b, vec![(a, true)]),
                (b, vec![(b, true)]),
                (r, vec![(r, true)]),
            ];
            for (bit, (head, body)) in candidates.iter().enumerate() {
                if mask & (1 << bit) != 0 {
                    rule(&mut c, *head, body);
                }
            }
            rule(&mut c, r, &[(i, false), (a, false)]);
            rule(&mut c, s, &[(i, true), (b, true)]);
            let limits = Limits::default();
            let domains = Domains::new();
            let fixed = FixedPreparation::prepare(&c, &domains, &limits).unwrap();
            let folded = GroundProgram::prepare_using_fixed(
                &c,
                &domains,
                &[],
                &BTreeSet::new(),
                &mut Budget::new(&limits),
                None,
                Some(&fixed),
            )
            .unwrap()
            .admit(&limits)
            .unwrap();
            let original = GroundProgram::prepare(&c, &domains, &limits)
                .unwrap()
                .admit(&limits)
                .unwrap();
            compare(&c, &domains, &folded);
            for world in subsets(&[atom(i)]) {
                let left = folded.evaluate(world.iter().cloned(), &limits).unwrap();
                let right = original.evaluate(world.iter().cloned(), &limits).unwrap();
                for relation in [i, a, b, r, s] {
                    let state = |r: &Replay<'_>| match r.fact(&atom(relation)).unwrap() {
                        FactState::Settled(value) => Some(value),
                        FactState::Blocked(_) => None,
                    };
                    assert_eq!(state(&left), state(&right), "program {mask}");
                }
            }
        }
    }

    #[test]
    fn fixed_exhaustion_is_explicit_and_cancelled_folds_publish_nothing() {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", false);
        rule(&mut c, a, &[]);
        let limits = Limits {
            max_atoms: 0,
            ..Limits::default()
        };
        assert!(matches!(
            FixedPreparation::prepare(&c, &Domains::new(), &limits),
            Err(CheckError::LimitExceeded {
                phase: "fixed facts",
                ..
            })
        ));
        let limits = Limits::default();
        limits.cancellation.cancel();
        assert!(matches!(
            FixedPreparation::prepare(&c, &Domains::new(), &limits),
            Err(CheckError::Cancelled)
        ));
        assert!(FixedPreparation::prepare(&c, &Domains::new(), &Limits::default()).is_ok());
    }
}
