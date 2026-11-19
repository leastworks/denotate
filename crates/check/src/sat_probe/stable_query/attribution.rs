//! Finite support in one reduct-validated interpretation. This is diagnostic work,
//! separately bounded for each tuple; it never reruns admission or certification.
use super::*;
impl Model {
    pub(super) fn attribute(
        &self,
        example: &mut PresenceExample<GroundAtom, Observation, BTreeMap<GroundAtom, EvidenceStep>>,
        limits: &Limits,
    ) -> Result<()> {
        let evidence = self.evidence(&example.tuple, &mut Budget::new(limits));
        example.attribution = Some(match evidence {
            Ok(v) => Attribution::Complete(v),
            Err(e) => {
                Attribution::Incomplete(query_inconclusive(e.in_phase("SAT attribution", None))?)
            }
        });
        let inputs = self
            .program
            .dependency_inputs_with_budget([example.tuple.clone()], &mut Budget::new(limits));
        example.dependency_inputs = Some(match inputs {
            Ok(v) => Attribution::Complete(v),
            Err(e) => Attribution::Incomplete(query_inconclusive(
                e.in_phase("SAT diagnostic inputs", None),
            )?),
        });
        Ok(())
    }
    fn evidence(
        &self,
        root: &GroundAtom,
        b: &mut Budget<'_>,
    ) -> Result<BTreeMap<GroundAtom, EvidenceStep>> {
        if self.mode != Mode::Program || self.value(root) != Some(true) {
            return Err(CheckError::Internal(
                "SAT evidence requires a confirmed present tuple",
            ));
        }
        let cone = self
            .program
            .dependency_cone_with_budget([root.clone()], b)?;
        let mut steps = BTreeMap::new();
        for a in &cone.facts {
            b.tick("SAT evidence inputs")?;
            if self.program.inputs.contains(a) && self.value(a) == Some(true) {
                steps.insert(
                    a.clone(),
                    EvidenceStep {
                        order: steps.len(),
                        evidence: GroundEvidence::Input,
                    },
                );
            }
        }
        let rules = cone
            .rules
            .iter()
            .map(|id| {
                self.program
                    .original_rule(*id)
                    .ok_or(CheckError::Internal("missing SAT evidence rule"))
            })
            .collect::<Result<Vec<_>>>()?;
        // Positive derivations must be finite, even when completion admits self
        // support. Negative premises read the already-validated whole model.
        while !steps.contains_key(root) {
            let before = steps.len();
            for rule in &rules {
                b.charge(rule.body.len() + 1, "SAT reduct evidence")?;
                if steps.contains_key(&rule.head.atom) {
                    continue;
                }
                if !rule.replacements.is_empty() {
                    return Err(CheckError::Internal("SAT evidence expected original rules"));
                }
                if !rule.body.iter().all(|l| match l.polarity {
                    Polarity::Positive => steps.contains_key(&l.term.atom),
                    Polarity::Negative => self.value(&l.term.atom) == Some(false),
                }) {
                    continue;
                }
                if self.value(&rule.head.atom) != Some(true) {
                    return Err(CheckError::Internal(
                        "SAT reduct evidence disagrees with model",
                    ));
                }
                let premises = rule
                    .body
                    .iter()
                    .map(|l| {
                        let fact = l.term.atom.clone();
                        let occurrence = l.term.occurrence;
                        Ok(if l.polarity == Polarity::Positive {
                            PremiseEvidence::Positive { fact, occurrence }
                        } else {
                            let provider = if self.program.inputs.contains(&fact) {
                                CompletedProvider::InputSnapshot
                            } else if !self.program.is_possible(&fact)? {
                                CompletedProvider::NoPossibleProducer
                            } else {
                                CompletedProvider::Component(self.program.component_for(&fact)?.id)
                            };
                            PremiseEvidence::Absent {
                                fact,
                                occurrence,
                                provider,
                            }
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                steps.insert(
                    rule.head.atom.clone(),
                    EvidenceStep {
                        order: steps.len(),
                        evidence: GroundEvidence::Derived {
                            rule: (*rule).clone(),
                            premises,
                        },
                    },
                );
            }
            if before == steps.len() {
                return Err(CheckError::Internal(
                    "confirmed SAT tuple has no finite reduct derivation",
                ));
            }
        }
        let mut result = BTreeMap::new();
        let mut pending = vec![root.clone()];
        while let Some(a) = pending.pop() {
            b.tick("SAT evidence selection")?;
            if result.contains_key(&a) {
                continue;
            }
            let step = steps
                .remove(&a)
                .ok_or(CheckError::Internal("missing SAT support"))?;
            if let GroundEvidence::Derived { premises, .. } = &step.evidence {
                for p in premises {
                    if let PremiseEvidence::Positive { fact, .. } = p {
                        pending.push(fact.clone());
                    }
                }
            }
            result.insert(a, step);
        }
        Ok(result)
    }
}
