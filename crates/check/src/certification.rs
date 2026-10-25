//! Concrete, observation-local admission. No symbolic region is admitted and
//! no unsuccessful attempt changes a previously established cone finding.
use crate::{
    limits::{Budget, Result},
    *,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservationPruning {
    pub round: usize,
    pub rule: GroundRuleId,
    /// This signed premise was false, with its fact settled to `value`.
    pub premise: GroundLiteral,
    pub value: bool,
    pub provider: CompletedProvider,
}

/// A complete replay for exactly this observation, not all permitted inputs.
/// Component IDs are local to residual graph revisions; `providers` resolves
/// the completed-provider references in pruning and absence evidence.
#[derive(Debug)]
pub struct CertifiedObservation {
    pub observation: Observation,
    pub facts: BTreeSet<GroundAtom>,
    pub evidence: BTreeMap<GroundAtom, EvidenceStep>,
    pub pruning: Vec<ObservationPruning>,
    pub providers: BTreeMap<ComponentId, Vec<GroundAtom>>,
}

#[derive(Debug)]
pub enum CertificationOutcome {
    Certified(Box<CertifiedObservation>),
    /// Progress stopped with unresolved components. Not a no-meaning claim.
    NotCertified,
    Inconclusive(Inconclusive),
}

impl GroundProgram {
    pub fn certify_observation(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
        limits: &Limits,
    ) -> Result<CertificationOutcome> {
        limits.cancellation.check()?;
        let result = self.certify_with_budget(present, &mut Budget::new(limits));
        match result {
            Ok(outcome) => Ok(outcome),
            Err(error) => Ok(CertificationOutcome::Inconclusive(
                Inconclusive::from_error(error)?,
            )),
        }
    }

    pub(crate) fn certify_with_budget(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<CertificationOutcome> {
        let mut observation = Observation {
            present: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for atom in present {
            budget.tick("certification observation")?;
            if !self.inputs.contains(&atom) {
                return Err(CheckError::InvalidObservation(atom));
            }
            observation.present.insert(atom);
        }
        self.validate_input_world(&observation.present, budget)?;
        for atom in &self.inputs {
            budget.tick("certification observation")?;
            if !observation.present.contains(atom) {
                observation.absent.insert(atom.clone());
            }
        }
        // Bound the copy before allocating it. BDD conditions and forwarding
        // certificates share immutable storage; rule/graph metadata is copied.
        budget.charge(
            self.atoms.len() + self.dependencies.len(),
            "certification snapshot",
        )?;
        for rule in self.original_rules().chain(self.rules()) {
            budget.charge(
                1 + rule.head.arguments.len()
                    + rule
                        .body
                        .iter()
                        .map(|l| 1 + l.term.arguments.len())
                        .sum::<usize>(),
                "certification snapshot",
            )?;
        }
        for proof in self.rewrite_proofs() {
            for summary in std::iter::once(&proof.candidate).chain(&proof.producers) {
                budget.charge(
                    1 + summary.rule.body.len() + summary.settled.len(),
                    "certification snapshot",
                )?;
            }
        }
        let mut residual = self.clone();
        let mut pruning = Vec::new();
        let mut providers = BTreeMap::new();
        let mut round = 0;
        loop {
            budget.tick("certification round")?;
            let replay =
                residual.evaluate_selected(observation.present.iter().cloned(), None, budget)?;
            if replay.is_complete() {
                let mut facts = BTreeSet::new();
                for atom in replay.established_facts() {
                    budget.tick("certification facts")?;
                    facts.insert(atom.clone());
                }
                let evidence = crate::findings::collect_evidence(&replay, &facts, budget)?;
                for step in evidence.values() {
                    budget.tick("certification providers")?;
                    if let GroundEvidence::Derived { premises, .. } = &step.evidence {
                        for premise in premises {
                            budget.tick("certification providers")?;
                            if let PremiseEvidence::Absent { provider, .. } = premise {
                                retain_provider(&residual, provider, &mut providers, budget)?;
                            }
                        }
                    }
                }
                return Ok(CertificationOutcome::Certified(Box::new(
                    CertifiedObservation {
                        observation,
                        facts,
                        evidence,
                        pruning,
                        providers,
                    },
                )));
            }
            let mut batch = Vec::new();
            for (component, rules) in residual.components.iter().zip(&residual.component_rules) {
                budget.tick("certification components")?;
                // Admitted providers have already settled. Disabling their false
                // producers cannot unblock anything and only pads the certificate.
                if component.blocked_by.is_empty() {
                    continue;
                }
                for index in rules {
                    let rule = &residual.rules[*index];
                    budget.tick("certification pruning")?;
                    for premise in &rule.body {
                        budget.tick("certification pruning")?;
                        let fact = &premise.term.atom;
                        let FactState::Settled(value) = replay.fact(fact)? else {
                            continue;
                        };
                        if value == (premise.polarity == Polarity::Positive) {
                            continue;
                        }
                        let provider = if residual.inputs.contains(fact) {
                            CompletedProvider::InputSnapshot
                        } else if !residual.is_possible(fact)? {
                            CompletedProvider::NoPossibleProducer
                        } else {
                            CompletedProvider::Component(residual.component_for(fact)?.id)
                        };
                        retain_provider(&residual, &provider, &mut providers, budget)?;
                        batch.push(ObservationPruning {
                            round,
                            rule: rule.id,
                            premise: premise.clone(),
                            value,
                            provider,
                        });
                        break; // One settled false premise suffices to disable a rule.
                    }
                }
            }
            if batch.is_empty() {
                return Ok(CertificationOutcome::NotCertified);
            }
            drop(replay);
            for step in batch {
                budget.tick("certification commit")?;
                residual.rewrites.dropped.insert(step.rule);
                pruning.push(step);
            }
            // Only this private copy changes. A failed rebuild is discarded,
            // and never exports a partial certificate or a global admission.
            crate::graph::analyze(&mut residual, budget)?;
            round += 1;
        }
    }
}

fn retain_provider(
    program: &GroundProgram,
    provider: &CompletedProvider,
    retained: &mut BTreeMap<ComponentId, Vec<GroundAtom>>,
    budget: &mut Budget<'_>,
) -> Result<()> {
    if let CompletedProvider::Component(id) = provider {
        if let std::collections::btree_map::Entry::Vacant(entry) = retained.entry(*id) {
            let component = program
                .component(*id)
                .ok_or(CheckError::Internal("missing certification provider"))?;
            budget.charge(component.atoms.len(), "certification providers")?;
            entry.insert(component.atoms.clone());
        }
    }
    Ok(())
}

impl SymbolicMeaning<'_> {
    pub(crate) fn certify_counterexample(
        &self,
        original: &mut Counterexample,
        group: &AtMostOneGroup,
        violation: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let attempt = (|| -> Result<Option<Counterexample>> {
            budget.charge(self.program.inputs.len(), "certification candidate")?;
            let mut observation = original.observation.clone();
            for candidate in 0..2 {
                if !self.context().evaluate_with_budget(
                    violation,
                    observation.present.iter().cloned(),
                    budget,
                )? {
                    return Err(CheckError::Internal(
                        "certification candidate lost violation",
                    ));
                }
                match self
                    .program
                    .certify_with_budget(observation.present.iter().cloned(), budget)?
                {
                    CertificationOutcome::Certified(certified) => {
                        let mut tuples = BTreeSet::new();
                        for fact in &group.tuples {
                            budget.tick("certification violation replay")?;
                            if self.context().evaluate_with_budget(
                                &self.known(fact),
                                observation.present.iter().cloned(),
                                budget,
                            )? != certified.facts.contains(fact)
                            {
                                return Err(CheckError::Internal(
                                    "certified replay disagrees with symbolic fact",
                                ));
                            }
                            if certified.facts.contains(fact) {
                                tuples.insert(fact.clone());
                            }
                        }
                        if tuples.len() < 2 {
                            return Err(CheckError::Internal("certified violation did not replay"));
                        }
                        return Ok(Some(certified_finding(
                            observation,
                            tuples,
                            certified,
                            budget,
                        )?));
                    }
                    CertificationOutcome::NotCertified => {}
                    CertificationOutcome::Inconclusive(_) => {
                        return Err(CheckError::Internal(
                            "unexpected nested certification status",
                        ));
                    }
                }
                if candidate == 0 {
                    let alternate =
                        self.context()
                            .present_dont_cares(violation, &observation, budget)?;
                    if alternate == observation {
                        break;
                    }
                    observation = alternate;
                }
            }
            Ok(None)
        })();
        match attempt {
            // Replace all witness-dependent fields together, after the entire
            // replay/evidence operation succeeds. Any limit keeps the original.
            Ok(Some(replacement)) => *original = replacement,
            Ok(None) => original.certification = Some(CertificationOutcome::NotCertified),
            Err(error) => {
                budget.failure(&error);
                original.certification = Some(CertificationOutcome::Inconclusive(
                    Inconclusive::from_error(error)?,
                ))
            }
        }
        Ok(())
    }
}

fn certified_finding(
    observation: Observation,
    tuples: BTreeSet<GroundAtom>,
    certified: Box<CertifiedObservation>,
    budget: &mut Budget<'_>,
) -> Result<Counterexample> {
    // Copy the conflict's grounded proof from THIS replay,
    // never from the absent-first candidate's old evidence.
    let mut evidence = BTreeMap::new();
    let mut pending: Vec<_> = tuples.iter().cloned().collect();
    while let Some(fact) = pending.pop() {
        budget.tick("certification finding evidence")?;
        if evidence.contains_key(&fact) {
            continue;
        }
        let step = certified
            .evidence
            .get(&fact)
            .ok_or(CheckError::Internal("missing certified evidence"))?;
        if let GroundEvidence::Derived { rule, premises } = &step.evidence {
            budget.charge(
                1 + rule.body.len() + premises.len(),
                "certification finding evidence",
            )?;
            for premise in premises {
                if let PremiseEvidence::Positive { fact, .. } = premise {
                    pending.push(fact.clone());
                }
            }
        }
        evidence.insert(fact, step.clone());
    }
    Ok(Counterexample {
        observation,
        replay_scope: ReplayScope::WholeProgram,
        tuples,
        evidence,
        certification: Some(CertificationOutcome::Certified(certified)),
        confined_to_no_meaning: vec![],
    })
}

impl GroundProgram {
    /// Candidate was already validated and replayed in its cone. This optional
    /// whole-program upgrade uses the shared concrete kernel, with no Boolean
    /// support computation or alternate-world retry.
    pub(crate) fn certify_replayed_candidate(
        &self,
        original: &mut Counterexample,
        group: &AtMostOneGroup,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        let attempt = (|| {
            let outcome =
                self.certify_with_budget(original.observation.present.iter().cloned(), budget)?;
            match outcome {
                CertificationOutcome::Certified(certified) => {
                    let mut tuples = BTreeSet::new();
                    for fact in &group.tuples {
                        budget.tick("certification violation replay")?;
                        if certified.facts.contains(fact) {
                            tuples.insert(fact.clone());
                        }
                    }
                    if tuples != original.tuples || tuples.len() < 2 {
                        return Err(CheckError::Internal(
                            "SAT certified replay disagrees with cone replay",
                        ));
                    }
                    Ok(Some(certified_finding(
                        original.observation.clone(),
                        tuples,
                        certified,
                        budget,
                    )?))
                }
                CertificationOutcome::NotCertified => Ok(None),
                CertificationOutcome::Inconclusive(_) => Err(CheckError::Internal(
                    "unexpected nested certification status",
                )),
            }
        })();
        match attempt {
            Ok(Some(replacement)) => *original = replacement,
            Ok(None) => original.certification = Some(CertificationOutcome::NotCertified),
            Err(error) => {
                budget.failure(&error);
                original.certification = Some(CertificationOutcome::Inconclusive(
                    Inconclusive::from_error(error)?,
                ));
            }
        }
        Ok(())
    }
}
