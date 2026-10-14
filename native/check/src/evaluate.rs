use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::OccurrenceId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactState {
    Settled(bool),
    Blocked(BTreeSet<ComponentId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletedProvider {
    /// Absent from the prepared positive closure with all legal input facts included.
    NoPossibleProducer,
    /// The complete set of input facts supplied to this Replay.
    InputSnapshot,
    Component(ComponentId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PremiseEvidence {
    Positive {
        fact: GroundAtom,
        occurrence: OccurrenceId,
    },
    /// A reference and confirmed absence, not a recursive why-not explanation.
    Absent {
        fact: GroundAtom,
        occurrence: OccurrenceId,
        provider: CompletedProvider,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Evidence {
    Input,
    Derived {
        rule: GroundRuleId,
        premises: Vec<PremiseEvidence>,
    },
}

#[derive(Debug)]
pub struct Derivation {
    /// Positive premises refer to facts with a smaller order. This is internal
    /// replay order, not an author-visible variable binding or semantic value.
    pub order: usize,
    pub evidence: Evidence,
}

/// One input observation. Can contain scoped settled results while other
/// components remain blocked. Retains its immutable prepared program.
#[derive(Debug)]
pub struct Replay<'a> {
    program: &'a GroundProgram,
    present: BTreeSet<GroundAtom>,
    derivations: BTreeMap<GroundAtom, Derivation>,
}
impl Replay<'_> {
    pub fn program(&self) -> &GroundProgram {
        self.program
    }
    pub fn is_complete(&self) -> bool {
        self.program.is_admitted()
    }
    pub fn present_inputs(&self) -> impl Iterator<Item = &GroundAtom> {
        self.present.iter()
    }
    /// Only established facts, NOT a total meaning when is_complete() is false.
    /// Use fact() to distinguish settled absence from blocked knowledge.
    pub fn established_facts(&self) -> impl Iterator<Item = &GroundAtom> {
        self.derivations.keys()
    }
    pub fn fact(&self, atom: &GroundAtom) -> Result<FactState> {
        if !self.program.is_possible(atom)? {
            return Ok(FactState::Settled(false));
        }
        let component = self.program.component_for(atom)?;
        if !component.blocked_by.is_empty() {
            return Ok(FactState::Blocked(component.blocked_by.clone()));
        }
        Ok(FactState::Settled(self.derivations.contains_key(atom)))
    }
    /// A settled absence has a provider; a true or blocked fact does not.
    pub fn absence_provider(&self, atom: &GroundAtom) -> Result<Option<CompletedProvider>> {
        if !self.program.is_possible(atom)? {
            return Ok(Some(CompletedProvider::NoPossibleProducer));
        }
        if self.fact(atom)? != FactState::Settled(false) {
            return Ok(None);
        }
        Ok(Some(if self.program.inputs.contains(atom) {
            CompletedProvider::InputSnapshot
        } else {
            CompletedProvider::Component(self.program.component_for(atom)?.id)
        }))
    }
    /// None is not evidence of absence; inspect fact() for settled/blocked state.
    pub fn derivation(&self, atom: &GroundAtom) -> Option<&Derivation> {
        self.derivations.get(atom)
    }
}

impl GroundProgram {
    /// Input facts form a complete snapshot: omitted input tuples are absent. Rules
    /// never restrict that snapshot. Non-stratifiable components remain blocked
    /// even if a particular observation could make their cycles inactive.
    pub fn evaluate(
        &self,
        present: impl IntoIterator<Item = GroundAtom>,
        limits: &Limits,
    ) -> Result<Replay<'_>> {
        let mut budget = Budget::new(limits);
        let mut snapshot = BTreeSet::new();
        for input in present {
            budget.tick("observation")?;
            if !self.inputs.contains(&input) {
                return Err(CheckError::InvalidObservation(input));
            }
            snapshot.insert(input);
        }
        let mut replay = Replay {
            program: self,
            present: snapshot,
            derivations: BTreeMap::new(),
        };
        for atom in &replay.present {
            budget.tick("evaluation")?;
            replay.derivations.insert(
                atom.clone(),
                Derivation {
                    order: replay.derivations.len(),
                    evidence: Evidence::Input,
                },
            );
        }
        for (index, component) in self.components.iter().enumerate() {
            budget.tick("evaluation")?;
            if !component.blocked_by.is_empty() {
                continue;
            }
            loop {
                let mut changed = false;
                for rule in &self.component_rules[index] {
                    budget.tick("evaluation")?;
                    let rule = &self.rules[*rule];
                    if replay.derivations.contains_key(&rule.head.atom) {
                        continue;
                    } // keep first grounded derivation
                    let mut premises = Vec::new();
                    let mut enabled = true;
                    for literal in &rule.body {
                        budget.tick("evaluation")?;
                        let fact = &literal.term.atom;
                        let occurrence = literal.term.occurrence;
                        match literal.polarity {
                            Polarity::Positive => {
                                if !replay.derivations.contains_key(fact) {
                                    enabled = false;
                                    break;
                                }
                                premises.push(PremiseEvidence::Positive {
                                    fact: fact.clone(),
                                    occurrence,
                                });
                            }
                            Polarity::Negative => {
                                if !self.atom_index.contains_key(fact) {
                                    premises.push(PremiseEvidence::Absent {
                                        fact: fact.clone(),
                                        occurrence,
                                        provider: CompletedProvider::NoPossibleProducer,
                                    });
                                    continue;
                                }
                                let provider = self.component_for(fact)?;
                                if provider.id.index >= index || !provider.blocked_by.is_empty() {
                                    return Err(CheckError::Internal(
                                        "negated premise is not settled",
                                    ));
                                }
                                if replay.derivations.contains_key(fact) {
                                    enabled = false;
                                    break;
                                }
                                premises.push(PremiseEvidence::Absent {
                                    fact: fact.clone(),
                                    occurrence,
                                    provider: if self.inputs.contains(fact) {
                                        CompletedProvider::InputSnapshot
                                    } else {
                                        CompletedProvider::Component(provider.id)
                                    },
                                });
                            }
                        }
                    }
                    if enabled {
                        let order = replay.derivations.len();
                        replay.derivations.insert(
                            rule.head.atom.clone(),
                            Derivation {
                                order,
                                evidence: Evidence::Derived {
                                    rule: rule.id,
                                    premises,
                                },
                            },
                        );
                        changed = true;
                    }
                }
                if !component.recursive || !changed {
                    break;
                }
            }
        }
        Ok(replay)
    }
}
