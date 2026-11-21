//! Verification-wide quantification is outside H. Processing never selects a class.
pub use super::super::stable_query::{Context, MeaningMode};
use super::*;
use denotate_ir::{NoticeId, ObligationId};

#[derive(Debug, Clone)]
pub enum Search<T> {
    NotAnalysed,
    None,
    Exists(T),
    Inconclusive(Inconclusive),
}
impl<T> Search<T> {
    pub fn exists(&self) -> bool {
        matches!(self, Self::Exists(_))
    }
    pub fn complete(&self) -> bool {
        matches!(self, Self::None | Self::Exists(_))
    }
    #[cfg(test)]
    fn unknown(&mut self, cause: Inconclusive) {
        if !self.exists() {
            *self = Self::Inconclusive(cause);
        }
    }
    #[cfg(test)]
    fn finish(&mut self) {
        if matches!(self, Self::NotAnalysed) {
            *self = Self::None;
        }
    }
}
#[derive(Debug, Clone)]
pub struct Pair {
    pub first: Model,
    pub second: Model,
}
#[derive(Debug, Clone)]
pub struct Classification {
    pub accepted: Search<Model>,
    /// Validated classification model without H; the H query was unsatisfiable.
    pub rejected: Search<Model>,
    pub no_meaning: Search<Observation>,
    pub ambiguous: Search<Pair>,
}
#[derive(Debug, Clone)]
pub struct Meaning {
    pub no_meaning: Search<Observation>,
    pub ambiguous: Search<Pair>,
    pub applicable: bool,
}
#[derive(Debug, Clone)]
pub struct CheckOptions {
    pub meaning: MeaningMode,
    /// Candidate observations per symbolic search; a cube may cover many worlds.
    pub max_worlds: usize,
    pub max_tuples: usize,
    pub max_examples: usize,
    /// Independent advisory work, never charged to required checking.
    pub circular_support: bool,
    pub advisory_limits: Limits,
}
impl Default for CheckOptions {
    fn default() -> Self {
        Self {
            meaning: MeaningMode::Full,
            max_worlds: 1024,
            max_tuples: 10000,
            max_examples: 8,
            circular_support: false,
            advisory_limits: Limits::default(),
        }
    }
}
#[derive(Debug)]
pub struct Report {
    pub verification: VerificationId,
    pub hypothesis: Option<RelationId>,
    pub decisions: Option<BTreeSet<RelationId>>,
    pub context: Context,
    pub classification: Option<Classification>,
    pub meaning: Meaning,
    pub obligations: BTreeMap<ObligationId, ObligationResult>,
    pub notices_not_analysed: BTreeSet<NoticeId>,
    pub incomplete: Vec<Inconclusive>,
    pub advisory: Advisory,
    pub(crate) program: Arc<GroundProgram>,
}
impl Report {
    pub fn program(&self) -> &GroundProgram {
        &self.program
    }
    pub fn all_rejected(&self) -> bool {
        self.classification.as_ref().is_some_and(|c| {
            matches!(c.accepted, Search::None)
                && matches!(c.ambiguous, Search::None)
                && matches!(c.no_meaning, Search::None)
                && c.rejected.exists()
        })
    }
    pub fn has_failures(&self) -> bool {
        matches!(
            self.context,
            Context::EmptyUniverse | Context::InconsistentAssumptions
        ) || self
            .classification
            .as_ref()
            .is_some_and(|c| c.ambiguous.exists() || c.no_meaning.exists())
            || self.meaning.no_meaning.exists()
            || self.meaning.ambiguous.exists()
            || self.obligations.values().any(ObligationResult::failed)
    }
    pub fn is_incomplete(&self) -> bool {
        if matches!(self.context, Context::Inconclusive(_)) {
            return true;
        }
        if self.context != Context::Permitted {
            return false;
        }
        !self.incomplete.is_empty()
            || !self.notices_not_analysed.is_empty()
            || self.obligations.values().any(|o| !o.complete())
            || self.classification.as_ref().is_some_and(|c| {
                !c.accepted.complete()
                    || !c.rejected.complete()
                    || !c.ambiguous.complete()
                    || !c.no_meaning.complete()
            })
            || (self.meaning.applicable
                && (!self.meaning.no_meaning.complete() || !self.meaning.ambiguous.complete()))
    }
}
#[cfg(test)]
impl Engine {
    pub(super) fn check_enumerated(
        &self,
        keys: &SemanticKeys,
        options: &CheckOptions,
    ) -> Result<Report> {
        if options.meaning != MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "completion supports full meaning analysis only",
            ));
        }
        let mut report = Report {
            verification: self.verification,
            hypothesis: self.hypothesis,
            decisions: self.decisions.clone(),
            context: Context::Permitted,
            classification: self.hypothesis.map(|_| Classification {
                accepted: Search::NotAnalysed,
                rejected: Search::NotAnalysed,
                no_meaning: Search::NotAnalysed,
                ambiguous: Search::NotAnalysed,
            }),
            meaning: Meaning {
                no_meaning: Search::NotAnalysed,
                ambiguous: Search::NotAnalysed,
                applicable: self.hypothesis.is_none(),
            },
            obligations: BTreeMap::new(),
            notices_not_analysed: self.notices.clone(),
            incomplete: vec![],
            advisory: Advisory::NotRequested,
            program: self.program.clone(),
        };
        let mut world_budget = Budget::new(&self.limits);
        let mut classification_budget = Budget::new(&self.limits);
        let mut meaning_budget = Budget::new(&self.limits);
        let mut query = WorldQuery::default();
        let mut worlds = 0;
        let mut rejected_unknown = None;
        let mut eligibility_unknown = None;
        let mut completed = false;
        let mut accepted_examples = Vec::new();
        let mut advisory_truncated = false;
        let mut properties = self.properties(keys, options)?;
        let mut property_budgets = self
            .selection
            .iter()
            .map(|(id, _)| (*id, Budget::new(&self.limits)))
            .collect::<BTreeMap<_, _>>();
        let _progress = self
            .limits
            .progress
            .scope("completion verification", None, true);
        let enumeration: Result<()> = (|| {
            loop {
                let world = match self.worlds_using(&query, &mut world_budget)? {
                    WorldAnswer::NoWorld => {
                        completed = true;
                        break;
                    }
                    WorldAnswer::Inconclusive(c) => return Err(c.into()),
                    WorldAnswer::World(w) => w,
                };
                world_budget.room(
                    worlds,
                    options.max_worlds,
                    "completion classification",
                    "worlds",
                )?;
                worlds += 1;
                let classification = if self.hypothesis.is_some() {
                    self.observation_using(
                        world.present.iter().cloned(),
                        &mut classification_budget,
                        false,
                    )?
                } else {
                    ObservationOutcome::WholeProgram(Interpretations::NotAnalysed)
                };
                let mut accepted = None;
                let applicable = match classification {
                    ObservationOutcome::Rejected { without_hypothesis } => {
                        let c = report.classification.as_mut().unwrap();
                        if !c.rejected.exists() {
                            c.rejected = Search::Exists(without_hypothesis);
                        }
                        false
                    }
                    ObservationOutcome::ClassificationNoMeaning => {
                        let c = report.classification.as_mut().unwrap();
                        if !c.no_meaning.exists() {
                            c.no_meaning = Search::Exists(world.clone());
                        }
                        false
                    }
                    ObservationOutcome::Ambiguous { first, second } => {
                        let c = report.classification.as_mut().unwrap();
                        if !c.ambiguous.exists() {
                            c.ambiguous = Search::Exists(Pair { first, second });
                        }
                        false
                    }
                    ObservationOutcome::Accepted { classification, .. } => {
                        let c = report.classification.as_mut().unwrap();
                        if !c.accepted.exists() {
                            c.accepted = Search::Exists(classification.clone());
                        }
                        if options.circular_support {
                            if accepted_examples.len() < options.max_examples {
                                accepted_examples.push(classification.clone());
                            } else {
                                advisory_truncated = true;
                            }
                        }
                        accepted = Some(classification);
                        true
                    }
                    ObservationOutcome::WholeProgram(_) => true,
                    ObservationOutcome::Inconclusive { cause, example } => {
                        let c = report.classification.as_mut().unwrap();
                        c.accepted.unknown(cause);
                        c.ambiguous.unknown(cause);
                        // A validated model proves K nonempty even if uniqueness stopped.
                        if example.is_none() {
                            c.rejected.unknown(cause);
                            c.no_meaning.unknown(cause);
                            rejected_unknown = Some(cause);
                        }
                        eligibility_unknown = Some(cause);
                        report.incomplete.push(cause);
                        false
                    }
                    ObservationOutcome::NotPermitted => {
                        return Err(CheckError::Internal(
                            "world search returned an excluded observation",
                        ));
                    }
                };
                if applicable {
                    report.meaning.applicable = true;
                    let meaning =
                        self.meaning_at(&world, accepted.as_ref(), &mut meaning_budget)?;
                    match meaning {
                        Interpretations::NoMeaning => {
                            if !report.meaning.no_meaning.exists() {
                                report.meaning.no_meaning = Search::Exists(world.clone());
                            }
                        }
                        Interpretations::Multiple { first, second } => {
                            if !report.meaning.ambiguous.exists() {
                                report.meaning.ambiguous = Search::Exists(Pair { first, second });
                            }
                        }
                        Interpretations::Unique(_) => (),
                        Interpretations::Inconclusive { cause, example } => {
                            if example.is_none() {
                                report.meaning.no_meaning.unknown(cause);
                            }
                            report.meaning.ambiguous.unknown(cause);
                            report.incomplete.push(cause);
                        }
                        Interpretations::NotAnalysed => unreachable!(),
                    }
                    // Independent property cones do not require a whole processing model.
                    for (id, property) in &mut properties {
                        self.check_property(
                            property,
                            &world,
                            accepted.as_ref(),
                            options,
                            property_budgets.get_mut(id).unwrap(),
                        )?;
                    }
                }
                let mut cube = Vec::new();
                world_budget.charge(self.program.inputs.len(), "completion world exclusions")?;
                for a in &self.program.inputs {
                    cube.push((a.clone(), world.present.contains(a)));
                }
                let retained = query
                    .exclude
                    .len()
                    .saturating_add(1)
                    .saturating_mul(self.program.inputs.len().saturating_add(1));
                world_budget.room(
                    retained.saturating_sub(1),
                    self.limits.max_dependencies,
                    "completion world exclusions",
                    "literals",
                )?;
                query.exclude.push(cube);
            }
            Ok(())
        })();
        if let Err(e) = enumeration {
            let cause = inconclusive(e)?;
            if worlds == 0 {
                report.context = Context::Inconclusive(cause);
            }
            report.incomplete.push(cause);
            if let Some(c) = &mut report.classification {
                c.accepted.unknown(cause);
                c.rejected.unknown(cause);
                c.no_meaning.unknown(cause);
                c.ambiguous.unknown(cause);
            }
            rejected_unknown = Some(cause);
            eligibility_unknown = Some(cause);
            report.meaning.no_meaning.unknown(cause);
            report.meaning.ambiguous.unknown(cause);
        }
        if completed && worlds == 0 {
            report.context = Context::InconsistentAssumptions;
        }
        if completed {
            if let Some(c) = &mut report.classification {
                c.accepted.finish();
                c.rejected.finish();
                c.no_meaning.finish();
                c.ambiguous.finish();
            }
            report.meaning.no_meaning.finish();
            report.meaning.ambiguous.finish();
        }
        if let Some(cause) = eligibility_unknown {
            report.meaning.no_meaning.unknown(cause);
            report.meaning.ambiguous.unknown(cause);
        }
        let vacuous = report
            .classification
            .as_ref()
            .is_some_and(|c| matches!(c.accepted, Search::None));
        for (id, mut property) in properties {
            property.finish(
                completed && report.context == Context::Permitted,
                eligibility_unknown,
                vacuous && report.context == Context::Permitted,
            );
            report.obligations.insert(id, property);
        }
        for (id, req) in &self.selection {
            if let denotate_ir::Requirement::NoRejections { .. } = req {
                let rejected = &report.classification.as_ref().unwrap().rejected;
                report.obligations.insert(
                    *id,
                    ObligationResult::rejection(req.clone(), rejected, rejected_unknown),
                );
            }
        }
        if report.context != Context::Permitted {
            for o in report.obligations.values_mut() {
                o.finished = false;
                o.vacuous = false;
            }
            report.classification = self.hypothesis.map(|_| Classification {
                accepted: Search::NotAnalysed,
                rejected: Search::NotAnalysed,
                no_meaning: Search::NotAnalysed,
                ambiguous: Search::NotAnalysed,
            });
            report.meaning.no_meaning = Search::NotAnalysed;
            report.meaning.ambiguous = Search::NotAnalysed;
        }
        report.incomplete.sort_by_key(|c| (c.phase, c.resource));
        report.incomplete.dedup();
        if options.circular_support {
            report.advisory = self.circular_advisory(
                &accepted_examples,
                advisory_truncated || !completed || eligibility_unknown.is_some(),
                options,
                keys,
            )?;
        }
        Ok(report)
    }
}
