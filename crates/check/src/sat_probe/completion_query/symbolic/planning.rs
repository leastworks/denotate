//! Bounded planning questions. Runtime paths pin actual inputs, never H or an
//! H-justified derived value. Accepted-value proofs do not decide runtime acceptance.
use super::*;

/// Facts observed at runtime. Derived pins are rejected, rather than silently
/// treating a tentative H-justified value as a runtime fact outside H.
pub type RuntimePath = BTreeMap<GroundAtom, bool>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathOutcome {
    NoPermittedInputs,
    Accept,
    Reject,
    Mixed,
    Invalid,
    Inconclusive,
}
#[derive(Debug, Clone)]
pub struct PlanningContext {
    pub outcome: PathOutcome,
    pub assumptions: Vec<AssumptionAnalysis>,
    pub classification: Option<Classification>,
    pub inconclusive: Option<Inconclusive>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantScope {
    /// No processing equations may justify a classification step.
    Classification,
    /// Frozen live cone of the target, union C(H). No unrelated downstream rules.
    Output,
}
#[derive(Debug, Clone)]
pub enum PlanningConstant {
    Proven {
        value: bool,
        example: Model,
    },
    Varying(Pair),
    /// No scoped interpretation exists. Never a vacuous constant proof.
    NoInterpretation,
    ContextNotReady(Box<PlanningContext>),
    Inconclusive(Inconclusive),
}

impl Engine {
    /// Classify all certified W observations extending a runtime path. The
    /// selected contract is audited independently over U, exactly as in checking.
    /// Without H every certified observation is accepted; output meaning is a
    /// separate query and may still fail.
    /// One cumulative SAT allowance for this pass (its runs share it).
    pub fn planning_context(
        &self,
        path: &RuntimePath,
        options: &CheckOptions,
    ) -> Result<PlanningContext> {
        self.scoped().planning_context_in(path, options)
    }
    fn planning_context_in(
        &self,
        path: &RuntimePath,
        options: &CheckOptions,
    ) -> Result<PlanningContext> {
        // Validate pins even when the contract cannot be certified.
        let world = self.worlds_using(
            &WorldQuery {
                pins: path.iter().map(|(a, v)| (a.clone(), *v)).collect(),
                ..Default::default()
            },
            &mut Budget::new(&self.limits),
        )?;
        let assumptions = self.assumption_analysis(options)?;
        let mut result = PlanningContext {
            outcome: PathOutcome::Inconclusive,
            assumptions,
            classification: None,
            inconclusive: None,
        };
        if result.assumptions.iter().any(|a| !a.certified()) {
            result.outcome = if result
                .assumptions
                .iter()
                .any(|a| a.ambiguous.exists() || a.no_meaning.exists())
            {
                PathOutcome::Invalid
            } else {
                PathOutcome::Inconclusive
            };
            return Ok(result);
        }
        match world {
            WorldAnswer::NoWorld => {
                result.outcome = PathOutcome::NoPermittedInputs;
                return Ok(result);
            }
            WorldAnswer::Inconclusive(c) => {
                result.inconclusive = Some(c);
                return Ok(result);
            }
            WorldAnswer::World(_) => {}
        }
        if self.classification.is_none() {
            result.outcome = PathOutcome::Accept;
            return Ok(result);
        }
        let ambiguous = self.symbolic_pair_in(path, true, true, options, 1)?;
        let accepted =
            self.symbolic_accepted_in(path, matches!(ambiguous, Search::None), options, 1)?;
        let rejected = self.symbolic_rejected_in(path, options, 1)?;
        let no_meaning = self.symbolic_no_meaning_in(path, true, true, options, 1)?;
        result.outcome = if ambiguous.exists() || no_meaning.exists() {
            PathOutcome::Invalid
        } else if !ambiguous.complete()
            || !no_meaning.complete()
            || !accepted.complete()
            || !rejected.complete()
        {
            PathOutcome::Inconclusive
        } else {
            match (accepted.exists(), rejected.exists()) {
                (true, false) => PathOutcome::Accept,
                (false, true) => PathOutcome::Reject,
                (true, true) => PathOutcome::Mixed,
                (false, false) => PathOutcome::Inconclusive,
            }
        };
        result.classification = Some(Classification {
            accepted,
            rejected,
            no_meaning,
            ambiguous,
            no_meaning_explanation: None,
        });
        Ok(result)
    }

    /// Prove a target constant over accepted interpretations, retaining helper
    /// freedom. This is a conditional value proof, NOT an acceptance certificate,
    /// proof of scoped existence for every observation, or permission to fabricate
    /// a raw input/task result. Runtime outcome is always `planning_context`.
    /// One cumulative SAT allowance for this pass (its runs share it).
    pub fn planning_constant(
        &self,
        path: &RuntimePath,
        target: &GroundAtom,
        scope: ConstantScope,
        options: &CheckOptions,
    ) -> Result<PlanningConstant> {
        self.scoped()
            .planning_constant_in(path, target, scope, options)
    }
    fn planning_constant_in(
        &self,
        path: &RuntimePath,
        target: &GroundAtom,
        scope: ConstantScope,
        options: &CheckOptions,
    ) -> Result<PlanningConstant> {
        self.program.validate_atom(target)?;
        if scope == ConstantScope::Classification && self.classification.is_none() {
            return Err(CheckError::InvalidRequest(
                "classification constant requires a hypothesis",
            ));
        }
        let context = self.planning_context(path, options)?;
        if !matches!(context.outcome, PathOutcome::Accept | PathOutcome::Mixed) {
            return Ok(PlanningConstant::ContextNotReady(Box::new(context)));
        }
        let answer = self.symbolic_search_in(path, "completion planning constant", 1, |s| {
            let mut members = self
                .classification
                .as_ref()
                .map_or_else(BTreeSet::new, |(_, m, _)| m.as_ref().clone());
            let mut cone = self.classification.as_ref().map_or_else(
                || self.cone.as_ref().clone(),
                |(c, _, _)| c.as_ref().clone(),
            );
            if scope == ConstantScope::Classification
                && !members.contains(target)
                && !self.input_relations.contains(&target.relation)
            {
                return Err(CheckError::InvalidRequest(
                    "target is outside classification scope",
                ));
            }
            if scope == ConstantScope::Output {
                members.extend(
                    self.program
                        .dependency_cone_with_budget([target.clone()], s.run.budget)?
                        .facts,
                );
                cone = self.cone.as_ref().clone();
                cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
            }
            let encoded = s.encode(&cone, true)?;
            let literal = if self.input_relations.contains(&target.relation) {
                s.run.input(target)?
            } else {
                self.program
                    .atom_index
                    .get(target)
                    .map(|i| encoded.encoding.vars[*i])
                    .unwrap_or(!s.run.truth)
            };
            if !s.solve(&[encoded.gate], &[])? {
                return Ok(None);
            }
            let values = s.values(&cone, &encoded)?;
            let mut first = self.model(values, ModelScope::Property);
            members.insert(target.clone());
            first.members = Some(Arc::new(members));
            let value = first.value(target).unwrap();
            if !s.solve(&[encoded.gate], &[if value { !literal } else { literal }])? {
                return Ok(Some(PlanningConstant::Proven {
                    value,
                    example: first,
                }));
            }
            let mut second = self.model(s.values(&cone, &encoded)?, ModelScope::Property);
            second.members = first.members.clone();
            Ok(Some(PlanningConstant::Varying(Pair { first, second })))
        })?;
        Ok(match answer {
            Search::Exists(a) => a,
            Search::None => PlanningConstant::NoInterpretation,
            Search::Inconclusive(c) => PlanningConstant::Inconclusive(c),
            Search::NotAnalysed => unreachable!(),
        })
    }
}

/// Output meaning in the frozen union of explicit root cones and C(H). The
/// requested atoms must be determined even when omitted from declared decisions;
/// other helpers remain free. Classification is audited independently first.
#[derive(Debug, Clone)]
pub struct PlanningOutputs {
    pub context: PlanningContext,
    pub members: BTreeSet<GroundAtom>,
    pub no_meaning: Search<Observation>,
    pub ambiguous: Search<Pair>,
}
impl PlanningOutputs {
    pub fn certified(&self) -> bool {
        matches!(
            self.context.outcome,
            PathOutcome::Accept | PathOutcome::Mixed
        ) && matches!(self.no_meaning, Search::None)
            && matches!(self.ambiguous, Search::None)
    }
}
impl Engine {
    /// One cumulative SAT allowance for this pass (its runs share it).
    pub fn planning_outputs(
        &self,
        path: &RuntimePath,
        targets: &BTreeSet<GroundAtom>,
        options: &CheckOptions,
    ) -> Result<PlanningOutputs> {
        self.scoped().planning_outputs_in(path, targets, options)
    }
    fn planning_outputs_in(
        &self,
        path: &RuntimePath,
        targets: &BTreeSet<GroundAtom>,
        options: &CheckOptions,
    ) -> Result<PlanningOutputs> {
        let mut budget = Budget::new(&self.limits);
        for atom in targets {
            budget.tick("completion planning scope")?;
            self.program.validate_atom(atom)?;
            if self
                .ignored_input_domains
                .iter()
                .any(|i| i.input == atom.relation)
            {
                return Err(CheckError::InvalidRequest(
                    "planning output input domain was omitted; use prepare_for_planning",
                ));
            }
        }
        let context = self.planning_context(path, options)?;
        let mut answer = PlanningOutputs {
            context,
            members: BTreeSet::new(),
            no_meaning: Search::NotAnalysed,
            ambiguous: Search::NotAnalysed,
        };
        if !matches!(
            answer.context.outcome,
            PathOutcome::Accept | PathOutcome::Mixed
        ) {
            return Ok(answer);
        }
        let mut members = self
            .program
            .dependency_cone_with_budget(targets.iter().cloned(), &mut budget)?
            .facts;
        if let Some((_, cm, _)) = &self.classification {
            members.extend(cm.iter().cloned());
        }
        budget.charge(
            self.cone.atoms.len() + self.cone.rules.len(),
            "completion planning scope",
        )?;
        let mut cone = self.cone.as_ref().clone();
        cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
        answer.members = members.clone();
        answer.no_meaning = self.symbolic_no_meaning_cone(path, false, true, options, 1, &cone)?;
        answer.ambiguous =
            self.symbolic_search_in(path, "completion planning output ambiguity", 1, |s| {
                let a = s.encode(&cone, true)?;
                let b = s.encode(&cone, true)?;
                let diff = s.difference_selected(&cone, &a, &b, Some(targets), false)?;
                if !s.solve(&[a.gate, b.gate, diff], &[])? {
                    return Ok(None);
                }
                let mut first = self.model(s.values(&cone, &a)?, ModelScope::Property);
                let mut second = self.model(s.values(&cone, &b)?, ModelScope::Property);
                let members = Arc::new(members);
                first.members = Some(members.clone());
                second.members = Some(members);
                Ok(Some(Pair { first, second }))
            })?;
        Ok(answer)
    }
}

/// One step of the planner's path driver on a runtime path (input pins only).
#[derive(Debug, Clone)]
pub enum PathStep {
    /// No permitted message on the path has an interpretation of the scope (with
    /// H when requested). Never a vacuous constant proof.
    Empty,
    /// Interpretations exist. `constants`: derived atoms of the scope with one
    /// value in all of them. `discharged`: their definitions hold in every
    /// interpretation of the scope with the constants substituted, so the
    /// constants alone define the same interpretations; otherwise the plan must
    /// check each definition at runtime.
    Forced {
        constants: Vec<(GroundAtom, bool)>,
        discharged: bool,
    },
    Inconclusive(Inconclusive),
}
impl Engine {
    /// The driver's satisfiability and forcing question on `path`. Scope: C(H)
    /// when `outputs` is `None` (requires H), else the frozen union of the output
    /// cones and C(H). `hypothesis` adds H (ignored without one).
    pub fn planning_path_step(
        &self,
        path: &RuntimePath,
        outputs: Option<&BTreeSet<GroundAtom>>,
        hypothesis: bool,
    ) -> Result<PathStep> {
        self.scoped()
            .planning_path_step_in(path, outputs, hypothesis)
    }
    fn planning_path_step_in(
        &self,
        path: &RuntimePath,
        outputs: Option<&BTreeSet<GroundAtom>>,
        hypothesis: bool,
    ) -> Result<PathStep> {
        let limits = self.shared_limits(1);
        let mut budget = Budget::new(&limits);
        let cone = match outputs {
            None => match &self.classification {
                Some((c, _, _)) => c.as_ref().clone(),
                None => {
                    return Err(CheckError::InvalidRequest(
                        "a classification step requires a hypothesis",
                    ));
                }
            },
            Some(targets) => {
                for atom in targets {
                    self.program.validate_atom(atom)?;
                }
                let mut members = self
                    .program
                    .dependency_cone_with_budget(targets.iter().cloned(), &mut budget)?
                    .facts;
                if let Some((_, cm, _)) = &self.classification {
                    members.extend(cm.iter().cloned());
                }
                budget.charge(
                    self.cone.atoms.len() + self.cone.rules.len(),
                    "completion planning scope",
                )?;
                let mut cone = self.cone.as_ref().clone();
                cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
                cone
            }
        };
        let satisfiable = self.symbolic_search_in(path, "completion planning path", 1, |s| {
            let encoded = s.encode(&cone, hypothesis)?;
            Ok(s.solve(&[encoded.gate], &[])?.then_some(()))
        })?;
        match satisfiable {
            Search::Exists(()) => {}
            Search::None => return Ok(PathStep::Empty),
            Search::Inconclusive(c) => return Ok(PathStep::Inconclusive(c)),
            Search::NotAnalysed => unreachable!(),
        }
        let mut pins = vec![];
        for (atom, value) in path {
            budget.tick("completion planning path")?;
            if let Some(i) = self.program.atom_index.get(atom) {
                pins.push((*i, *value));
            }
        }
        let forced = (|| {
            branches::force_on_path(self, Arc::new(cone.clone()), hypothesis, &pins, &mut budget)
        })();
        match forced {
            Ok((constants, discharged)) => Ok(PathStep::Forced {
                constants: constants
                    .into_iter()
                    .map(|(i, v)| (cone.atoms[i].clone(), v))
                    .collect(),
                discharged,
            }),
            Err(error) => {
                self.limits.cancellation.check()?;
                Ok(PathStep::Inconclusive(inconclusive(error)?))
            }
        }
    }
}
