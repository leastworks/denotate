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
    /// This first interface requires an explicit hypothesis.
    pub fn planning_context(
        &self,
        path: &RuntimePath,
        options: &CheckOptions,
    ) -> Result<PlanningContext> {
        if self.classification.is_none() {
            return Err(CheckError::InvalidRequest(
                "planning context requires a hypothesis",
            ));
        }
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
        let ambiguous = self.symbolic_pair_in(path, true, true, options)?;
        let accepted =
            self.symbolic_accepted_in(path, matches!(ambiguous, Search::None), options)?;
        let rejected = self.symbolic_rejected_in(path, options)?;
        let no_meaning = self.symbolic_no_meaning_in(path, true, true, options)?;
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
        });
        Ok(result)
    }

    /// Prove a target constant over accepted interpretations, retaining helper
    /// freedom. This is a conditional value proof, NOT an acceptance certificate,
    /// proof of scoped existence for every observation, or permission to fabricate
    /// a raw input/task result. Runtime outcome is always `planning_context`.
    pub fn planning_constant(
        &self,
        path: &RuntimePath,
        target: &GroundAtom,
        scope: ConstantScope,
        options: &CheckOptions,
    ) -> Result<PlanningConstant> {
        self.program.validate_atom(target)?;
        let context = self.planning_context(path, options)?;
        if !matches!(context.outcome, PathOutcome::Accept | PathOutcome::Mixed) {
            return Ok(PlanningConstant::ContextNotReady(Box::new(context)));
        }
        let answer = self.symbolic_search_in(path, "completion planning constant", |s| {
            let (classification, cm, _) = self.classification.as_ref().unwrap();
            let mut members = cm.as_ref().clone();
            let mut cone = classification.clone();
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
                cone = self.cone.clone();
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
