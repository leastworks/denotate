//! Advisory condition analysis. Independent allowances keep notices from consuming
//! obligation budgets; only settled conditions and replayed worlds yield labels.
use crate::{
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function;
use denotate_ir::RelationId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NoticeState {
    Impossible,
    AlwaysTrue,
    Varying,
    ParentUnreachable,
    Unknown(NoticeUnknown),
}
impl NoticeState {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Impossible => "impossible",
            Self::AlwaysTrue => "always-true",
            Self::Varying => "varying",
            Self::ParentUnreachable => "parent-unreachable",
            Self::Unknown(_) => "unknown",
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NoticeUnknown {
    Unsupported,
    Inconclusive(Inconclusive),
    Deadline,
    InconsistentAssumptions,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoticeWitness {
    pub observation: Observation,
    pub replay_scope: ReplayScope,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionAnalysis {
    pub state: NoticeState,
    pub when_true: Option<NoticeWitness>,
    pub when_false: Option<NoticeWitness>,
}
impl ConditionAnalysis {
    fn state(state: NoticeState) -> Self {
        Self {
            state,
            when_true: None,
            when_false: None,
        }
    }
    fn unknown(reason: NoticeUnknown) -> Self {
        Self::state(NoticeState::Unknown(reason))
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoticeExample {
    pub observation: Candidate,
    pub replay_scope: ReplayScope,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoticeResult {
    pub state: NoticeState,
    pub when_true: Option<NoticeExample>,
    pub when_false: Option<NoticeExample>,
}

impl GroundProgram {
    pub fn analyze_condition(
        &self,
        condition: RelationId,
        within: Option<RelationId>,
        limits: &Limits,
    ) -> Result<ConditionAnalysis> {
        self.analyze_condition_with_budget(condition, within, &mut Budget::new(limits))
    }
    pub(crate) fn analyze_condition_with_budget(
        &self,
        condition: RelationId,
        within: Option<RelationId>,
        budget: &mut Budget<'_>,
    ) -> Result<ConditionAnalysis> {
        let condition = GroundAtom::new(condition, []);
        let parent = within.map(|r| GroundAtom::new(r, []));
        self.validate_atom(&condition)?;
        if let Some(p) = &parent {
            self.validate_atom(p)?;
        }
        budget.limits.cancellation.check()?;
        if !self.assumptions_consistent() {
            return Ok(ConditionAnalysis::unknown(
                NoticeUnknown::InconsistentAssumptions,
            ));
        }
        let run = (|| {
            let meaning = self.symbolic_impl(budget, true)?;
            let ctx = meaning.context();
            let settled =
                |a: &GroundAtom| -> Result<std::result::Result<Condition, NoticeUnknown>> {
                    Ok(match meaning.fact(a)? {
                        SymbolicFact::Settled(c) => Ok(c),
                        SymbolicFact::Blocked(_) => Err(NoticeUnknown::Unsupported),
                        SymbolicFact::Inconclusive(c) => Err(NoticeUnknown::Inconclusive(c)),
                    })
                };
            let p = match parent.as_ref().map(&settled).transpose()? {
                None => ctx.true_condition(),
                Some(Ok(c)) => c,
                Some(Err(reason)) => return Ok(ConditionAnalysis::unknown(reason)),
            };
            let p = ctx.restrict(&p, budget)?;
            if p.is_false() {
                return Ok(ConditionAnalysis::state(NoticeState::ParentUnreachable));
            }
            let g = match settled(&condition)? {
                Ok(c) => c,
                Err(reason) => return Ok(ConditionAnalysis::unknown(reason)),
            };
            let yes = ctx.apply(&p, &g, op_function::and, budget)?;
            let no = ctx.apply(&p, &g, op_function::and_not, budget)?;
            let mut retained = meaning.metrics().retained_condition_nodes;
            for c in [&p, &yes, &no] {
                retained = crate::symbolic::retain(retained, 0, c.node_count(), budget)?;
            }
            let mut witness = |c: &Condition, expected: bool| -> Result<Option<NoticeWitness>> {
                let Some(observation) = ctx.witness_with_budget(c, budget)? else {
                    return Ok(None);
                };
                let replay =
                    self.evaluate_selected(observation.present.iter().cloned(), None, budget)?;
                if !matches!(replay.fact(&condition)?, FactState::Settled(v) if v == expected) {
                    return Err(CheckError::Internal("notice witness did not replay"));
                }
                if let Some(parent) = &parent {
                    if !matches!(replay.fact(parent)?, FactState::Settled(true)) {
                        return Err(CheckError::Internal("notice parent witness did not replay"));
                    }
                }
                Ok(Some(NoticeWitness {
                    observation,
                    replay_scope: if self.is_admitted() {
                        ReplayScope::WholeProgram
                    } else {
                        ReplayScope::ConeOnly
                    },
                }))
            };
            let when_true = witness(&yes, true)?;
            let when_false = witness(&no, false)?;
            let state = match (when_true.is_some(), when_false.is_some()) {
                (true, true) => NoticeState::Varying,
                (true, false) => NoticeState::AlwaysTrue,
                (false, true) => NoticeState::Impossible,
                (false, false) => {
                    return Err(CheckError::Internal("reachable notice parent has no world"));
                }
            };
            Ok(ConditionAnalysis {
                state,
                when_true,
                when_false,
            })
        })();
        match run {
            Err(e @ CheckError::LimitExceeded { .. }) => {
                budget.failure(&e);
                Ok(ConditionAnalysis::unknown(NoticeUnknown::Inconclusive(
                    Inconclusive::from_error(e)?,
                )))
            }
            Err(CheckError::Deadline { .. }) => {
                Ok(ConditionAnalysis::unknown(NoticeUnknown::Deadline))
            }
            other => other,
        }
    }
}
