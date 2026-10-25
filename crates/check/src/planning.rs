//! Owned positional plans. The planner reads only variable/constant incidence;
//! relations, constant values and provenance are bound afresh by sparse grounding.
use super::*;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinPlanSchema {
    pub positions: Vec<usize>,
    pub positives: Vec<Vec<Option<Arc<str>>>>,
}
impl JoinPlanSchema {
    pub fn from_schema(schema: &RuleSchema) -> Self {
        let mut out = Self {
            positions: Vec::new(),
            positives: Vec::new(),
        };
        for (i, (negative, atom)) in schema.body.iter().enumerate() {
            if !negative {
                out.positions.push(i);
                out.positives.push(
                    atom.arguments
                        .iter()
                        .map(|(_, t)| match t {
                            TermKey::Constant(_) => None,
                            TermKey::Variable(v) => Some(v.name.clone()),
                        })
                        .collect(),
                );
            }
        }
        out
    }
    pub(super) fn from_rule(rule: &Rule) -> Self {
        let mut out = Self {
            positions: Vec::new(),
            positives: Vec::new(),
        };
        for (i, literal) in rule.body.iter().enumerate() {
            if let Literal::Positive(atom) = literal {
                out.positions.push(i);
                out.positives.push(
                    atom.arguments()
                        .iter()
                        .map(|t| match t.value() {
                            Term::Constant(_) => None,
                            Term::Variable { name, .. } => Some(Arc::from(name.as_str())),
                        })
                        .collect(),
                );
            }
        }
        out
    }
    /// Conservative linear-time preflight for a cold tracked query. Never run
    /// an unbounded pure planner on a request that cannot afford its work.
    pub fn work_bound(&self) -> Option<usize> {
        let n = self.positives.len();
        let a = self.positives.iter().map(Vec::len).max().unwrap_or(0);
        let terms = self
            .positives
            .iter()
            .try_fold(0usize, |s, v| s.checked_add(v.len()))?;
        // new: n+terms; per pivot: constant columns, n+variables+arity+1,
        // argument visits, incidence visits, score scans and output columns.
        let per_pivot = n
            .checked_mul(a.checked_add(1)?)?
            .checked_add(terms.checked_mul(4)?)?
            .checked_add(n)?
            .checked_add(a.checked_mul(2)?)?
            .checked_add(1)?;
        n.checked_add(terms)?.checked_add(n.checked_mul(per_pivot)?)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PivotPlan {
    pub columns: Vec<usize>,
    pub steps: Vec<(usize, Vec<usize>)>,
    pub columns_work: usize,
    pub steps_work: usize,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedJoinPlan {
    pub schema: JoinPlanSchema,
    pub initialization_work: usize,
    pub pivots: Vec<PivotPlan>,
}
impl OwnedJoinPlan {
    /// Pure owned-input computation used by the real session Salsa query.
    /// Operational interruption is checked around this bounded computation.
    pub fn compute(schema: JoinPlanSchema) -> Result<Self> {
        let limits = Limits {
            max_work: usize::MAX,
            timeout: Duration::MAX,
            ..Limits::default()
        };
        let mut budget = Budget::new(&limits);
        let planner = sparse::JoinPlanner::new(&schema.positives, &mut budget)?;
        let initialization_work = budget.used();
        let mut pivots = Vec::new();
        for (i, atom) in schema.positives.iter().enumerate() {
            let before = budget.used();
            let columns = constant_columns(atom, &mut budget)?;
            let columns_work = budget.used() - before;
            let before = budget.used();
            let steps = planner.steps(i, &mut budget)?;
            pivots.push(PivotPlan {
                columns,
                steps,
                columns_work,
                steps_work: budget.used() - before,
            });
        }
        Ok(Self {
            schema,
            initialization_work,
            pivots,
        })
    }
    pub fn required_work(&self) -> Option<usize> {
        let n = self.pivots.len();
        self.pivots
            .iter()
            .try_fold(self.work()?.checked_add(n.checked_mul(n)?)?, |sum, p| {
                sum.checked_add(p.columns.len())
            })
    }
    pub fn work(&self) -> Option<usize> {
        self.pivots
            .iter()
            .try_fold(self.initialization_work, |sum, p| {
                sum.checked_add(p.columns_work)?.checked_add(p.steps_work)
            })
    }
}

pub(super) fn constant_columns(
    atom: &[Option<Arc<str>>],
    budget: &mut Budget<'_>,
) -> Result<Vec<usize>> {
    let mut columns = Vec::new();
    for (i, variable) in atom.iter().enumerate() {
        budget.tick("grounding plans")?;
        if variable.is_none() {
            columns.push(i);
        }
    }
    Ok(columns)
}

/// Storage-neutral boundary. Implementations execute owned plans; borrowed
/// corpus reads only construct inputs and rebind positions, never enter Salsa.
pub trait JoinPlanStore {
    /// Admission policy checked before building owned keys/schema. Rejection
    /// uses the same fresh planner and charge sequence.
    fn should_cache(&mut self, _positive_literals: usize) -> bool {
        true
    }

    fn plan(
        &mut self,
        key: RuleKey,
        schema: RuleSchema,
        remaining: usize,
    ) -> Result<Option<Arc<OwnedJoinPlan>>>;
}
pub struct FreshPlans;
impl JoinPlanStore for FreshPlans {
    fn plan(&mut self, _: RuleKey, _: RuleSchema, _: usize) -> Result<Option<Arc<OwnedJoinPlan>>> {
        Ok(None)
    }
}
