//! Bounded executable Boolean expressions introduced by justified admission.
//! Leaves are globally settled atoms; source occurrences stay on the replacement.
use crate::{
    limits::{Budget, Result},
    *,
};
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SettledExpression<A> {
    Constant(bool),
    Atom(A),
    Not(Arc<Self>),
    All(Vec<Arc<Self>>),
    Any(Vec<Arc<Self>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SettledReplacement<A, O> {
    /// The replaced occurrence in the original authored rule.
    pub occurrence: O,
    /// Signed truth of that premise, not the unsigned atom.
    pub expression: Arc<SettledExpression<A>>,
}

impl<A> SettledExpression<A> {
    pub fn atoms(&self) -> impl Iterator<Item = &A> {
        let mut pending = vec![self];
        std::iter::from_fn(move || {
            while let Some(node) = pending.pop() {
                match node {
                    Self::Atom(atom) => return Some(atom),
                    Self::Not(child) => pending.push(child),
                    Self::All(children) | Self::Any(children) => {
                        pending.extend(children.iter().rev().map(AsRef::as_ref))
                    }
                    Self::Constant(_) => {}
                }
            }
            None
        })
    }
    pub fn nodes(&self) -> usize {
        match self {
            Self::Constant(_) | Self::Atom(_) => 1,
            Self::Not(child) => 1 + child.nodes(),
            Self::All(children) | Self::Any(children) => {
                1 + children.iter().map(|c| c.nodes()).sum::<usize>()
            }
        }
    }
    pub fn map<B>(&self, f: &mut impl FnMut(&A) -> Result<B>) -> Result<Arc<SettledExpression<B>>> {
        Ok(Arc::new(match self {
            Self::Constant(v) => SettledExpression::Constant(*v),
            Self::Atom(a) => SettledExpression::Atom(f(a)?),
            Self::Not(c) => SettledExpression::Not(c.map(f)?),
            Self::All(cs) => {
                SettledExpression::All(cs.iter().map(|c| c.map(f)).collect::<Result<_>>()?)
            }
            Self::Any(cs) => {
                SettledExpression::Any(cs.iter().map(|c| c.map(f)).collect::<Result<_>>()?)
            }
        }))
    }
    pub(crate) fn evaluate(
        &self,
        atom: &mut impl FnMut(&A) -> Result<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        budget.tick("settled expression")?;
        Ok(match self {
            Self::Constant(v) => *v,
            Self::Atom(a) => atom(a)?,
            Self::Not(c) => !c.evaluate(atom, budget)?,
            Self::All(cs) => {
                let mut result = true;
                for c in cs {
                    if !c.evaluate(atom, budget)? {
                        result = false;
                        break;
                    }
                }
                result
            }
            Self::Any(cs) => {
                let mut result = false;
                for c in cs {
                    if c.evaluate(atom, budget)? {
                        result = true;
                        break;
                    }
                }
                result
            }
        })
    }
}

impl SettledExpression<GroundAtom> {
    pub(crate) fn symbolic(
        &self,
        ctx: &ConditionContext,
        atom: &mut impl FnMut(&GroundAtom) -> Result<Condition>,
        budget: &mut Budget<'_>,
    ) -> Result<Condition> {
        budget.tick("settled expression")?;
        match self {
            Self::Constant(v) => Ok(if *v {
                ctx.true_condition()
            } else {
                ctx.false_condition()
            }),
            Self::Atom(a) => atom(a),
            Self::Not(c) => ctx.complement(&c.symbolic(ctx, atom, budget)?, budget),
            Self::All(cs) | Self::Any(cs) => {
                let all = matches!(self, Self::All(_));
                let mut value = if all {
                    ctx.true_condition()
                } else {
                    ctx.false_condition()
                };
                for c in cs {
                    let next = c.symbolic(ctx, atom, budget)?;
                    value = ctx.apply(
                        &value,
                        &next,
                        if all {
                            biodivine_lib_bdd::op_function::and
                        } else {
                            biodivine_lib_bdd::op_function::or
                        },
                        budget,
                    )?;
                }
                Ok(value)
            }
        }
    }
}

impl GroundRule {
    /// Executable dependency leaves, preserving their sign and authored target.
    pub(crate) fn dependency_literals(&self) -> impl Iterator<Item = GroundLiteral> + '_ {
        self.body
            .iter()
            .cloned()
            .chain(self.replacements.iter().flat_map(|replacement| {
                let mut stack = vec![(replacement.expression.as_ref(), false)];
                std::iter::from_fn(move || {
                    while let Some((node, negative)) = stack.pop() {
                        match node {
                            SettledExpression::Atom(atom) => {
                                return Some(GroundLiteral {
                                    polarity: if negative {
                                        Polarity::Negative
                                    } else {
                                        Polarity::Positive
                                    },
                                    term: GroundOccurrence {
                                        atom: atom.clone(),
                                        occurrence: replacement.occurrence,
                                        arguments: vec![],
                                    },
                                });
                            }
                            SettledExpression::Not(c) => stack.push((c, !negative)),
                            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                                stack.extend(cs.iter().rev().map(|c| (c.as_ref(), negative)))
                            }
                            SettledExpression::Constant(_) => {}
                        }
                    }
                    None
                })
            }))
    }
}
