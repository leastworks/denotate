//! Bounded executable Boolean expressions introduced by justified admission.
//! Leaves are globally settled atoms; source occurrences stay on the replacement.
use crate::{
    limits::{Budget, Result},
    *,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Debug, Clone)]
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
        let mut seen = BTreeSet::new();
        std::iter::from_fn(move || {
            while let Some(node) = pending.pop() {
                if !seen.insert(node as *const Self) {
                    continue;
                }
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
        Self::shared_nodes([self])
    }
    /// Count retained DAG nodes once across all roots; pointer identity is only
    /// temporary traversal state, never a semantic key or ordering choice.
    pub(crate) fn shared_nodes<'a>(roots: impl IntoIterator<Item = &'a Self>) -> usize
    where
        A: 'a,
    {
        let mut pending: Vec<_> = roots.into_iter().collect();
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node as *const Self) {
                continue;
            }
            match node {
                Self::Not(c) => pending.push(c),
                Self::All(cs) | Self::Any(cs) => pending.extend(cs.iter().map(AsRef::as_ref)),
                _ => {}
            }
        }
        seen.len()
    }
    pub fn map<B>(&self, f: &mut impl FnMut(&A) -> Result<B>) -> Result<Arc<SettledExpression<B>>> {
        ExpressionMap::default().map(self, f)
    }
    pub(crate) fn evaluate(
        &self,
        atom: &mut impl FnMut(&A) -> Result<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        self.evaluate_cached(atom, budget, &mut BTreeMap::new())
    }
    fn evaluate_cached(
        &self,
        atom: &mut impl FnMut(&A) -> Result<bool>,
        budget: &mut Budget<'_>,
        cache: &mut BTreeMap<*const Self, bool>,
    ) -> Result<bool> {
        let key = self as *const _;
        if let Some(value) = cache.get(&key) {
            return Ok(*value);
        }
        budget.tick("settled expression")?;
        let result = match self {
            Self::Constant(v) => *v,
            Self::Atom(a) => atom(a)?,
            Self::Not(c) => !c.evaluate_cached(atom, budget, cache)?,
            Self::All(cs) => {
                let mut result = true;
                for c in cs {
                    if !c.evaluate_cached(atom, budget, cache)? {
                        result = false;
                        break;
                    }
                }
                result
            }
            Self::Any(cs) => {
                let mut result = false;
                for c in cs {
                    if c.evaluate_cached(atom, budget, cache)? {
                        result = true;
                        break;
                    }
                }
                result
            }
        };
        cache.insert(key, result);
        Ok(result)
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
                let mut seen = BTreeSet::new();
                std::iter::from_fn(move || {
                    while let Some((node, negative)) = stack.pop() {
                        if !seen.insert((node as *const _, negative)) {
                            continue;
                        }
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

/// One mapping scope per immutable graph/query. Reusing it across roots preserves
/// shared expressions across rules as well as within an individual replacement.
pub(crate) struct ExpressionMap<A, B> {
    mapped: BTreeMap<*const SettledExpression<A>, Arc<SettledExpression<B>>>,
}
impl<A, B> Default for ExpressionMap<A, B> {
    fn default() -> Self {
        Self {
            mapped: BTreeMap::new(),
        }
    }
}
impl<A, B> ExpressionMap<A, B> {
    pub fn map(
        &mut self,
        root: &SettledExpression<A>,
        f: &mut impl FnMut(&A) -> Result<B>,
    ) -> Result<Arc<SettledExpression<B>>> {
        let mut pending = vec![(root, false)];
        while let Some((node, ready)) = pending.pop() {
            let key = node as *const _;
            if self.mapped.contains_key(&key) {
                continue;
            }
            if !ready {
                pending.push((node, true));
                match node {
                    SettledExpression::Not(c) => pending.push((c, false)),
                    SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                        pending.extend(cs.iter().rev().map(|c| (c.as_ref(), false)))
                    }
                    _ => {}
                }
                continue;
            }
            let child = |c: &Arc<SettledExpression<A>>| self.mapped[&Arc::as_ptr(c)].clone();
            let mapped = match node {
                SettledExpression::Constant(v) => SettledExpression::Constant(*v),
                SettledExpression::Atom(a) => SettledExpression::Atom(f(a)?),
                SettledExpression::Not(c) => SettledExpression::Not(child(c)),
                SettledExpression::All(cs) => {
                    SettledExpression::All(cs.iter().map(child).collect())
                }
                SettledExpression::Any(cs) => {
                    SettledExpression::Any(cs.iter().map(child).collect())
                }
            };
            self.mapped.insert(key, Arc::new(mapped));
        }
        Ok(self.mapped[&(root as *const _)].clone())
    }
}

// Structural equality and hashing ignore sharing layout. Visit each shared node
// once, so projecting a DAG cannot turn a cache lookup into tree expansion.
impl<A: PartialEq> PartialEq for SettledExpression<A> {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        let mut seen = BTreeSet::new();
        while let Some((a, b)) = pending.pop() {
            if std::ptr::eq(a, b) || !seen.insert((a as *const _, b as *const _)) {
                continue;
            }
            match (a, b) {
                (Self::Constant(a), Self::Constant(b)) if a == b => {}
                (Self::Atom(a), Self::Atom(b)) if a == b => {}
                (Self::Not(a), Self::Not(b)) => pending.push((a, b)),
                (Self::All(a), Self::All(b)) | (Self::Any(a), Self::Any(b))
                    if a.len() == b.len() =>
                {
                    pending.extend(a.iter().zip(b).map(|(a, b)| (a.as_ref(), b.as_ref())))
                }
                _ => return false,
            }
        }
        true
    }
}
impl<A: Eq> Eq for SettledExpression<A> {}
impl<A: std::hash::Hash> std::hash::Hash for SettledExpression<A> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        use std::hash::Hasher;
        let mut hashes: BTreeMap<*const Self, u64> = BTreeMap::new();
        let mut pending = vec![(self, false)];
        while let Some((node, ready)) = pending.pop() {
            let key = node as *const _;
            if hashes.contains_key(&key) {
                continue;
            }
            if !ready {
                pending.push((node, true));
                match node {
                    Self::Not(c) => pending.push((c, false)),
                    Self::All(cs) | Self::Any(cs) => {
                        pending.extend(cs.iter().rev().map(|c| (c.as_ref(), false)))
                    }
                    _ => {}
                }
                continue;
            }
            let mut h = std::collections::hash_map::DefaultHasher::new();
            std::mem::discriminant(node).hash(&mut h);
            match node {
                Self::Constant(v) => v.hash(&mut h),
                Self::Atom(a) => a.hash(&mut h),
                Self::Not(c) => hashes[&Arc::as_ptr(c)].hash(&mut h),
                Self::All(cs) | Self::Any(cs) => {
                    cs.len().hash(&mut h);
                    for c in cs {
                        hashes[&Arc::as_ptr(c)].hash(&mut h);
                    }
                }
            }
            hashes.insert(key, h.finish());
        }
        state.write_u64(hashes[&(self as *const _)]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    #[test]
    fn shared_projection_rebinding_hashing_and_evaluation_do_not_expand_the_tree() {
        let mut root = Arc::new(SettledExpression::Atom(7));
        for _ in 0..100 {
            root = Arc::new(SettledExpression::All(vec![root.clone(), root]));
        }
        let other = Arc::new(SettledExpression::Not(root.clone()));
        let mut projection = ExpressionMap::default();
        let mut visited = 0;
        let mut key = |a: &i32| {
            visited += 1;
            Ok(a.to_string())
        };
        let projected = projection.map(&root, &mut key).unwrap();
        let sibling = projection.map(&other, &mut key).unwrap();
        assert_eq!(visited, 1);
        let SettledExpression::Not(child) = sibling.as_ref() else {
            panic!()
        };
        assert!(Arc::ptr_eq(&projected, child));
        let rebound = projected
            .map(&mut |a| Ok(a.parse::<i32>().unwrap()))
            .unwrap();
        assert_eq!(root, rebound);
        let hash = |e: &SettledExpression<i32>| {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            e.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&root), hash(&rebound));
        assert_eq!(root.nodes(), rebound.nodes());
        let mut reads = 0;
        assert!(
            rebound
                .evaluate(
                    &mut |_| {
                        reads += 1;
                        Ok(true)
                    },
                    &mut Budget::new(&Limits::default())
                )
                .unwrap()
        );
        assert_eq!(reads, 1);
        let separate = SettledExpression::All(vec![
            Arc::new(SettledExpression::Atom(7)),
            Arc::new(SettledExpression::Atom(7)),
        ]);
        let leaf = Arc::new(SettledExpression::Atom(7));
        let shared = SettledExpression::All(vec![leaf.clone(), leaf]);
        assert_eq!(separate, shared);
        assert_eq!(hash(&separate), hash(&shared));
    }
}
