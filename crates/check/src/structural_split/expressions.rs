//! Attempt-local hash-consing. Keys refer to owned children, never arena identity
//! outside this attempt. Different leaf values remain different expressions.
use super::*;

const MAX_NODES: usize = 262_144;
const MAX_DEPTH: usize = 256;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Constant(bool),
    Atom(GroundAtom),
    Not(usize),
    All(Vec<usize>),
    Any(Vec<usize>),
}
#[derive(Default)]
pub(super) struct Expressions {
    nodes: BTreeMap<Key, Expr>,
    depths: BTreeMap<usize, usize>,
    pub storage: usize,
}
impl Expressions {
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn intern(
        &mut self,
        expression: Expr,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<Expr> {
        // New expressions have interned children; imported replacements are
        // traversed bottom-up and canonicalized as well.
        if self
            .depths
            .contains_key(&(Arc::as_ptr(&expression) as usize))
        {
            return Ok(expression);
        }
        budget.tick("structural split expression")?;
        let expression = match expression.as_ref() {
            SettledExpression::Not(c) => signed(self.intern(c.clone(), retained, budget)?, true),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                let all = matches!(expression.as_ref(), SettledExpression::All(_));
                let cs = cs
                    .iter()
                    .map(|c| self.intern(c.clone(), retained, budget))
                    .collect::<Result<_>>()?;
                join(cs, all)
            }
            _ => expression,
        };
        let pointer = |c: &Expr| Arc::as_ptr(c) as usize;
        let (key, depth, edges) = match expression.as_ref() {
            SettledExpression::Constant(v) => (Key::Constant(*v), 1, 0),
            SettledExpression::Atom(a) => (Key::Atom(a.clone()), 1, a.arguments.len()),
            SettledExpression::Not(c) => (Key::Not(pointer(c)), self.depths[&pointer(c)] + 1, 1),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                budget.charge(cs.len(), "structural split expression edges")?;
                let children = cs.iter().map(pointer).collect();
                let depth = 1 + cs
                    .iter()
                    .map(|c| self.depths[&pointer(c)])
                    .max()
                    .unwrap_or(0);
                (
                    if matches!(expression.as_ref(), SettledExpression::All(_)) {
                        Key::All(children)
                    } else {
                        Key::Any(children)
                    },
                    depth,
                    cs.len(),
                )
            }
        };
        if let Some(existing) = self.nodes.get(&key) {
            return Ok(existing.clone());
        }
        if depth > MAX_DEPTH || self.nodes.len() >= MAX_NODES {
            return Err(CheckError::limit(
                "structural split",
                if depth > MAX_DEPTH {
                    "expression depth"
                } else {
                    "expression nodes"
                },
                if depth > MAX_DEPTH {
                    MAX_DEPTH
                } else {
                    MAX_NODES
                },
                Some(if depth > MAX_DEPTH {
                    depth
                } else {
                    self.nodes.len() + 1
                }),
            ));
        }
        // Include the interning index, child references and cached depth, not
        // just the immutable expression. Work is never refunded; storage lives
        // until the attempt drops.
        let storage = 4 + 2 * edges;
        budget.charge(storage, "structural split expression storage")?;
        *retained = crate::symbolic::retain(*retained, 0, storage, budget)?;
        self.storage += storage;
        self.depths.insert(pointer(&expression), depth);
        self.nodes.insert(key, expression.clone());
        Ok(expression)
    }
}
