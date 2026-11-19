use super::*;

/// A topologically ordered Boolean DAG. Child indices must precede their parent.
/// The root need not be the last node. Leaves name values, not readiness assertions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression {
    pub nodes: Vec<ExpressionNode>,
    pub root: usize,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExpressionNode {
    Constant(bool),
    Atom(GroundAtom),
    Not(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
    If {
        atom: GroundAtom,
        when_true: usize,
        when_false: usize,
    },
}
impl ExpressionNode {
    pub(super) fn children(&self) -> &[usize] {
        match self {
            Self::Not(i) => std::slice::from_ref(i),
            Self::And(xs) | Self::Or(xs) => xs,
            _ => &[],
        }
    }
    pub(super) fn atom(&self) -> Option<&GroundAtom> {
        match self {
            Self::Atom(a) | Self::If { atom: a, .. } => Some(a),
            _ => None,
        }
    }
    pub(super) fn valid_at(&self, i: usize) -> bool {
        match self {
            Self::If {
                when_true,
                when_false,
                ..
            } => *when_true < i && *when_false < i,
            _ => self.children().iter().all(|j| *j < i),
        }
    }
    fn mark_children(&self, used: &mut [bool]) {
        match self {
            Self::If {
                when_true,
                when_false,
                ..
            } => {
                used[*when_true] = true;
                used[*when_false] = true;
            }
            _ => {
                for j in self.children() {
                    used[*j] = true;
                }
            }
        }
    }
}
impl Expression {
    fn reachable(&self) -> Option<Vec<bool>> {
        if self.root >= self.nodes.len()
            || self.nodes.iter().enumerate().any(|(i, n)| !n.valid_at(i))
        {
            return None;
        }
        let mut used = vec![false; self.nodes.len()];
        used[self.root] = true;
        for i in (0..=self.root).rev() {
            if used[i] {
                self.nodes[i].mark_children(&mut used);
            }
        }
        Some(used)
    }
    /// Actual referenced values. Invalid DAGs return None. This does not certify
    /// their runtime availability; the caller owns the execution schedule.
    pub fn dependencies(&self) -> Option<BTreeSet<GroundAtom>> {
        let used = self.reachable()?;
        Some(
            self.nodes
                .iter()
                .zip(used)
                .filter_map(|(n, used)| used.then(|| n.atom().cloned()).flatten())
                .collect(),
        )
    }
    /// Evaluate with supplied values only; no access to the checker or its model.
    /// Returns None for an invalid DAG or a missing referenced value.
    pub fn evaluate(&self, mut value: impl FnMut(&GroundAtom) -> Option<bool>) -> Option<bool> {
        let used = self.reachable()?;
        let mut values = vec![false; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            if !used[i] {
                continue;
            }
            values[i] = match n {
                ExpressionNode::Constant(v) => *v,
                ExpressionNode::Atom(a) => value(a)?,
                ExpressionNode::Not(j) => !values[*j],
                ExpressionNode::And(js) => js.iter().all(|j| values[*j]),
                ExpressionNode::Or(js) => js.iter().any(|j| values[*j]),
                ExpressionNode::If {
                    atom,
                    when_true,
                    when_false,
                } => {
                    values[if value(atom)? {
                        *when_true
                    } else {
                        *when_false
                    }]
                }
            };
        }
        Some(values[self.root])
    }
    pub(super) fn compact(self) -> Self {
        let used = self
            .reachable()
            .expect("constructed topological expression");
        let mut map = vec![0; self.nodes.len()];
        let mut nodes = Vec::new();
        for (i, n) in self.nodes.into_iter().enumerate() {
            if !used[i] {
                continue;
            }
            map[i] = nodes.len();
            nodes.push(match n {
                ExpressionNode::Not(j) => ExpressionNode::Not(map[j]),
                ExpressionNode::And(js) => {
                    ExpressionNode::And(js.into_iter().map(|j| map[j]).collect())
                }
                ExpressionNode::Or(js) => {
                    ExpressionNode::Or(js.into_iter().map(|j| map[j]).collect())
                }
                ExpressionNode::If {
                    atom,
                    when_true,
                    when_false,
                } => ExpressionNode::If {
                    atom,
                    when_true: map[when_true],
                    when_false: map[when_false],
                },
                n => n,
            });
        }
        Self {
            root: map[self.root],
            nodes,
        }
    }
}
