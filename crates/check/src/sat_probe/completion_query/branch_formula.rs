//! Total input formulas certified in a particular scope and W/H branch view.
//! A pin retains this formula even when Fitting substitutes its derived atom.
use super::*;

#[derive(Clone)]
pub(super) enum Node {
    Constant(bool),
    Input(usize),
    Definition(Vec<Vec<(usize, bool)>>),
}
#[derive(Clone)]
pub(super) struct SettledAtom {
    pub atom: usize,
    pub scope: Arc<Vec<usize>>,
    pub context: PruningContext,
    nodes: Vec<Node>,
}
#[derive(Clone)]
pub(super) struct Pin {
    pub certificate: Arc<SettledAtom>,
    pub value: bool,
}
impl SettledAtom {
    /// Iterative postorder: every live producer must have wholly acyclic upstream.
    /// Fixed atoms are terminals; a positive cycle is just as ineligible as an odd one.
    pub fn build(
        c: &Cone,
        producers: &[Vec<usize>],
        atom: usize,
        scope: Arc<Vec<usize>>,
        context: PruningContext,
        b: &mut Budget<'_>,
    ) -> Result<Option<Arc<Self>>> {
        if c.input[atom] || c.fixed[atom].is_some() {
            return Ok(None);
        }
        let mut visiting = BTreeSet::new();
        let mut indices = BTreeMap::new();
        let mut nodes = vec![];
        let mut stack = vec![(atom, false)];
        while let Some((i, exit)) = stack.pop() {
            b.tick("completion branch formula")?;
            if indices.contains_key(&i) {
                continue;
            }
            if !exit {
                if !visiting.insert(i) {
                    return Ok(None);
                }
                stack.push((i, true));
                if c.fixed[i].is_none() && !c.input[i] {
                    for r in &producers[i] {
                        let rule = &c.rules[*r];
                        b.charge(rule.body.len() + 1, "completion branch formula")?;
                        for (j, _) in &rule.body {
                            if !indices.contains_key(j) {
                                stack.push((*j, false));
                            }
                        }
                    }
                }
            } else {
                let node = if let Some(v) = c.fixed[i] {
                    Node::Constant(v)
                } else if c.input[i] {
                    Node::Input(i)
                } else {
                    let mut bodies = vec![];
                    for r in &producers[i] {
                        b.charge(c.rules[*r].body.len() + 1, "completion branch formula")?;
                        bodies.push(
                            c.rules[*r]
                                .body
                                .iter()
                                .map(|(j, p)| (indices[j], *p))
                                .collect(),
                        );
                    }
                    Node::Definition(bodies)
                };
                visiting.remove(&i);
                indices.insert(i, nodes.len());
                nodes.push(node);
            }
        }
        // A directly exhaustive pair gives no useful partition. This only
        // declines a candidate; it installs no forced atom or proof.
        if let Some(Node::Definition(bodies)) = nodes.last() {
            let singles: BTreeSet<_> = bodies
                .iter()
                .filter_map(|b| (b.len() == 1).then(|| b[0]))
                .collect();
            if singles.iter().any(|(i, p)| singles.contains(&(*i, !*p))) {
                return Ok(None);
            }
        }
        Ok(Some(Arc::new(Self {
            atom,
            scope,
            context,
            nodes,
        })))
    }
    pub fn encode(
        &self,
        inputs: &[Lit],
        truth: Lit,
        cnf: &mut Cnf,
        b: &mut Budget<'_>,
    ) -> Result<Lit> {
        let mut values: Vec<Lit> = vec![];
        let mut booleans = encoding::Booleans::new(truth);
        for node in &self.nodes {
            b.tick("completion branch formula encoding")?;
            values.push(match node {
                Node::Constant(v) => {
                    if *v {
                        truth
                    } else {
                        !truth
                    }
                }
                Node::Input(i) => inputs[*i],
                Node::Definition(bs) => {
                    let mut bodies = vec![];
                    for body in bs {
                        b.charge(body.len() + 1, "completion branch formula encoding")?;
                        let lits: Vec<Lit> = body
                            .iter()
                            .map(|(i, p)| if *p { values[*i] } else { !values[*i] })
                            .collect();
                        bodies.push(booleans.and(&lits, cnf, b)?);
                    }
                    booleans.or(&bodies, cnf, b)?
                }
            });
        }
        Ok(*values.last().unwrap())
    }
    pub fn evaluate(&self, input: impl Fn(usize) -> bool, b: &mut Budget<'_>) -> Result<bool> {
        let mut values = vec![];
        for node in &self.nodes {
            b.tick("completion branch formula replay")?;
            let v = match node {
                Node::Constant(v) => *v,
                Node::Input(i) => input(*i),
                Node::Definition(bs) => {
                    b.charge(
                        bs.iter().map(|body| body.len() + 1).sum(),
                        "completion branch formula replay",
                    )?;
                    bs.iter()
                        .any(|body| body.iter().all(|(i, p)| values[*i] == *p))
                }
            };
            values.push(v);
        }
        Ok(*values.last().unwrap())
    }
}
