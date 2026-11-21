//! Original dependency scopes, independent of impossible-producer pruning.
//! Project one dependency at a time: variables occurring only in other premises
//! do not create Cartesian copies of the same edge. Shared pattern nodes compact
//! edges such as p(X) -> q(Y), without changing reachability or recursion.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Arg {
    Constant(ConstantId),
    Variable(usize, SortId),
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Pattern {
    relation: RelationId,
    arguments: Vec<Arg>,
}
#[derive(Clone)]
struct Template {
    head: Pattern,
    body: Vec<(Pattern, bool)>,
}
#[derive(Clone)]
pub(crate) struct OriginalDependencies {
    templates: BTreeMap<RelationId, Vec<Template>>,
    domains: Domains,
    heads: BTreeMap<RelationId, BTreeMap<Vec<usize>, BTreeMap<Vec<ConstantId>, Vec<usize>>>>,
}
pub(crate) struct OriginalCone {
    pub(crate) facts: BTreeSet<GroundAtom>,
    pub(crate) cycle: Option<Vec<GroundAtom>>,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Atom(GroundAtom),
    Pattern(Pattern),
}
impl OriginalDependencies {
    pub(crate) fn new(corpus: &Corpus, domains: &Domains, b: &mut Budget<'_>) -> Result<Self> {
        let domains = validate_domains(corpus, domains, b)?;
        let mut templates = BTreeMap::<_, Vec<_>>::new();
        for rule in corpus.rules() {
            b.tick("completion original dependencies")?;
            let mut variables = BTreeMap::new();
            let mut possible = true;
            for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
                for term in atom.arguments() {
                    b.tick("completion original dependencies")?;
                    if let Term::Variable { name, sort } = term.value() {
                        let next = variables.len();
                        variables.entry(name.as_str()).or_insert(next);
                        possible &= !domains[sort].is_empty();
                    }
                }
            }
            // An empty variable domain means no original ground instance exists.
            if !possible {
                continue;
            }
            let project = |atom: &Atom| Pattern {
                relation: atom.relation(),
                arguments: atom
                    .arguments()
                    .iter()
                    .map(|t| match t.value() {
                        Term::Constant(c) => Arg::Constant(*c),
                        Term::Variable { name, sort } => {
                            Arg::Variable(variables[name.as_str()], *sort)
                        }
                    })
                    .collect(),
            };
            templates
                .entry(rule.head.relation())
                .or_default()
                .push(Template {
                    head: project(&rule.head),
                    body: rule
                        .body
                        .iter()
                        .map(|l| (project(l.atom()), matches!(l, Literal::Positive(_))))
                        .collect(),
                });
        }
        let mut heads = BTreeMap::<
            RelationId,
            BTreeMap<Vec<usize>, BTreeMap<Vec<ConstantId>, Vec<usize>>>,
        >::new();
        for (relation, ts) in &templates {
            for (i, t) in ts.iter().enumerate() {
                b.charge(t.head.arguments.len() + 1, "completion original head index")?;
                let mut columns = Vec::new();
                let mut key = Vec::new();
                for (j, a) in t.head.arguments.iter().enumerate() {
                    if let Arg::Constant(c) = a {
                        columns.push(j);
                        key.push(*c);
                    }
                }
                heads
                    .entry(*relation)
                    .or_default()
                    .entry(columns)
                    .or_default()
                    .entry(key)
                    .or_default()
                    .push(i);
            }
        }
        Ok(Self {
            templates,
            domains,
            heads,
        })
    }
    pub(crate) fn cone(
        &self,
        roots: impl IntoIterator<Item = GroundAtom>,
        b: &mut Budget<'_>,
    ) -> Result<OriginalCone> {
        self.walk(roots.into_iter().map(Node::Atom).collect(), None, b)
    }
    pub(crate) fn relation_cone(
        &self,
        relation: RelationId,
        roots: impl IntoIterator<Item = GroundAtom>,
        b: &mut Budget<'_>,
    ) -> Result<OriginalCone> {
        let mut pending: Vec<_> = roots.into_iter().map(Node::Atom).collect();
        if let Some(ts) = self.templates.get(&relation) {
            for t in ts {
                b.tick("completion original roots")?;
                pending.push(Node::Pattern(canonical(&t.head, &BTreeMap::new())));
            }
        }
        self.walk(pending, None, b)
    }
    pub(crate) fn positive_component(
        &self,
        root: &GroundAtom,
        b: &mut Budget<'_>,
    ) -> Result<BTreeSet<GroundAtom>> {
        let cone = self.walk(vec![Node::Atom(root.clone())], Some(root), b)?;
        Ok(cone
            .cycle
            .unwrap_or_else(|| vec![root.clone()])
            .into_iter()
            .collect())
    }
    fn walk(
        &self,
        roots: Vec<Node>,
        positive_root: Option<&GroundAtom>,
        b: &mut Budget<'_>,
    ) -> Result<OriginalCone> {
        let mut nodes = Vec::new();
        let mut ids = BTreeMap::new();
        let mut edges = Vec::new();
        let mut atoms = BTreeSet::new();
        let mut dependencies = 0;
        for node in roots {
            insert(node, &mut nodes, &mut ids, &mut atoms, b)?;
        }
        let mut cursor = 0;
        while cursor < nodes.len() {
            let node = nodes[cursor].clone();
            b.tick("completion original dependencies")?;
            let mut adjacent = BTreeSet::new();
            let mut add = |node, budget: &mut Budget<'_>| -> Result<()> {
                budget.room(
                    dependencies,
                    budget.limits.max_dependencies,
                    "completion original dependencies",
                    "dependencies",
                )?;
                let id = insert(node, &mut nodes, &mut ids, &mut atoms, budget)?;
                if adjacent.insert(id) {
                    dependencies += 1;
                }
                Ok(())
            };
            match node {
                Node::Atom(atom) => {
                    let mut selected = Vec::new();
                    for (columns, index) in self.heads.get(&atom.relation).into_iter().flatten() {
                        b.charge(columns.len() + 1, "completion original head lookup")?;
                        let key: Vec<_> = columns.iter().map(|i| atom.arguments[*i]).collect();
                        if let Some(ids) = index.get(&key) {
                            b.charge(ids.len(), "completion original head lookup")?;
                            selected.extend(ids.iter().copied());
                        }
                    }
                    for i in selected {
                        let t = &self.templates[&atom.relation][i];
                        b.charge(
                            t.head.arguments.len() + 1,
                            "completion original dependencies",
                        )?;
                        let mut binding = BTreeMap::new();
                        let matched =
                            t.head
                                .arguments
                                .iter()
                                .zip(&atom.arguments)
                                .all(|(arg, value)| match arg {
                                    Arg::Constant(c) => c == value,
                                    Arg::Variable(v, _) => {
                                        binding.insert(*v, *value).is_none_or(|old| old == *value)
                                    }
                                });
                        if !matched {
                            continue;
                        }
                        for (premise, positive) in &t.body {
                            if positive_root.is_some() && !positive {
                                continue;
                            }
                            b.charge(
                                premise.arguments.len() + 1,
                                "completion original dependencies",
                            )?;
                            add(Node::Pattern(canonical(premise, &binding)), b)?;
                        }
                    }
                }
                Node::Pattern(pattern) => {
                    let variables: BTreeMap<_, _> = pattern
                        .arguments
                        .iter()
                        .filter_map(|a| {
                            if let Arg::Variable(v, s) = a {
                                Some((*v, *s))
                            } else {
                                None
                            }
                        })
                        .collect();
                    let columns: Vec<_> = variables
                        .values()
                        .map(|s| self.domains[s].as_slice())
                        .collect();
                    each_tuple(&columns, b, |values, b| {
                        let binding: BTreeMap<_, _> = variables
                            .keys()
                            .zip(values)
                            .map(|(v, c)| (*v, *c))
                            .collect();
                        let atom = GroundAtom::new(
                            pattern.relation,
                            pattern.arguments.iter().map(|a| match a {
                                Arg::Constant(c) => *c,
                                Arg::Variable(v, _) => binding[v],
                            }),
                        );
                        add(Node::Atom(atom), b)
                    })?;
                }
            }
            edges.push(adjacent.into_iter().collect::<Vec<_>>());
            cursor += 1;
        }
        // Iterative Kosaraju on the compressed graph. Pattern hubs preserve
        // atom-to-atom reachability, including self loops and dead producers.
        let mut reverse = vec![Vec::new(); nodes.len()];
        for (i, es) in edges.iter().enumerate() {
            for j in es {
                b.tick("completion original cycles")?;
                reverse[*j].push(i);
            }
        }
        let mut seen = vec![false; nodes.len()];
        let mut finish = Vec::new();
        for root in 0..nodes.len() {
            let mut stack = vec![(root, false)];
            while let Some((i, exit)) = stack.pop() {
                b.tick("completion original cycles")?;
                if exit {
                    finish.push(i);
                    continue;
                }
                if std::mem::replace(&mut seen[i], true) {
                    continue;
                }
                stack.push((i, true));
                stack.extend(edges[i].iter().rev().map(|j| (*j, false)));
            }
        }
        seen.fill(false);
        let mut cycle = None;
        for root in finish.into_iter().rev() {
            if seen[root] {
                continue;
            }
            let mut stack = vec![root];
            let mut component = Vec::new();
            let mut size = 0;
            while let Some(i) = stack.pop() {
                b.tick("completion original cycles")?;
                if std::mem::replace(&mut seen[i], true) {
                    continue;
                }
                size += 1;
                if let Node::Atom(a) = &nodes[i] {
                    component.push(a.clone());
                }
                stack.extend(reverse[i].iter().copied());
            }
            if cycle.is_none()
                && size > 1
                && positive_root.is_none_or(|root| component.contains(root))
            {
                component.sort();
                cycle = Some(component);
            }
        }
        Ok(OriginalCone {
            facts: atoms,
            cycle,
        })
    }
}
fn canonical(pattern: &Pattern, binding: &BTreeMap<usize, ConstantId>) -> Pattern {
    let mut variables = BTreeMap::new();
    Pattern {
        relation: pattern.relation,
        arguments: pattern
            .arguments
            .iter()
            .map(|a| match a {
                Arg::Constant(c) => Arg::Constant(*c),
                Arg::Variable(v, s) => match binding.get(v) {
                    Some(c) => Arg::Constant(*c),
                    None => {
                        let next = variables.len();
                        Arg::Variable(*variables.entry(*v).or_insert(next), *s)
                    }
                },
            })
            .collect(),
    }
}
fn insert(
    node: Node,
    nodes: &mut Vec<Node>,
    ids: &mut BTreeMap<Node, usize>,
    atoms: &mut BTreeSet<GroundAtom>,
    b: &mut Budget<'_>,
) -> Result<usize> {
    b.tick("completion original dependencies")?;
    if let Some(i) = ids.get(&node) {
        return Ok(*i);
    }
    if let Node::Atom(a) = &node {
        b.room(
            atoms.len(),
            b.limits.max_atoms,
            "completion original dependencies",
            "atoms",
        )?;
        atoms.insert(a.clone());
    } else {
        b.room(
            nodes.len(),
            b.limits.max_dependencies,
            "completion original dependencies",
            "patterns",
        )?;
    }
    let i = nodes.len();
    ids.insert(node.clone(), i);
    nodes.push(node);
    Ok(i)
}
