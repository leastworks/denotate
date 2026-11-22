//! Completion possibility is a greatest fixpoint, not least-model reachability.
//! Resolve positive relation components provider first. Unknown recursive tables
//! initially denote their complete domains; sparse known providers bind variables
//! before any remaining domain enumeration. Retain unseeded positive loops.
use super::*;
use std::cell::RefCell;
#[path = "completion_ground/original.rs"]
mod original;
pub(crate) use original::OriginalDependencies;
#[cfg(test)]
#[path = "completion_ground/full.rs"]
mod full;
#[cfg(test)]
#[path = "completion_ground/tests.rs"]
mod tests;

type Binding<'a> = BTreeMap<&'a str, ConstantId>;
type Index = BTreeMap<Vec<ConstantId>, Vec<usize>>;
struct Table {
    rows: Vec<GroundAtom>,
    indexes: RefCell<BTreeMap<Vec<usize>, Index>>,
}
impl Table {
    fn new(atoms: impl IntoIterator<Item = GroundAtom>) -> Self {
        Self {
            rows: atoms.into_iter().collect(),
            indexes: RefCell::new(BTreeMap::new()),
        }
    }
    fn candidates(
        &self,
        atom: &Atom,
        binding: &Binding<'_>,
        b: &mut Budget<'_>,
    ) -> Result<Vec<usize>> {
        let mut columns = Vec::new();
        let mut key = Vec::new();
        for (i, t) in atom.arguments().iter().enumerate() {
            b.tick("completion joins")?;
            let value = match t.value() {
                Term::Constant(c) => Some(*c),
                Term::Variable { name, .. } => binding.get(name.as_str()).copied(),
            };
            if let Some(value) = value {
                columns.push(i);
                key.push(value);
            }
        }
        let mut indexes = self.indexes.borrow_mut();
        if !indexes.contains_key(&columns) {
            let mut index = Index::new();
            for (i, row) in self.rows.iter().enumerate() {
                b.charge(columns.len() + 1, "completion join index")?;
                index
                    .entry(columns.iter().map(|j| row.arguments[*j]).collect())
                    .or_default()
                    .push(i);
            }
            indexes.insert(columns.clone(), index);
        }
        let found = indexes[&columns]
            .get(&key)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        b.charge(found.len() + 1, "completion joins")?;
        Ok(found.to_vec())
    }
}
type Upper = BTreeMap<RelationId, Option<Table>>;

impl GroundProgram {
    #[cfg(test)]
    pub(crate) fn prepare_completion(
        corpus: &Corpus,
        domains: &Domains,
        b: &mut Budget<'_>,
    ) -> Result<Self> {
        Self::prepare_completion_with_inputs(corpus, domains, None, None, b)
    }
    /// Supplied eligibility has already been evaluated under the selected semantics.
    /// A static scope builds only that provider's rules, without any runtime inputs.
    pub(crate) fn prepare_completion_with_inputs(
        corpus: &Corpus,
        domains: &Domains,
        eligibility: Option<BTreeMap<RelationId, BTreeSet<GroundAtom>>>,
        static_scope: Option<&BTreeSet<RelationId>>,
        b: &mut Budget<'_>,
    ) -> Result<Self> {
        let domains = validate_domains(corpus, domains, b)?;
        let mut p = Self::empty(corpus, domains.clone());
        p.obligations.clear();
        if static_scope.is_none() {
            match eligibility {
                Some(values) => {
                    p.input_domains = values;
                    p.seed_completion_inputs(corpus, b)?;
                }
                None => p.completion_inputs(corpus, b)?,
            }
        }
        let mut tables: Upper = corpus
            .relations()
            .map(|r| {
                (
                    r.id,
                    if r.role == RelationRole::Input {
                        Some(Table::new(
                            p.inputs.iter().filter(|a| a.relation == r.id).cloned(),
                        ))
                    } else {
                        None
                    },
                )
            })
            .collect();
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        for r in corpus
            .rules()
            .filter(|r| static_scope.is_none_or(|scope| scope.contains(&r.head.relation())))
        {
            b.tick("completion grounding")?;
            producers.entry(r.head.relation()).or_default().push(r);
        }
        let mut fixed_count = p.inputs.len();
        for component in positive_components(corpus, b)? {
            if component
                .iter()
                .all(|r| corpus.relation(*r).unwrap().role == RelationRole::Input)
            {
                continue;
            }
            loop {
                let mut next = BTreeMap::<RelationId, BTreeSet<GroundAtom>>::new();
                let mut count = 0;
                for relation in &component {
                    let out = next.entry(*relation).or_default();
                    for rule in producers.get(relation).into_iter().flatten() {
                        bindings(rule, &tables, &domains, b, |binding, b| {
                            let atom = ground_atom(&rule.head, binding, b)?.atom;
                            if !out.contains(&atom) {
                                b.room(
                                    fixed_count + count,
                                    b.limits.max_atoms,
                                    "completion possibility",
                                    "atoms",
                                )?;
                                out.insert(atom);
                                count += 1;
                            }
                            Ok(())
                        })?;
                    }
                }
                let mut equal = true;
                for (relation, atoms) in next {
                    b.charge(atoms.len() + 1, "completion possibility")?;
                    equal &= tables[&relation]
                        .as_ref()
                        .is_some_and(|old| old.rows.iter().eq(atoms.iter()));
                    tables.insert(relation, Some(Table::new(atoms)));
                }
                if equal {
                    fixed_count += count;
                    break;
                }
            }
        }
        // Construct only instances whose positive premises survived the greatest
        // fixpoint. Every omitted producer has a premise false in every completion.
        let mut dependencies = 0;
        for rule in corpus
            .rules()
            .filter(|r| static_scope.is_none_or(|scope| scope.contains(&r.head.relation())))
        {
            bindings(rule, &tables, &domains, b, |binding, b| {
                b.room(
                    p.rules.len(),
                    b.limits.max_rules,
                    "completion grounding",
                    "rules",
                )?;
                let head = ground_atom(&rule.head, binding, b)?;
                p.completion_atom(head.atom.clone(), b)?;
                let mut body = Vec::new();
                for literal in &rule.body {
                    b.room(
                        dependencies,
                        b.limits.max_dependencies,
                        "completion grounding",
                        "dependencies",
                    )?;
                    dependencies += 1;
                    let term = ground_atom(literal.atom(), binding, b)?;
                    p.completion_atom(term.atom.clone(), b)?;
                    body.push(GroundLiteral {
                        polarity: if matches!(literal, Literal::Positive(_)) {
                            Polarity::Positive
                        } else {
                            Polarity::Negative
                        },
                        term,
                    });
                }
                let id = GroundRuleId {
                    preparation: p.preparation,
                    index: p.rules.len(),
                };
                p.rules.push(GroundRule {
                    id,
                    source: rule.id,
                    head,
                    body,
                    replacements: vec![],
                });
                Ok(())
            })?;
        }
        graph::analyze(&mut p, b)?;
        Ok(p)
    }
    pub(crate) fn completion_inputs(
        &mut self,
        corpus: &Corpus,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        self.input_domains = input_domains::evaluate(corpus, &self.domains, budget)?;
        self.seed_completion_inputs(corpus, budget)
    }
    fn seed_completion_inputs(&mut self, corpus: &Corpus, budget: &mut Budget<'_>) -> Result<()> {
        let domains = self.domains.clone();
        for r in corpus.relations().filter(|r| r.role == RelationRole::Input) {
            if let Some(allowed) = self.input_domains.get(&r.id).cloned() {
                for a in allowed {
                    self.completion_atom(a.clone(), budget)?;
                    self.inputs.insert(a);
                }
            } else {
                let columns: Vec<_> = r
                    .parameters
                    .iter()
                    .map(|p| domains[&p.sort].as_slice())
                    .collect();
                each_tuple(&columns, budget, |values, b| {
                    let a = GroundAtom::new(r.id, values.iter().copied());
                    self.completion_atom(a.clone(), b)?;
                    self.inputs.insert(a);
                    Ok(())
                })?;
            }
        }
        self.build_input_groups(corpus, &[], budget)?;
        graph::analyze(self, budget)
    }
    fn completion_atom(&mut self, atom: GroundAtom, b: &mut Budget<'_>) -> Result<()> {
        b.charge(atom.arguments.len() + 1, "completion grounding")?;
        if !self.atom_index.contains_key(&atom) {
            b.room(
                self.atoms.len(),
                b.limits.max_atoms,
                "completion grounding",
                "atoms",
            )?;
            let i = self.atoms.len();
            self.atom_index.insert(atom.clone(), i);
            self.atoms.push(atom);
        }
        Ok(())
    }
}

fn bindings<'a>(
    rule: &'a Rule,
    tables: &Upper,
    domains: &Domains,
    b: &mut Budget<'_>,
    mut emit: impl FnMut(&Binding<'a>, &mut Budget<'_>) -> Result<()>,
) -> Result<()> {
    let mut variables = BTreeMap::new();
    let mut steps = Vec::new();
    for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
        for term in atom.arguments() {
            b.tick("completion join planning")?;
            if let Term::Variable { name, sort } = term.value() {
                variables.insert(name.as_str(), *sort);
            }
        }
    }
    for literal in &rule.body {
        if let Literal::Positive(atom) = literal {
            if let Some(table) = &tables[&atom.relation()] {
                steps.push((atom, table));
            }
        }
    }
    steps.sort_by_key(|(_, t)| t.rows.len());
    let mut complete = |binding: &Binding<'a>, b: &mut Budget<'_>| -> Result<()> {
        let unbound: Vec<_> = variables
            .iter()
            .filter(|(v, _)| !binding.contains_key(**v))
            .collect();
        let columns: Vec<_> = unbound.iter().map(|(_, s)| domains[s].as_slice()).collect();
        each_tuple(&columns, b, |values, b| {
            b.charge(binding.len() + values.len(), "completion bindings")?;
            let mut all = binding.clone();
            for ((v, _), value) in unbound.iter().zip(values) {
                all.insert(**v, *value);
            }
            emit(&all, b)
        })
    };
    if steps.is_empty() {
        return complete(&BTreeMap::new(), b);
    }
    let initial = BTreeMap::new();
    let candidates = steps[0].1.candidates(steps[0].0, &initial, b)?;
    let mut stack = vec![(initial, candidates.into_iter())];
    while !stack.is_empty() {
        b.tick("completion joins")?;
        let depth = stack.len() - 1;
        let (binding, candidates) = stack.last_mut().unwrap();
        let Some(i) = candidates.next() else {
            stack.pop();
            continue;
        };
        let (atom, table) = steps[depth];
        b.charge(binding.len() + atom.arguments().len(), "completion joins")?;
        let mut next = binding.clone();
        let matches = atom
            .arguments()
            .iter()
            .zip(&table.rows[i].arguments)
            .all(|(term, value)| match term.value() {
                Term::Constant(c) => c == value,
                Term::Variable { name, .. } => next
                    .insert(name.as_str(), *value)
                    .is_none_or(|old| old == *value),
            });
        if !matches {
            continue;
        }
        if depth + 1 == steps.len() {
            complete(&next, b)?;
        } else {
            let candidates = steps[depth + 1]
                .1
                .candidates(steps[depth + 1].0, &next, b)?;
            stack.push((next, candidates.into_iter()));
        }
    }
    Ok(())
}
fn positive_components(corpus: &Corpus, b: &mut Budget<'_>) -> Result<Vec<Vec<RelationId>>> {
    let ids: Vec<_> = corpus.relations().map(|r| r.id).collect();
    let positions: BTreeMap<_, _> = ids.iter().enumerate().map(|(i, r)| (*r, i)).collect();
    let mut edges = vec![BTreeSet::new(); ids.len()];
    let mut reverse = edges.clone();
    for r in corpus.rules() {
        for l in &r.body {
            b.tick("completion relation graph")?;
            if let Literal::Positive(a) = l {
                let from = positions[&r.head.relation()];
                let to = positions[&a.relation()];
                edges[from].insert(to);
                reverse[to].insert(from);
            }
        }
    }
    let mut seen = vec![false; ids.len()];
    let mut finish = Vec::new();
    for root in 0..ids.len() {
        let mut stack = vec![(root, false)];
        while let Some((i, exit)) = stack.pop() {
            b.tick("completion relation graph")?;
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
    let mut components = Vec::new();
    for root in finish.into_iter().rev() {
        if seen[root] {
            continue;
        }
        let mut stack = vec![root];
        let mut component = Vec::new();
        while let Some(i) = stack.pop() {
            b.tick("completion relation graph")?;
            if std::mem::replace(&mut seen[i], true) {
                continue;
            }
            component.push(ids[i]);
            stack.extend(reverse[i].iter().copied());
        }
        component.sort();
        components.push(component);
    }
    components.reverse();
    Ok(components)
}
