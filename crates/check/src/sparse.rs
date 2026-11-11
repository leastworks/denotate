//! Positive closure with delta-driven, indexed joins. Negative premises are
//! retained in instances but never restrict possibility.
use super::planning::constant_columns;
use super::*;
use std::collections::VecDeque;

#[cfg(test)]
#[path = "tests/planner.rs"]
mod planner_tests;

type Binding<'a> = BTreeMap<&'a str, ConstantId>;
type Buckets = BTreeMap<Vec<ConstantId>, Vec<usize>>;
type Indexes = BTreeMap<RelationId, BTreeMap<Vec<usize>, Buckets>>;

#[derive(Default)]
struct Tuples {
    atoms: Vec<GroundAtom>,
    seen: BTreeSet<GroundAtom>,
    indexes: Indexes,
    delta: VecDeque<usize>,
}
impl Tuples {
    fn insert(&mut self, atom: GroundAtom, budget: &mut Budget<'_>) -> Result<()> {
        budget.tick("grounding")?;
        if self.seen.contains(&atom) {
            return Ok(());
        }
        budget.room(
            self.atoms.len(),
            budget.limits.max_atoms,
            "grounding",
            "atoms",
        )?;
        let id = self.atoms.len();
        if let Some(indexes) = self.indexes.get_mut(&atom.relation) {
            for (columns, buckets) in indexes {
                budget.tick("grounding indexes")?;
                let key = project(&atom, columns, budget)?;
                buckets.entry(key).or_default().push(id);
            }
        }
        self.seen.insert(atom.clone());
        self.atoms.push(atom);
        self.delta.push_back(id);
        Ok(())
    }

    fn candidates(
        &self,
        step: &Step<'_>,
        binding: &Binding<'_>,
        budget: &mut Budget<'_>,
    ) -> Result<&[usize]> {
        budget.tick("grounding joins")?;
        let mut key = Vec::new();
        for column in &step.columns {
            budget.tick("grounding joins")?;
            key.push(match step.atom.arguments()[*column].value() {
                Term::Constant(c) => *c,
                Term::Variable { name, .. } => binding[name.as_str()],
            });
        }
        Ok(self.indexes[&step.atom.relation()][&step.columns]
            .get(&key)
            .map(Vec::as_slice)
            .unwrap_or(&[]))
    }
}

fn project(
    atom: &GroundAtom,
    columns: &[usize],
    budget: &mut Budget<'_>,
) -> Result<Vec<ConstantId>> {
    columns
        .iter()
        .map(|column| {
            budget.tick("grounding indexes")?;
            Ok(atom.arguments[*column])
        })
        .collect()
}

struct Step<'a> {
    atom: &'a Atom,
    columns: Vec<usize>,
}
struct Plan<'a> {
    rule: &'a Rule,
    pivot: &'a Atom,
    steps: Vec<Step<'a>>,
}

// Dense variable incidence is built once per rule. Each pivot binds each variable
// once and visits each argument incidence once; score buckets avoid rescanning
// remaining literals. At bounded arity, all n pivot plans take O(n²) work.
pub(super) struct JoinPlanner {
    variables: Vec<Vec<Option<usize>>>,
    readers: Vec<Vec<usize>>,
    constants: Vec<usize>,
    arity: usize,
}
impl JoinPlanner {
    pub(super) fn new(
        positives: &[Vec<Option<std::sync::Arc<str>>>],
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let mut names = BTreeMap::new();
        let mut readers: Vec<Vec<usize>> = Vec::new();
        let mut variables = Vec::new();
        let mut constants = Vec::new();
        let mut arity = 0;
        for (index, atom) in positives.iter().enumerate() {
            budget.tick("grounding plans")?;
            let mut terms = Vec::new();
            let mut fixed = 0;
            for term in atom {
                budget.tick("grounding plans")?;
                terms.push(match term {
                    None => {
                        fixed += 1;
                        None
                    }
                    Some(name) => {
                        let next = names.len();
                        let id = *names.entry(name.as_ref()).or_insert(next);
                        if id == readers.len() {
                            readers.push(Vec::new());
                        }
                        // Repeated variables count once per bound column.
                        readers[id].push(index);
                        Some(id)
                    }
                });
            }
            arity = arity.max(terms.len());
            variables.push(terms);
            constants.push(fixed);
        }
        Ok(Self {
            variables,
            readers,
            constants,
            arity,
        })
    }

    pub(super) fn steps(
        &self,
        pivot: usize,
        budget: &mut Budget<'_>,
    ) -> Result<Vec<(usize, Vec<usize>)>> {
        let n = self.variables.len();
        budget.charge(n + self.readers.len() + self.arity + 1, "grounding plans")?;
        let mut bound = vec![false; self.readers.len()];
        let mut buckets = ScoreBuckets {
            heads: vec![None; self.arity + 1],
            previous: vec![None; n],
            next: vec![None; n],
            scores: self.constants.clone(),
            active: vec![true; n],
        };
        // Initial ties follow authored order; promotions go to the bucket head.
        // This deterministic tie policy avoids an ordered-tree/logarithmic cost
        // for each incidence update. It does not change the selectivity score.
        for i in (0..n).rev() {
            buckets.insert(i);
        }
        buckets.remove(pivot);
        buckets.active[pivot] = false;
        let mut selected = pivot;
        let mut steps = Vec::with_capacity(n.saturating_sub(1));
        loop {
            for variable in &self.variables[selected] {
                budget.tick("grounding plans")?;
                let Some(variable) = *variable else { continue };
                if std::mem::replace(&mut bound[variable], true) {
                    continue;
                }
                for &reader in &self.readers[variable] {
                    budget.tick("grounding plans")?;
                    if buckets.active[reader] {
                        buckets.remove(reader);
                        buckets.scores[reader] += 1;
                        buckets.insert(reader);
                    }
                }
            }
            budget.charge(self.arity + 1, "grounding plans")?;
            let Some(best) = buckets.heads.iter().rev().find_map(|head| *head) else {
                break;
            };
            buckets.remove(best);
            buckets.active[best] = false;
            let mut columns = Vec::new();
            for (column, variable) in self.variables[best].iter().enumerate() {
                budget.tick("grounding plans")?;
                if variable.is_none_or(|v| bound[v]) {
                    columns.push(column);
                }
            }
            steps.push((best, columns));
            selected = best;
        }
        Ok(steps)
    }
}

struct ScoreBuckets {
    heads: Vec<Option<usize>>,
    previous: Vec<Option<usize>>,
    next: Vec<Option<usize>>,
    scores: Vec<usize>,
    active: Vec<bool>,
}
impl ScoreBuckets {
    fn insert(&mut self, index: usize) {
        let head = &mut self.heads[self.scores[index]];
        self.previous[index] = None;
        self.next[index] = *head;
        if let Some(old) = *head {
            self.previous[old] = Some(index);
        }
        *head = Some(index);
    }
    fn remove(&mut self, index: usize) {
        if let Some(previous) = self.previous[index] {
            self.next[previous] = self.next[index];
        } else {
            self.heads[self.scores[index]] = self.next[index];
        }
        if let Some(next) = self.next[index] {
            self.previous[next] = self.previous[index];
        }
    }
}

fn match_tuple<'a>(
    atom: &'a Atom,
    tuple: &GroundAtom,
    binding: &Binding<'a>,
    budget: &mut Budget<'_>,
) -> Result<Option<Binding<'a>>> {
    budget.tick("grounding joins")?;
    let mut result = BTreeMap::new();
    for (name, value) in binding {
        budget.tick("grounding joins")?;
        result.insert(*name, *value);
    }
    for (term, value) in atom.arguments().iter().zip(&tuple.arguments) {
        budget.tick("grounding joins")?;
        match term.value() {
            Term::Constant(c) if c != value => return Ok(None),
            Term::Variable { name, .. } => {
                if let Some(previous) = result.insert(name.as_str(), *value) {
                    if previous != *value {
                        return Ok(None);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(Some(result))
}

#[derive(Default)]
struct Instances {
    // Binding values are in rule-local variable-name order, including body-only
    // variables. Different authored rules never share an instance identity.
    rules: BTreeMap<(RuleId, Vec<ConstantId>), GroundRule>,
}
impl Instances {
    fn add(
        &mut self,
        rule: &Rule,
        binding: &Binding<'_>,
        preparation: u64,
        fixed: Option<&FixedFacts>,
        budget: &mut Budget<'_>,
    ) -> Result<Option<GroundAtom>> {
        budget.tick("grounding")?;
        let mut values = Vec::new();
        for value in binding.values() {
            budget.tick("grounding")?;
            values.push(*value);
        }
        let key = (rule.id, values);
        if self.rules.contains_key(&key) {
            return Ok(None);
        }
        let folded_head = if let Some(fixed) = fixed {
            let head = ground_atom(&rule.head, binding, budget)?;
            if fixed.program.atom_index.contains_key(&head.atom) {
                return Ok(None);
            }
            Some(head)
        } else {
            None
        };
        budget.room(
            self.rules
                .len()
                .saturating_add(fixed.map_or(0, |f| f.program.rules.len())),
            budget.limits.max_rules,
            "grounding",
            "rules",
        )?;
        let head = match folded_head {
            Some(head) => head,
            None => ground_atom(&rule.head, binding, budget)?,
        };
        let mut body = Vec::new();
        for literal in &rule.body {
            budget.tick("grounding")?;
            body.push(GroundLiteral {
                polarity: match literal {
                    Literal::Positive(_) => Polarity::Positive,
                    Literal::Negative(_) => Polarity::Negative,
                },
                term: ground_atom(literal.atom(), binding, budget)?,
            });
        }
        let atom = head.atom.clone();
        self.rules.insert(
            key,
            GroundRule {
                id: GroundRuleId {
                    preparation,
                    index: 0,
                },
                source: rule.id,
                head,
                body,
            },
        );
        Ok(Some(atom))
    }
}

// Iterative depth-first join: no call-stack dependency on rule body length and
// no materialized Cartesian intermediate. Each frame probes an indexed bucket.
fn join<'a>(
    plan: &Plan<'a>,
    initial: Binding<'a>,
    tuples: &Tuples,
    budget: &mut Budget<'_>,
    mut emit: impl FnMut(&Binding<'a>, &mut Budget<'_>) -> Result<()>,
) -> Result<()> {
    if plan.steps.is_empty() {
        return emit(&initial, budget);
    }
    let candidates = tuples.candidates(&plan.steps[0], &initial, budget)?;
    let mut stack = vec![(initial, candidates.iter())];
    while !stack.is_empty() {
        budget.tick("grounding joins")?;
        let depth = stack.len() - 1;
        let (binding, cursor) = stack.last_mut().unwrap();
        let Some(candidate) = cursor.next() else {
            stack.pop();
            continue;
        };
        let Some(next) = match_tuple(
            plan.steps[depth].atom,
            &tuples.atoms[*candidate],
            binding,
            budget,
        )?
        else {
            continue;
        };
        if depth + 1 == plan.steps.len() {
            emit(&next, budget)?;
        } else {
            let candidates = tuples.candidates(&plan.steps[depth + 1], &next, budget)?;
            stack.push((next, candidates.iter()));
        }
    }
    Ok(())
}

pub(super) fn populate(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
) -> Result<()> {
    populate_with_delta(corpus, p, budget, VecDeque::pop_front)
}

fn populate_with_delta(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
    mut next: impl FnMut(&mut VecDeque<usize>) -> Option<usize>,
) -> Result<()> {
    populate_using(corpus, p, budget, &mut next, None, &[], None)
}

pub(super) fn populate_cached(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
    keys: &SemanticKeys,
    store: &mut dyn JoinPlanStore,
) -> Result<()> {
    populate_using(
        corpus,
        p,
        budget,
        &mut VecDeque::pop_front,
        Some((keys, store)),
        &[],
        None,
    )
}

pub(super) fn populate_seeded(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
    keys: &SemanticKeys,
    store: &mut dyn JoinPlanStore,
    external: &[GroundAtom],
) -> Result<()> {
    populate_using(
        corpus,
        p,
        budget,
        &mut VecDeque::pop_front,
        Some((keys, store)),
        external,
        None,
    )
}

pub(super) fn populate_domain_cone(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
    cone: &BTreeSet<RelationId>,
) -> Result<()> {
    populate_using(
        corpus,
        p,
        budget,
        &mut VecDeque::pop_front,
        None,
        &[],
        Some(cone),
    )
}

fn populate_using(
    corpus: &Corpus,
    p: &mut GroundProgram,
    budget: &mut Budget<'_>,
    next: &mut impl FnMut(&mut VecDeque<usize>) -> Option<usize>,
    mut cache: Option<(&SemanticKeys, &mut dyn JoinPlanStore)>,
    external: &[GroundAtom],
    cone: Option<&BTreeSet<RelationId>>,
) -> Result<()> {
    let mut tuples = Tuples::default();
    let mut instances = Instances::default();
    let mut plans = Vec::new();
    let mut seeds = Vec::new();
    // Same index shape as tuple indexes, but bucket entries identify consumers.
    // Constants in authored guards must not cause a scan of all authored rules.
    let mut consumers = Indexes::new();
    let plan_start = Instant::now();
    for rule in corpus.rules() {
        budget.tick("grounding plans")?;
        if cone.is_some_and(|c| !c.contains(&rule.head.relation())) {
            continue;
        }
        if p.fixed
            .as_ref()
            .is_some_and(|f| f.relations.contains(&rule.head.relation()))
        {
            continue;
        }
        let mut positives = Vec::new();
        for literal in &rule.body {
            budget.tick("grounding plans")?;
            if let Literal::Positive(atom) = literal {
                positives.push(atom);
            }
        }
        if positives.is_empty() {
            if let Some(head) = instances.add(
                rule,
                &Binding::new(),
                p.preparation,
                p.fixed.as_deref(),
                budget,
            )? {
                seeds.push(head);
            }
        }
        let key_start = Instant::now();
        let shape = JoinPlanSchema::from_rule(rule);
        budget.check("grounding plans")?;
        let cached = if let Some((keys, store)) = &mut cache
            && store.should_cache(positives.len())
        {
            let key = keys.rule(rule.id).map_err(CheckError::Keys)?.clone();
            let schema = keys.rule_schema(rule).map_err(CheckError::Keys)?;
            p.metrics.plan_keying += key_start.elapsed();
            store.plan(key, schema, budget.remaining())?
        } else {
            p.metrics.plan_keying += key_start.elapsed();
            None
        };
        budget.check("grounding plans")?;
        // Current positions and variable/constant incidence must match exactly.
        // SemanticKeys::validate has already checked one-to-one source bindings.
        if cached
            .as_ref()
            .is_some_and(|p| p.schema != shape || p.pivots.len() != positives.len())
        {
            return Err(CheckError::Internal("cached plan/current rule mismatch"));
        }
        // A provider cannot force lumped exhaustion: insufficient remaining
        // allowance always executes the original rule planning charge sequence.
        let cached = cached.filter(|p| p.required_work().is_some_and(|w| w <= budget.remaining()));
        let planner = if let Some(plan) = &cached {
            budget.charge(plan.initialization_work, "grounding plans")?;
            None
        } else {
            Some(JoinPlanner::new(&shape.positives, budget)?)
        };
        // At most 2^arity shapes per occurrence. Register each shape once, so
        // relation-map lookup is not repeated for all n² materialized steps.
        let mut shapes: Vec<Vec<Vec<usize>>> = vec![Vec::new(); positives.len()];
        for (pivot_index, pivot) in positives.iter().enumerate() {
            budget.tick("grounding plans")?;
            let columns = if let Some(plan) = &cached {
                budget.charge(plan.pivots[pivot_index].columns_work, "grounding plans")?;
                plan.pivots[pivot_index].columns.clone()
            } else {
                constant_columns(&shape.positives[pivot_index], budget)?
            };
            let binding_start = Instant::now();
            let mut key = Vec::new();
            for column in &columns {
                budget.tick("grounding plans")?;
                if let Term::Constant(c) = pivot.arguments()[*column].value() {
                    key.push(*c);
                }
            }
            consumers
                .entry(pivot.relation())
                .or_default()
                .entry(columns)
                .or_default()
                .entry(key)
                .or_default()
                .push(plans.len());
            p.metrics.plan_binding += binding_start.elapsed();
            let mut steps = Vec::new();
            let ordered = if let Some(plan) = &cached {
                budget.charge(plan.pivots[pivot_index].steps_work, "grounding plans")?;
                plan.pivots[pivot_index].steps.clone()
            } else {
                planner.as_ref().unwrap().steps(pivot_index, budget)?
            };
            let binding_start = Instant::now();
            for (index, columns) in ordered {
                let atom = *positives
                    .get(index)
                    .ok_or(CheckError::Internal("cached plan literal position"))?;
                budget.tick("grounding plans")?;
                if !shapes[index].contains(&columns) {
                    tuples
                        .indexes
                        .entry(atom.relation())
                        .or_default()
                        .entry(columns.clone())
                        .or_default();
                    shapes[index].push(columns.clone());
                }
                steps.push(Step { atom, columns });
            }
            plans.push(Plan { rule, pivot, steps });
            p.metrics.plan_binding += binding_start.elapsed();
        }
    }
    p.metrics.plans_and_seeds = plan_start.elapsed();
    let seed_start = Instant::now();
    #[cfg(any(test, feature = "test-support"))]
    budget.mark("plans_and_seed_instances");
    // Index definitions must exist before any tuple is indexed.
    for atom in p
        .fixed
        .iter()
        .flat_map(|f| f.program.atoms.iter())
        .cloned()
        .chain(external.iter().cloned())
        .chain(seeds)
    {
        tuples.insert(atom, budget)?;
    }
    for relation in corpus.relations() {
        budget.tick("grounding")?;
        if relation.role != RelationRole::Input || cone.is_some() {
            continue;
        }
        if let Some(allowed) = p.input_domains.get(&relation.id) {
            for atom in allowed {
                budget.tick("grounding")?;
                p.inputs.insert(atom.clone());
                tuples.insert(atom.clone(), budget)?;
            }
            continue;
        }
        let columns: Vec<_> = relation
            .parameters
            .iter()
            .map(|parameter| p.domains[&parameter.sort].as_slice())
            .collect();
        each_tuple(&columns, budget, |args, budget| {
            let atom = GroundAtom::new(relation.id, args.iter().copied());
            p.inputs.insert(atom.clone());
            tuples.insert(atom, budget)
        })?;
    }
    p.metrics.input_seeding = seed_start.elapsed();
    let closure_start = Instant::now();
    #[cfg(any(test, feature = "test-support"))]
    budget.mark("input_seeding_and_indexes");
    while let Some(delta) = next(&mut tuples.delta) {
        budget.tick("grounding")?;
        let tuple = &tuples.atoms[delta];
        let mut heads = Vec::new();
        if let Some(indexes) = consumers.get(&tuple.relation) {
            for (columns, buckets) in indexes {
                budget.tick("grounding indexes")?;
                let key = project(tuple, columns, budget)?;
                if let Some(readers) = buckets.get(&key) {
                    for reader in readers {
                        budget.tick("grounding joins")?;
                        let plan = &plans[*reader];
                        if let Some(binding) =
                            match_tuple(plan.pivot, tuple, &Binding::new(), budget)?
                        {
                            join(plan, binding, &tuples, budget, |binding, budget| {
                                if let Some(head) = instances.add(
                                    plan.rule,
                                    binding,
                                    p.preparation,
                                    p.fixed.as_deref(),
                                    budget,
                                )? {
                                    heads.push(head);
                                }
                                Ok(())
                            })?;
                        }
                    }
                }
            }
        }
        for head in heads {
            tuples.insert(head, budget)?;
        }
    }
    p.metrics.closure_and_instances = closure_start.elapsed();
    let order_start = Instant::now();
    #[cfg(any(test, feature = "test-support"))]
    budget.mark("closure_and_instances");
    // Canonical IDs and traversal order, independent of delta discovery order.
    for atom in tuples.seen {
        budget.tick("grounding")?;
        if p.fixed_value(&atom).is_some() {
            continue;
        }
        p.atom_index.insert(atom.clone(), p.atoms.len());
        p.atoms.push(atom);
    }
    for (_, mut rule) in instances.rules {
        budget.tick("grounding")?;
        rule.id.index = p.rules.len();
        p.rules.push(rule);
    }
    p.metrics.ordering = order_start.elapsed();
    #[cfg(any(test, feature = "test-support"))]
    budget.mark("grounding_order");
    Ok(())
}

#[cfg(test)]
impl GroundProgram {
    pub(crate) fn prepare_reversed(
        corpus: &Corpus,
        domains: &Domains,
        limits: &Limits,
    ) -> Result<Self> {
        let mut budget = Budget::new(limits);
        let domains = validate_domains(corpus, domains, &mut budget)?;
        let restricted = input_domains::evaluate(corpus, &domains, &mut budget)?;
        let mut p = Self::empty(corpus, domains);
        p.input_domains = restricted;
        populate_with_delta(corpus, &mut p, &mut budget, VecDeque::pop_back)?;
        p.build_groups(corpus, &mut budget)?;
        graph::analyze(&mut p, &mut budget)?;
        Ok(p)
    }
}
