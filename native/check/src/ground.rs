use crate::{
    graph,
    limits::{Budget, Result},
    *,
};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

#[cfg(any(test, feature = "test-support"))]
#[path = "cartesian_oracle.rs"]
mod cartesian_oracle;
#[path = "planning.rs"]
mod planning;
#[path = "sparse.rs"]
mod sparse;
pub use planning::*;

#[cfg(any(test, feature = "test-support"))]
#[path = "tests/preparation_profile.rs"]
mod preparation_profile;

/// Explicit finite domains, not inferred from constants mentioned in rules.
pub type Domains = BTreeMap<SortId, Vec<ConstantId>>;

#[derive(Debug, Default, Clone)]
pub struct PreparationMetrics {
    /// Planning, current plan installation/index definitions and seed instances.
    pub plans_and_seeds: Duration,
    /// Owned incidence/schema projection, within plans_and_seeds.
    pub plan_keying: Duration,
    /// Current consumer/index registration and positional plan-step installation.
    pub plan_binding: Duration,
    pub input_seeding: Duration,
    pub closure_and_instances: Duration,
    pub ordering: Duration,
    /// Domain validation, possible closure, instances and obligation grouping.
    pub grounding: Duration,
    /// Ground dependency graph and local stratification.
    pub admissibility: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroundAtom {
    pub relation: RelationId,
    pub arguments: Vec<ConstantId>,
}
impl GroundAtom {
    pub fn new(relation: RelationId, arguments: impl IntoIterator<Item = ConstantId>) -> Self {
        Self {
            relation,
            arguments: arguments.into_iter().collect(),
        }
    }
}

// IDs are scoped to this immutable preparation, not interchangeable between
// preparations even when they used the same corpus. IR IDs remain unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroundRuleId {
    pub(crate) preparation: u64,
    pub(crate) index: usize,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ComponentId {
    pub(crate) preparation: u64,
    pub(crate) index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Polarity {
    Positive,
    Negative,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundOccurrence {
    pub atom: GroundAtom,
    pub occurrence: OccurrenceId,
    pub arguments: Vec<OccurrenceId>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundLiteral {
    pub polarity: Polarity,
    pub term: GroundOccurrence,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundRule {
    pub id: GroundRuleId,
    pub source: RuleId,
    pub head: GroundOccurrence,
    pub body: Vec<GroundLiteral>,
}

/// A nontrivial group of distinct possible tuples. This is preparation data,
/// not an obligation result: tuples may still depend on blocked components.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AtMostOneGroup {
    pub obligation: ObligationId,
    pub key: Vec<ConstantId>,
    pub tuples: Vec<GroundAtom>,
}

/// Input-only permitted-world constraint, separate from checked obligations.
/// Tuples agreeing on these columns are mutually exclusive (zero is allowed).
#[derive(Debug, Clone)]
pub struct InputAtMostOne {
    pub relation: RelationId,
    pub group_by: Vec<usize>,
}

/// Checked, immutable finite ground program, with provider-first components.
/// Owns a snapshot of rule structure; source IDs point back to the original IR.
#[derive(Debug, Clone)]
pub struct GroundProgram {
    pub(crate) preparation: u64,
    pub(crate) graph_revision: u64,
    signatures: BTreeMap<RelationId, Vec<SortId>>,
    domains: Domains,
    pub(crate) atoms: Vec<GroundAtom>,
    pub(crate) atom_index: BTreeMap<GroundAtom, usize>,
    pub(crate) inputs: BTreeSet<GroundAtom>,
    pub(crate) input_order: Option<Vec<GroundAtom>>,
    pub(crate) rules: Vec<GroundRule>,
    pub(crate) rewrites: crate::rewrite::Rewrites,
    pub(crate) components: Vec<Component>,
    pub(crate) atom_components: Vec<ComponentId>,
    pub(crate) component_rules: Vec<Vec<usize>>,
    pub(crate) dependencies: Vec<Dependency>,
    groups: Vec<AtMostOneGroup>,
    pub(crate) input_groups: Vec<Vec<GroundAtom>>,
    metrics: PreparationMetrics,
}
impl GroundProgram {
    /// Prepare unrestricted input worlds (W = true). This does not infer input
    /// constraints from relation names, signatures or checked obligations.
    /// Use `prepare_with_input_groups` when the caller selects input exclusivity;
    /// InputMapping callers should use that frontend's `LoweredProgram::prepare`.
    pub fn prepare(corpus: &Corpus, domains: &Domains, limits: &Limits) -> Result<Self> {
        Self::prepare_with_input_groups(corpus, domains, &[], limits)
    }

    pub fn prepare_with_input_groups(
        corpus: &Corpus,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        limits: &Limits,
    ) -> Result<Self> {
        Self::prepare_with_budget(corpus, domains, constraints, &mut Budget::new(limits))
    }

    pub(crate) fn prepare_with_budget(
        corpus: &Corpus,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        Self::prepare_using(corpus, domains, constraints, budget, None)
    }
    pub(crate) fn prepare_using(
        corpus: &Corpus,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        budget: &mut Budget<'_>,
        cache: Option<(&SemanticKeys, &mut dyn JoinPlanStore)>,
    ) -> Result<Self> {
        let limits = budget.limits;
        limits.cancellation.check()?;
        let start = Instant::now();
        let domains = validate_domains(corpus, domains, budget)?;
        let mut p = Self::empty(corpus, domains);
        if let Some((keys, store)) = cache {
            sparse::populate_cached(corpus, &mut p, budget, keys, store)?;
        } else {
            sparse::populate(corpus, &mut p, budget)?;
        }
        p.build_groups(corpus, budget)?;
        p.build_input_groups(corpus, constraints, budget)?;
        p.metrics.grounding = start.elapsed();
        let start = Instant::now();
        graph::analyze(&mut p, budget)?;
        p.metrics.admissibility = start.elapsed();
        limits.cancellation.check()?;
        Ok(p)
    }

    /// Select stable BDD variables without changing grounding, rule IDs or group order.
    /// The low-level unkeyed API remains the allocation-order reference path.
    pub fn prepare_keyed_inputs(
        corpus: &Corpus,
        keys: &SemanticKeys,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        limits: &Limits,
    ) -> Result<Self> {
        limits.cancellation.check()?;
        keys.validate(corpus).map_err(CheckError::Keys)?;
        Self::prepare_with_input_groups(corpus, domains, constraints, limits)?
            .with_atom_key_order(keys)
    }
    // Only fresh construction may choose an order: previously issued Conditions
    // must never be interpreted using a different variable map.
    pub(crate) fn with_atom_key_order(mut self, keys: &SemanticKeys) -> Result<Self> {
        let mut ordered = self
            .inputs
            .iter()
            .map(|a| {
                Ok((
                    AtomKey::from_atom(keys, a).map_err(CheckError::Keys)?,
                    a.clone(),
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        ordered.sort_by(|a, b| a.0.cmp(&b.0));
        self.input_order = Some(ordered.into_iter().map(|(_, a)| a).collect());
        Ok(self)
    }
    pub(crate) fn ordered_inputs(&self) -> Vec<&GroundAtom> {
        self.input_order
            .as_ref()
            .map_or_else(|| self.inputs.iter().collect(), |v| v.iter().collect())
    }

    pub fn domain(&self, sort: SortId) -> Option<&[ConstantId]> {
        self.domains.get(&sort).map(Vec::as_slice)
    }

    pub fn metrics(&self) -> &PreparationMetrics {
        &self.metrics
    }

    pub(crate) fn empty(corpus: &Corpus, domains: Domains) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self {
            preparation: NEXT.fetch_add(1, Ordering::Relaxed),
            graph_revision: 0,
            rewrites: Default::default(),
            signatures: corpus
                .relations()
                .map(|r| (r.id, r.parameters.iter().map(|p| p.sort).collect()))
                .collect(),
            domains,
            atoms: vec![],
            atom_index: BTreeMap::new(),
            inputs: BTreeSet::new(),
            input_order: None,
            rules: vec![],
            components: vec![],
            atom_components: vec![],
            component_rules: vec![],
            dependencies: vec![],
            groups: vec![],
            input_groups: vec![],
            metrics: PreparationMetrics::default(),
        }
    }

    pub(crate) fn validate_atom(&self, atom: &GroundAtom) -> Result<()> {
        let legal = self.signatures.get(&atom.relation).is_some_and(|sorts| {
            sorts.len() == atom.arguments.len()
                && sorts
                    .iter()
                    .zip(&atom.arguments)
                    .all(|(sort, value)| self.domains[sort].binary_search(value).is_ok())
        });
        if legal {
            Ok(())
        } else {
            Err(CheckError::UnknownAtom(atom.clone()))
        }
    }

    /// Legality and possibility are independent of whether a replay derives a fact.
    pub fn is_possible(&self, atom: &GroundAtom) -> Result<bool> {
        self.validate_atom(atom)?;
        Ok(self.atom_index.contains_key(atom))
    }

    fn build_groups(&mut self, corpus: &Corpus, budget: &mut Budget<'_>) -> Result<()> {
        let mut by_relation = BTreeMap::<_, Vec<_>>::new();
        for atom in &self.atoms {
            budget.tick("obligation groups")?;
            by_relation.entry(atom.relation).or_default().push(atom);
        }
        for obligation in corpus.obligations() {
            budget.tick("obligation groups")?;
            let Requirement::AtMostOne { relation, group_by } = &obligation.requirement;
            let mut groups = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
            if let Some(atoms) = by_relation.get(relation) {
                for atom in atoms {
                    budget.tick("obligation groups")?;
                    let mut key = Vec::new();
                    for column in group_by {
                        budget.tick("obligation groups")?;
                        key.push(atom.arguments[*column]);
                    }
                    groups.entry(key).or_default().push((*atom).clone());
                }
            }
            for (key, tuples) in groups {
                budget.tick("obligation groups")?;
                if tuples.len() >= 2 {
                    self.groups.push(AtMostOneGroup {
                        obligation: obligation.id,
                        key,
                        tuples,
                    });
                }
            }
        }
        Ok(())
    }

    fn build_input_groups(
        &mut self,
        corpus: &Corpus,
        constraints: &[InputAtMostOne],
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        for constraint in constraints {
            budget.tick("input groups")?;
            let relation = corpus
                .relation(constraint.relation)
                .ok_or(CheckError::InvalidInputGroup("unknown relation"))?;
            if relation.role != RelationRole::Input {
                return Err(CheckError::InvalidInputGroup("relation must be input-only"));
            }
            let mut columns = BTreeSet::new();
            for column in &constraint.group_by {
                budget.tick("input groups")?;
                if *column >= relation.parameters.len() || !columns.insert(*column) {
                    return Err(CheckError::InvalidInputGroup(
                        "invalid or duplicate grouping column",
                    ));
                }
            }
            let mut groups = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
            for atom in &self.inputs {
                budget.tick("input groups")?;
                if atom.relation == constraint.relation {
                    budget.charge(columns.len(), "input groups")?;
                    let key = columns.iter().map(|c| atom.arguments[*c]).collect();
                    groups.entry(key).or_default().push(atom.clone());
                }
            }
            self.input_groups
                .extend(groups.into_values().filter(|g| g.len() > 1));
        }
        Ok(())
    }

    pub(crate) fn validate_input_world(
        &self,
        present: &BTreeSet<GroundAtom>,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        for group in &self.input_groups {
            let mut found = false;
            for atom in group {
                budget.tick("input observation")?;
                if present.contains(atom) {
                    if found {
                        return Err(CheckError::InvalidObservation(atom.clone()));
                    }
                    found = true;
                }
            }
        }
        Ok(())
    }

    /// Only groups with at least two possible tuples need checking. Missing
    /// empty/singleton groups are trivially at-most-one, not global admission.
    pub fn at_most_one_groups(&self) -> impl Iterator<Item = &AtMostOneGroup> {
        self.groups.iter()
    }

    pub fn atoms(&self) -> impl Iterator<Item = &GroundAtom> {
        self.atoms.iter()
    }
    pub fn input_atoms(&self) -> impl Iterator<Item = &GroundAtom> {
        self.inputs.iter()
    }
    pub fn rules(&self) -> impl Iterator<Item = &GroundRule> {
        self.rules
            .iter()
            .filter(|r| !self.rewrites.dropped.contains(&r.id))
    }
    pub fn rule(&self, id: GroundRuleId) -> Option<&GroundRule> {
        (id.preparation == self.preparation && !self.rewrites.dropped.contains(&id))
            .then(|| self.rules.get(id.index))
            .flatten()
    }
    pub fn components(&self) -> impl Iterator<Item = &Component> {
        self.components.iter()
    }
    pub fn component(&self, id: ComponentId) -> Option<&Component> {
        (id.preparation == self.graph_revision)
            .then(|| self.components.get(id.index))
            .flatten()
    }
    /// Looks up a represented node. For legal unrepresented atoms use
    /// is_possible() or Replay::fact(); they have no component.
    pub fn component_for(&self, atom: &GroundAtom) -> Result<&Component> {
        let index = self
            .atom_index
            .get(atom)
            .ok_or_else(|| CheckError::UnknownAtom(atom.clone()))?;
        Ok(&self.components[self.atom_components[*index].index])
    }
    pub fn dependencies(&self) -> impl Iterator<Item = &Dependency> {
        self.dependencies.iter()
    }
    pub fn is_admitted(&self) -> bool {
        self.components.iter().all(|c| c.blocked_by.is_empty())
    }
}

fn validate_domains(
    corpus: &Corpus,
    domains: &Domains,
    budget: &mut Budget<'_>,
) -> Result<Domains> {
    let mut normalized = Domains::new();
    for (sort, values) in domains {
        budget.tick("domains")?;
        if corpus.sort(*sort).is_none() {
            return Err(CheckError::InvalidDomain {
                sort: *sort,
                reason: "unknown or foreign sort",
            });
        }
        let mut distinct = BTreeSet::new();
        for value in values {
            budget.tick("domains")?;
            if corpus.constant(*value).map(|c| c.sort) != Some(*sort) {
                return Err(CheckError::InvalidDomain {
                    sort: *sort,
                    reason: "unknown, foreign or wrong-sort constant",
                });
            }
            if !distinct.insert(*value) {
                return Err(CheckError::InvalidDomain {
                    sort: *sort,
                    reason: "duplicate constant",
                });
            }
        }
        normalized.insert(*sort, distinct.into_iter().collect());
    }
    for sort in corpus.sorts() {
        budget.tick("domains")?;
        if !domains.contains_key(&sort.id) {
            return Err(CheckError::InvalidDomain {
                sort: sort.id,
                reason: "missing finite domain",
            });
        }
    }
    for rule in corpus.rules() {
        budget.tick("domains")?;
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            budget.tick("domains")?;
            for term in atom.arguments() {
                budget.tick("domains")?;
                if let Term::Constant(id) = term.value() {
                    let c = corpus
                        .constant(*id)
                        .ok_or(CheckError::Internal("IR constant missing"))?;
                    if normalized[&c.sort].binary_search(id).is_err() {
                        return Err(CheckError::ConstantOutsideDomain(*id));
                    }
                }
            }
        }
    }
    Ok(normalized)
}

fn ground_atom(
    atom: &Atom,
    binding: &BTreeMap<&str, ConstantId>,
    budget: &mut Budget<'_>,
) -> Result<GroundOccurrence> {
    let mut values = Vec::new();
    let mut origins = Vec::new();
    for term in atom.arguments() {
        budget.tick("grounding")?;
        values.push(match term.value() {
            Term::Constant(id) => *id,
            Term::Variable { name, .. } => *binding
                .get(name.as_str())
                .ok_or(CheckError::Internal("unbound grounding variable"))?,
        });
        origins.push(term.id());
    }
    Ok(GroundOccurrence {
        atom: GroundAtom::new(atom.relation(), values),
        occurrence: atom.id(),
        arguments: origins,
    })
}

// Streaming Cartesian product: do not allocate a product-sized intermediate.
fn each_tuple(
    columns: &[&[ConstantId]],
    budget: &mut Budget<'_>,
    mut emit: impl FnMut(&[ConstantId], &mut Budget<'_>) -> Result<()>,
) -> Result<()> {
    if columns.iter().any(|c| c.is_empty()) {
        return Ok(());
    }
    let mut positions = vec![0; columns.len()];
    loop {
        budget.tick("grounding")?;
        let mut values = Vec::new();
        for (column, index) in columns.iter().zip(&positions) {
            budget.tick("grounding")?;
            values.push(column[*index]);
        }
        emit(&values, budget)?;
        let mut at = columns.len();
        loop {
            if at == 0 {
                return Ok(());
            }
            at -= 1;
            positions[at] += 1;
            if positions[at] < columns[at].len() {
                break;
            }
            positions[at] = 0;
        }
    }
}
