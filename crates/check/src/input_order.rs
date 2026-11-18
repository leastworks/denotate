//! Diagnostic BDD placement, using only the prepared dependency graph.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::SemanticKeys;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum InputOrder {
    #[default]
    Key,
    ReverseKey,
    Structural,
}
impl InputOrder {
    pub fn label(self) -> &'static str {
        match self {
            Self::Key => "key",
            Self::ReverseKey => "reverse-key",
            Self::Structural => "structural",
        }
    }
}
impl std::str::FromStr for InputOrder {
    type Err = &'static str;
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "key" => Ok(Self::Key),
            "reverse-key" => Ok(Self::ReverseKey),
            "structural" => Ok(Self::Structural),
            _ => Err("input order must be key, reverse-key or structural"),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InputOrderReport {
    pub requested: InputOrder,
    pub effective: InputOrder,
    pub fallback: Option<&'static str>,
    pub inputs: usize,
    /// Peak retained placement entries, including temporary containers; not bytes.
    pub structural_entries: usize,
    pub structural_work: usize,
    pub fallback_limit: Option<usize>,
    pub fallback_observed: Option<usize>,
    pub hyperedges: usize,
    pub passes: usize,
}

// Optimization cutoffs, not checker limits. The original key order remains usable.
const PASSES: usize = 8;
enum Stop {
    Cutoff(&'static str, usize, usize),
    Check(CheckError),
}
impl From<CheckError> for Stop {
    fn from(e: CheckError) -> Self {
        Self::Check(e)
    }
}
type Placement<T> = std::result::Result<T, Stop>;
struct Meter<'a, 'b> {
    budget: &'a mut Budget<'b>,
    visits: usize,
    entries: usize,
    peak: usize,
    cap: usize,
    work_cap: usize,
}
impl Meter<'_, '_> {
    fn visit(&mut self, n: usize) -> Placement<()> {
        self.budget.charge(n, "input ordering")?;
        self.visits = self.visits.saturating_add(n);
        if self.visits > self.work_cap {
            return Err(Stop::Cutoff(
                "structural work allowance",
                self.work_cap,
                self.visits,
            ));
        }
        Ok(())
    }
    fn store(&mut self, n: usize) -> Placement<()> {
        self.visit(n)?;
        self.entries = self.entries.saturating_add(n);
        self.peak = self.peak.max(self.entries);
        if self.entries > self.cap {
            return Err(Stop::Cutoff(
                "structural entry allowance",
                self.cap,
                self.entries,
            ));
        }
        Ok(())
    }
    fn release(&mut self, n: usize) {
        self.entries -= n;
    }
}

impl GroundProgram {
    pub fn input_order_report(&self) -> &InputOrderReport {
        &self.order_report
    }
    pub fn ordered_input_atoms(&self) -> impl Iterator<Item = &GroundAtom> {
        self.ordered_inputs().into_iter()
    }

    pub(crate) fn choose_input_order(
        self,
        keys: &SemanticKeys,
        constraints: &[InputConstraint],
        order: InputOrder,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let cap = budget.limits.max_input_order_entries;
        self.choose_input_order_bounded(keys, constraints, order, budget, cap)
    }
    fn choose_input_order_bounded(
        mut self,
        keys: &SemanticKeys,
        constraints: &[InputConstraint],
        order: InputOrder,
        budget: &mut Budget<'_>,
        cutoff: usize,
    ) -> Result<Self> {
        if self.input_order.is_none() || self.order_report.requested != InputOrder::Key {
            self = self.with_atom_key_order(keys)?;
        }
        if order == InputOrder::Key {
            return Ok(self);
        }
        self.order_report = InputOrderReport {
            requested: order,
            effective: order,
            inputs: self.inputs.len(),
            ..Default::default()
        };
        let key_order = self.input_order.as_ref().unwrap();
        let chosen = if order == InputOrder::ReverseKey {
            budget.charge(key_order.len(), "input ordering")?;
            key_order.iter().rev().cloned().collect()
        } else {
            let mut report = self.order_report.clone();
            let result = self.structural_order(keys, constraints, budget, cutoff, &mut report);
            let ordered = match result {
                Ok(indices) => indices.into_iter().map(|i| key_order[i].clone()).collect(),
                Err(Stop::Cutoff(reason, limit, observed)) => {
                    report.fallback_limit = Some(limit);
                    report.fallback_observed = Some(observed);
                    report.effective = InputOrder::Key;
                    report.fallback = Some(reason);
                    key_order.clone()
                }
                Err(Stop::Check(e)) => return Err(e),
            };
            self.order_report = report;
            ordered
        };
        // Ground instance IDs stay unchanged. Conditions have a separate identity:
        // a clone with another layout must reject the old layout's conditions.
        self.variable_map = crate::ground::next_identity();
        self.input_order = Some(chosen);
        Ok(self)
    }

    pub(crate) fn inherit_input_order(&mut self, from: &Self) -> Result<()> {
        if self.inputs != from.inputs || self.assumption_condition.is_some() {
            return Err(CheckError::Internal("incompatible assumption variable map"));
        }
        self.input_order = from.input_order.clone();
        self.variable_map = from.variable_map;
        self.order_report = from.order_report.clone();
        Ok(())
    }

    fn structural_order(
        &self,
        keys: &SemanticKeys,
        constraints: &[InputConstraint],
        budget: &mut Budget<'_>,
        cap: usize,
        report: &mut InputOrderReport,
    ) -> Placement<Vec<usize>> {
        let work_cap = budget.limits.max_input_order_work;
        let mut meter = Meter {
            budget,
            visits: 0,
            entries: 0,
            peak: 0,
            cap,
            work_cap,
        };
        let result = self.place(keys, constraints, &mut meter, report);
        report.structural_entries = meter.peak;
        report.structural_work = meter.visits;
        result
    }

    fn place(
        &self,
        keys: &SemanticKeys,
        constraints: &[InputConstraint],
        meter: &mut Meter<'_, '_>,
        report: &mut InputOrderReport,
    ) -> Placement<Vec<usize>> {
        let ordered = self.input_order.as_ref().unwrap();
        meter.store(ordered.len())?;
        let inputs: BTreeMap<_, _> = ordered.iter().enumerate().map(|(i, a)| (a, i)).collect();
        let mut supports = BTreeMap::<ComponentId, usize>::new();
        let mut pool = Supports::default();
        let mut edges = BTreeMap::<usize, u64>::new();
        // Canonical support IDs share vectors across providers, readers and edges.
        // IDs affect iteration only: weighted sums are exact integers.
        for rule in self
            .core
            .rules
            .iter()
            .filter(|r| !self.rewrites.dropped.contains(&r.id))
        {
            meter.visit(1)?;
            let mut parts = Vec::new();
            for literal in rule.dependency_literals() {
                meter.visit(1)?;
                let Some(i) = self.atom_index.get(&literal.term.atom) else {
                    continue;
                };
                let id = self.atom_components[*i];
                if self.components[id.index].blocked_by.is_empty() {
                    self.support(id, &inputs, &mut supports, &mut pool, meter)?;
                    meter.store(1)?;
                    parts.push(supports[&id]);
                }
            }
            let count = parts.len();
            let edge = pool.union(parts, meter)?;
            meter.release(count);
            add_edge(&mut edges, edge, 1, &pool, meter)?;
        }
        let mut groups = BTreeSet::new();
        for group in self
            .input_groups
            .iter()
            .chain(self.universe_groups.iter().map(|g| &g.atoms))
        {
            meter.visit(group.len())?;
            meter.store(group.len())?;
            let count = group.len();
            let mut group: Vec<_> = group.iter().map(|a| inputs[a]).collect();
            sort_work(group.len(), meter)?;
            group.sort_unstable();
            let id = pool.intern(group, meter)?;
            meter.release(count);
            if groups.insert(id) {
                meter.store(1)?;
            }
        }
        for constraint in constraints {
            let mut parts = Vec::new();
            let mut exclusive = BTreeMap::<Vec<_>, Vec<usize>>::new();
            let mut exclusive_entries = 0;
            for atom in &self.core.atoms {
                meter.visit(1)?;
                if keys.relation(atom.relation).map_err(CheckError::Keys)? != constraint.relation()
                {
                    continue;
                }
                let id = self.atom_components[self.atom_index[atom]];
                self.support(id, &inputs, &mut supports, &mut pool, meter)?;
                meter.store(1)?;
                parts.push(supports[&id]);
                if constraint.kind().has_uniqueness() {
                    if let Some(i) = inputs.get(atom) {
                        let group =
                            constraint
                                .group_by()
                                .iter()
                                .map(|c| {
                                    atom.arguments.get(*c).copied().ok_or(
                                        CheckError::InvalidRequest("invalid assumption grouping"),
                                    )
                                })
                                .collect::<Result<Vec<_>>>()?;
                        let n = 1 + if exclusive.contains_key(&group) {
                            0
                        } else {
                            1 + group.len()
                        };
                        meter.store(n)?;
                        exclusive_entries += n;
                        exclusive.entry(group).or_default().push(*i);
                    }
                }
            }
            let count = parts.len();
            let edge = pool.union(parts, meter)?;
            meter.release(count);
            add_edge(&mut edges, edge, 1, &pool, meter)?;
            for mut group in exclusive.into_values().filter(|g| g.len() > 1) {
                sort_work(group.len(), meter)?;
                group.sort_unstable();
                let id = pool.intern(group, meter)?;
                if groups.insert(id) {
                    meter.store(1)?;
                }
            }
            meter.release(exclusive_entries);
        }
        for group in &groups {
            add_edge(&mut edges, *group, 4, &pool, meter)?;
        }
        meter.release(groups.len());
        drop(groups);
        report.hyperedges = edges.len();
        meter.store(6 * ordered.len())?; // order, best, positions and weighted centers
        let mut order: Vec<_> = (0..ordered.len()).collect();
        let mut best = order.clone();
        let mut best_cost = u128::MAX;
        for pass in 0..=PASSES {
            meter.visit(order.len())?;
            let mut positions = vec![0u128; order.len()];
            for (i, b) in order.iter().enumerate() {
                positions[*b] = i as u128;
            }
            let mut cost = 0;
            let mut centers = vec![(0u128, 0u128); order.len()];
            for (edge, weight) in &edges {
                let edge = &pool.sets[*edge];
                meter.visit(edge.len())?;
                let min = edge.iter().map(|b| positions[*b]).min().unwrap();
                let max = edge.iter().map(|b| positions[*b]).max().unwrap();
                cost += (max - min) * u128::from(*weight);
                // Fixed-point integer arithmetic: no platform-dependent floats.
                let center = edge.iter().map(|b| positions[*b]).sum::<u128>() * (1 << 20)
                    / edge.len() as u128;
                for b in edge.iter() {
                    centers[*b].0 += center * u128::from(*weight);
                    centers[*b].1 += u128::from(*weight);
                }
            }
            if cost < best_cost || (cost == best_cost && order < best) {
                best_cost = cost;
                best = order.clone();
            }
            report.passes = pass;
            if pass == PASSES {
                break;
            }
            meter.visit(
                order
                    .len()
                    .saturating_mul(order.len().max(1).ilog2() as usize + 1),
            )?;
            order.sort_by_key(|b| {
                let (sum, weight) = centers[*b];
                (
                    if weight == 0 {
                        positions[*b] * (1 << 20)
                    } else {
                        sum / weight
                    },
                    *b,
                )
            });
        }
        Ok(best)
    }

    fn support(
        &self,
        root: ComponentId,
        inputs: &BTreeMap<&GroundAtom, usize>,
        cache: &mut BTreeMap<ComponentId, usize>,
        pool: &mut Supports,
        meter: &mut Meter<'_, '_>,
    ) -> Placement<()> {
        meter.store(1)?;
        let mut pending = vec![(root, false)];
        while let Some((id, finishing)) = pending.pop() {
            meter.release(1);
            meter.visit(1)?;
            if cache.contains_key(&id) {
                continue;
            }
            let c = &self.components[id.index];
            if !finishing {
                meter.store(1)?;
                pending.push((id, true));
                for d in &c.dependencies {
                    meter.visit(1)?;
                    if !cache.contains_key(d) {
                        meter.store(1)?;
                        pending.push((*d, false));
                    }
                }
            } else {
                let mut local = Vec::new();
                for atom in &c.atoms {
                    meter.visit(1)?;
                    if let Some(i) = inputs.get(atom) {
                        meter.store(1)?;
                        local.push(*i);
                    }
                }
                sort_work(local.len(), meter)?;
                local.sort_unstable();
                local.dedup();
                let local_count = local.len();
                let local = pool.intern(local, meter)?;
                meter.release(local_count);
                let mut parts = Vec::new();
                meter.store(1 + c.dependencies.len())?;
                parts.push(local);
                parts.extend(c.dependencies.iter().map(|d| cache[d]));
                let count = parts.len();
                let support = pool.union(parts, meter)?;
                meter.release(count);
                meter.store(1)?;
                cache.insert(id, support);
            }
        }
        Ok(())
    }
}

fn sort_work(n: usize, meter: &mut Meter<'_, '_>) -> Placement<()> {
    meter.visit(n.saturating_mul(n.max(1).ilog2() as usize + 1))
}

/// Intern expanded supports once; memoize unions of provider IDs, so repeated
/// readers do not expand the same wide set again. All storage is invocation-local.
#[derive(Default)]
struct Supports {
    sets: Vec<Arc<[usize]>>,
    ids: BTreeMap<Arc<[usize]>, usize>,
    unions: BTreeMap<Vec<usize>, usize>,
}
impl Supports {
    fn intern(&mut self, values: Vec<usize>, meter: &mut Meter<'_, '_>) -> Placement<usize> {
        // Conservative comparison work; equality is not a free storage hit.
        meter.visit(
            values
                .len()
                .saturating_mul(self.ids.len().max(1).ilog2() as usize + 1),
        )?;
        if let Some(id) = self.ids.get(values.as_slice()) {
            return Ok(*id);
        }
        meter.store(values.len() + 2)?;
        let id = self.sets.len();
        let values: Arc<[usize]> = values.into();
        self.ids.insert(values.clone(), id);
        self.sets.push(values);
        Ok(id)
    }
    fn union(&mut self, mut parts: Vec<usize>, meter: &mut Meter<'_, '_>) -> Placement<usize> {
        sort_work(parts.len(), meter)?;
        parts.retain(|id| !self.sets[*id].is_empty());
        parts.sort_unstable();
        parts.dedup();
        if parts.len() == 1 {
            return Ok(parts[0]);
        }
        meter.visit(
            parts
                .len()
                .saturating_mul(self.unions.len().max(1).ilog2() as usize + 1),
        )?;
        if let Some(id) = self.unions.get(&parts) {
            return Ok(*id);
        }
        let mut values = BTreeSet::new();
        for part in &parts {
            for v in self.sets[*part].iter() {
                meter.visit(values.len().max(1).ilog2() as usize + 1)?;
                if values.insert(*v) {
                    meter.store(1)?;
                }
            }
        }
        let count = values.len();
        let id = self.intern(values.into_iter().collect(), meter)?;
        meter.release(count);
        meter.store(1 + parts.len())?;
        self.unions.insert(parts, id);
        Ok(id)
    }
}
fn add_edge(
    edges: &mut BTreeMap<usize, u64>,
    edge: usize,
    weight: u64,
    pool: &Supports,
    meter: &mut Meter<'_, '_>,
) -> Placement<()> {
    if pool.sets[edge].len() < 2 {
        return Ok(());
    }
    meter.visit(edges.len().max(1).ilog2() as usize + 1)?;
    if !edges.contains_key(&edge) {
        meter.store(1)?;
    }
    *edges.entry(edge).or_default() += weight;
    Ok(())
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod reference;
