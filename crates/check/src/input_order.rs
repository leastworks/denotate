//! Diagnostic BDD placement, using only the prepared dependency graph.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::SemanticKeys;
use std::collections::{BTreeMap, BTreeSet};

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
    pub structural_entries: usize,
    pub hyperedges: usize,
    pub passes: usize,
}

// Optimization cutoffs, not checker limits. The original key order remains usable.
const STRUCTURAL_ENTRIES: usize = 1_000_000;
const VISITS: usize = 4_000_000;
const PASSES: usize = 8;
enum Stop {
    Cutoff(&'static str),
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
    cap: usize,
}
impl Meter<'_, '_> {
    fn visit(&mut self, n: usize) -> Placement<()> {
        self.budget.charge(n, "input ordering")?;
        self.visits = self.visits.saturating_add(n);
        if self.visits > VISITS {
            return Err(Stop::Cutoff("structural traversal cutoff"));
        }
        Ok(())
    }
    fn store(&mut self, n: usize) -> Placement<()> {
        self.visit(n)?;
        self.entries = self.entries.saturating_add(n);
        if self.entries > self.cap {
            return Err(Stop::Cutoff("structural entry cutoff"));
        }
        Ok(())
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
        self.choose_input_order_bounded(keys, constraints, order, budget, STRUCTURAL_ENTRIES)
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
                Err(Stop::Cutoff(reason)) => {
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
        let mut meter = Meter {
            budget,
            visits: 0,
            entries: 0,
            cap,
        };
        let result = self.place(keys, constraints, &mut meter, report);
        report.structural_entries = meter.entries;
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
        let mut supports = BTreeMap::<ComponentId, Vec<usize>>::new();
        let mut edges = BTreeMap::<Vec<usize>, u64>::new();
        // Fixed evidence has no inputs. Read only executable residual rules.
        for rule in self
            .core
            .rules
            .iter()
            .filter(|r| !self.rewrites.dropped.contains(&r.id))
        {
            meter.visit(1)?;
            let mut edge = BTreeSet::new();
            for literal in rule.dependency_literals() {
                meter.visit(1)?;
                let Some(i) = self.atom_index.get(&literal.term.atom) else {
                    continue;
                };
                let id = self.atom_components[*i];
                if self.components[id.index].blocked_by.is_empty() {
                    self.support(id, &inputs, &mut supports, meter)?;
                    meter.visit(supports[&id].len())?;
                    edge.extend(supports[&id].iter().copied());
                }
            }
            add_edge(&mut edges, edge.into_iter().collect(), 1, meter)?;
        }
        let mut groups = BTreeSet::<Vec<usize>>::new();
        for group in &self.input_groups {
            meter.visit(group.len())?;
            let mut group: Vec<_> = group.iter().map(|a| inputs[a]).collect();
            group.sort_unstable();
            meter.store(group.len())?;
            groups.insert(group);
        }
        // Selected general assumptions supply structural preferences too. Only
        // input-only uniqueness groups are eligible for hard contiguous blocks.
        for constraint in constraints {
            let mut edge = BTreeSet::new();
            let mut exclusive = BTreeMap::<Vec<_>, Vec<usize>>::new();
            for atom in &self.core.atoms {
                meter.visit(1)?;
                if keys.relation(atom.relation).map_err(CheckError::Keys)? != constraint.relation()
                {
                    continue;
                }
                let id = self.atom_components[self.atom_index[atom]];
                self.support(id, &inputs, &mut supports, meter)?;
                meter.visit(supports[&id].len())?;
                edge.extend(supports[&id].iter().copied());
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
                        meter.store(1)?;
                        exclusive.entry(group).or_default().push(*i);
                    }
                }
            }
            add_edge(&mut edges, edge.into_iter().collect(), 1, meter)?;
            for mut group in exclusive.into_values().filter(|g| g.len() > 1) {
                group.sort_unstable();
                groups.insert(group);
            }
        }
        let mut counts = vec![0usize; ordered.len()];
        for group in &groups {
            meter.visit(group.len())?;
            for i in group {
                counts[*i] += 1;
            }
            add_edge(&mut edges, group.clone(), 4, meter)?;
        }
        let mut blocks = Vec::new();
        let mut assigned = vec![false; ordered.len()];
        for group in &groups {
            meter.visit(group.len())?;
            if group.iter().all(|i| counts[*i] == 1) {
                for i in group {
                    assigned[*i] = true;
                }
                blocks.push(group.clone());
            }
        }
        blocks.extend(
            (0..ordered.len())
                .filter(|i| !assigned[*i])
                .map(|i| vec![i]),
        );
        blocks.sort_by_key(|b| b[0]);
        let mut owner = vec![0; ordered.len()];
        for (b, members) in blocks.iter().enumerate() {
            for i in members {
                owner[*i] = b;
            }
        }
        let mut block_edges = BTreeMap::new();
        for (edge, weight) in edges {
            meter.visit(edge.len())?;
            let edge = edge
                .into_iter()
                .map(|i| owner[i])
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            add_edge(&mut block_edges, edge, weight, meter)?;
        }
        report.hyperedges = block_edges.len();
        let mut order: Vec<_> = (0..blocks.len()).collect();
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
            for (edge, weight) in &block_edges {
                meter.visit(edge.len())?;
                let min = edge.iter().map(|b| positions[*b]).min().unwrap();
                let max = edge.iter().map(|b| positions[*b]).max().unwrap();
                cost += (max - min) * u128::from(*weight);
                // Fixed-point integer arithmetic: no platform-dependent floats.
                let center = edge.iter().map(|b| positions[*b]).sum::<u128>() * (1 << 20)
                    / edge.len() as u128;
                for b in edge {
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
                    blocks[*b][0],
                )
            });
        }
        Ok(best
            .into_iter()
            .flat_map(|b| blocks[b].iter().copied())
            .collect())
    }

    fn support(
        &self,
        root: ComponentId,
        inputs: &BTreeMap<&GroundAtom, usize>,
        cache: &mut BTreeMap<ComponentId, Vec<usize>>,
        meter: &mut Meter<'_, '_>,
    ) -> Placement<()> {
        let mut pending = vec![(root, false)];
        while let Some((id, finishing)) = pending.pop() {
            meter.visit(1)?;
            if cache.contains_key(&id) {
                continue;
            }
            let c = &self.components[id.index];
            if !finishing {
                meter.store(1 + c.dependencies.len())?;
                pending.push((id, true));
                pending.extend(
                    c.dependencies
                        .iter()
                        .filter(|d| !cache.contains_key(d))
                        .map(|d| (*d, false)),
                );
            } else {
                let mut support = BTreeSet::new();
                for atom in &c.atoms {
                    meter.visit(1)?;
                    if let Some(i) = inputs.get(atom) {
                        support.insert(*i);
                    }
                }
                for dependency in &c.dependencies {
                    meter.visit(cache[dependency].len())?;
                    support.extend(cache[dependency].iter().copied());
                }
                meter.store(support.len())?;
                cache.insert(id, support.into_iter().collect());
            }
        }
        Ok(())
    }
}
fn add_edge(
    edges: &mut BTreeMap<Vec<usize>, u64>,
    edge: Vec<usize>,
    weight: u64,
    meter: &mut Meter<'_, '_>,
) -> Placement<()> {
    if edge.len() < 2 {
        return Ok(());
    }
    meter.store(1 + edge.len())?;
    *edges.entry(edge).or_default() += weight;
    Ok(())
}

#[cfg(test)]
mod tests;
