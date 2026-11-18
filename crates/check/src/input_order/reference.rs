//! Pre-sharing expansion retained only as an independent placement oracle.
use super::*;
impl GroundProgram {
    pub(super) fn reference_place(
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
                    self.reference_support(id, &inputs, &mut supports, meter)?;
                    meter.visit(supports[&id].len())?;
                    edge.extend(supports[&id].iter().copied());
                }
            }
            reference_add_edge(&mut edges, edge.into_iter().collect(), 1, meter)?;
        }
        let mut groups = BTreeSet::<Vec<usize>>::new();
        for group in self
            .input_groups
            .iter()
            .chain(self.universe_groups.iter().map(|g| &g.atoms))
        {
            meter.visit(group.len())?;
            let mut group: Vec<_> = group.iter().map(|a| inputs[a]).collect();
            group.sort_unstable();
            meter.store(group.len())?;
            groups.insert(group);
        }
        // Selected general assumptions supply structural preferences too.
        // Exclusivity influences placement without forcing its inputs together:
        // each member may be co-read with inputs outside the group.
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
                self.reference_support(id, &inputs, &mut supports, meter)?;
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
            reference_add_edge(&mut edges, edge.into_iter().collect(), 1, meter)?;
            for mut group in exclusive.into_values().filter(|g| g.len() > 1) {
                group.sort_unstable();
                groups.insert(group);
            }
        }
        for group in &groups {
            meter.visit(group.len())?;
            reference_add_edge(&mut edges, group.clone(), 4, meter)?;
        }
        report.hyperedges = edges.len();
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
                    *b,
                )
            });
        }
        Ok(best)
    }

    fn reference_support(
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
fn reference_add_edge(
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
