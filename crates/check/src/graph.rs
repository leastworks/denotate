use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::OccurrenceId;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::{AtomicU64, Ordering};

/// Direction: consumer depends on provider. The premise occurrence points to
/// the signed atom in the original rule, including its lowering origins.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dependency {
    pub consumer: GroundAtom,
    pub provider: GroundAtom,
    pub rule: GroundRuleId,
    pub premise: OccurrenceId,
    pub polarity: Polarity,
}

/// One closed, ordered dependency path per non-stratifiable SCC. Includes a
/// negative edge and every rule on this path, not every possible cycle in the SCC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cycle {
    pub edges: Vec<Dependency>,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub id: ComponentId,
    pub atoms: Vec<GroundAtom>,
    pub dependencies: BTreeSet<ComponentId>,
    /// Has an internal dependency edge, including a singleton's self-loop.
    /// Components without one need only a single evaluation pass.
    pub recursive: bool,
    /// Root unresolved components, including this one if it has a negative cycle.
    pub blocked_by: BTreeSet<ComponentId>,
    pub cycle: Option<Cycle>,
}

pub(crate) fn analyze(p: &mut GroundProgram, budget: &mut Budget<'_>) -> Result<()> {
    let p = &mut **p;
    static NEXT: AtomicU64 = AtomicU64::new(1);
    p.graph_revision = NEXT.fetch_add(1, Ordering::Relaxed);
    p.dependencies.clear();
    p.components.clear();
    let n = p.atoms.len();
    let mut adjacent = vec![Vec::new(); n];
    let mut reverse = vec![Vec::new(); n];
    for rule in &p.rules {
        budget.tick("dependencies")?;
        if p.rewrites.dropped.contains(&rule.id) {
            continue;
        }
        let consumer = p.atom_index[&rule.head.atom];
        for literal in rule.dependency_literals() {
            budget.tick("dependencies")?;
            let Some(&provider) = p.atom_index.get(&literal.term.atom) else {
                if p.fixed_value(&literal.term.atom).is_some() {
                    // Keep the original boundary edge as evidence, but do not
                    // schedule an already-settled provider in the residual graph.
                    budget.room(
                        p.dependencies.len().saturating_add(
                            p.fixed.as_ref().map_or(0, |f| f.program.dependencies.len()),
                        ),
                        budget.limits.max_dependencies,
                        "dependencies",
                        "dependencies",
                    )?;
                    p.dependencies.push(Dependency {
                        consumer: rule.head.atom.clone(),
                        provider: literal.term.atom.clone(),
                        rule: rule.id,
                        premise: literal.term.occurrence,
                        polarity: literal.polarity,
                    });
                    continue;
                }
                if literal.polarity == Polarity::Positive {
                    return Err(CheckError::Internal("impossible positive premise"));
                }
                // A structurally impossible negative premise is statically true.
                // Its occurrence stays in the rule and in replay evidence.
                continue;
            };
            budget.room(
                p.dependencies
                    .len()
                    .saturating_add(p.fixed.as_ref().map_or(0, |f| f.program.dependencies.len())),
                budget.limits.max_dependencies,
                "dependencies",
                "dependencies",
            )?;
            adjacent[consumer].push(p.dependencies.len());
            reverse[provider].push(consumer);
            p.dependencies.push(Dependency {
                consumer: rule.head.atom.clone(),
                provider: literal.term.atom.clone(),
                rule: rule.id,
                premise: literal.term.occurrence,
                polarity: literal.polarity,
            });
        }
    }

    // Iterative Kosaraju avoids a Rust call-stack limit on long rule chains.
    let mut seen = vec![false; n];
    let mut finish = Vec::new();
    for root in 0..n {
        budget.tick("components")?;
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((node, next)) = stack.last_mut() {
            budget.tick("components")?;
            if let Some(edge) = adjacent[*node].get(*next) {
                *next += 1;
                let provider = p.atom_index[&p.dependencies[*edge].provider];
                if !seen[provider] {
                    seen[provider] = true;
                    stack.push((provider, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }
    seen.fill(false);
    let mut groups = Vec::new();
    for root in finish.into_iter().rev() {
        budget.tick("components")?;
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut group = Vec::new();
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            budget.tick("components")?;
            group.push(node);
            for consumer in &reverse[node] {
                budget.tick("components")?;
                if !seen[*consumer] {
                    seen[*consumer] = true;
                    stack.push(*consumer);
                }
            }
        }
        group.sort_unstable();
        groups.push(group);
    }
    groups.reverse(); // edges point to dependencies: reverse gives provider-first
    let mut membership = vec![0; n];
    for (index, group) in groups.iter().enumerate() {
        for node in group {
            budget.tick("components")?;
            membership[*node] = index;
        }
    }
    p.atom_components = membership
        .iter()
        .map(|index| ComponentId {
            preparation: p.graph_revision,
            index: *index,
        })
        .collect();
    for (index, group) in groups.iter().enumerate() {
        let id = ComponentId {
            preparation: p.graph_revision,
            index,
        };
        let mut dependencies = BTreeSet::new();
        let mut recursive = false;
        let mut negative = None;
        for node in group {
            for edge in &adjacent[*node] {
                budget.tick("components")?;
                let e = &p.dependencies[*edge];
                let provider = p.atom_index[&e.provider];
                if membership[provider] != index {
                    let other = p.atom_components[provider];
                    if other.index >= index {
                        return Err(CheckError::Internal("components not provider-first"));
                    }
                    dependencies.insert(other);
                } else {
                    recursive = true;
                    if e.polarity == Polarity::Negative && negative.is_none() {
                        negative = Some(*edge);
                    }
                }
            }
        }
        let cycle = negative
            .map(|edge| cycle_path(p, &adjacent, &membership, edge, budget))
            .transpose()?;
        let mut blocked_by = BTreeSet::new();
        if cycle.is_some() {
            blocked_by.insert(id);
        }
        for dependency in &dependencies {
            for root in &p.components[dependency.index].blocked_by {
                budget.tick("components")?;
                blocked_by.insert(*root);
            }
        }
        p.components.push(Component {
            id,
            atoms: group.iter().map(|i| p.atoms[*i].clone()).collect(),
            dependencies,
            recursive,
            blocked_by,
            cycle,
        });
    }
    p.component_rules = vec![vec![]; p.components.len()];
    for (index, rule) in p.rules.iter().enumerate() {
        budget.tick("components")?;
        if p.rewrites.dropped.contains(&rule.id) {
            continue;
        }
        p.component_rules[p.atom_components[p.atom_index[&rule.head.atom]].index].push(index);
    }
    Ok(())
}

fn cycle_path(
    p: &GroundCore,
    adjacent: &[Vec<usize>],
    membership: &[usize],
    negative: usize,
    budget: &mut Budget<'_>,
) -> Result<Cycle> {
    let edge = &p.dependencies[negative];
    let start = p.atom_index[&edge.provider];
    let target = p.atom_index[&edge.consumer];
    let component = membership[start];
    let mut queue = VecDeque::from([start]);
    let mut visited = BTreeSet::from([start]);
    let mut previous = BTreeMap::new();
    while let Some(node) = queue.pop_front() {
        budget.tick("cycle evidence")?;
        if node == target {
            break;
        }
        for edge in &adjacent[node] {
            budget.tick("cycle evidence")?;
            let next = p.atom_index[&p.dependencies[*edge].provider];
            if membership[next] == component && visited.insert(next) {
                previous.insert(next, *edge);
                queue.push_back(next);
            }
        }
    }
    let mut tail = Vec::new();
    let mut at = target;
    while at != start {
        budget.tick("cycle evidence")?;
        let edge = *previous
            .get(&at)
            .ok_or(CheckError::Internal("SCC cycle path missing"))?;
        tail.push(p.dependencies[edge].clone());
        at = p.atom_index[&p.dependencies[edge].consumer];
    }
    tail.reverse();
    let mut edges = vec![p.dependencies[negative].clone()];
    edges.extend(tail);
    Ok(Cycle { edges })
}
