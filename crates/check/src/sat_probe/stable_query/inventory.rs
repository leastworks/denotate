//! Bounded structural reporting, independent of meaning search and its allowances.
use super::*;
use crate::{ComponentId, Dependency};

#[derive(Debug, Clone)]
pub struct NegativeComponent {
    pub id: ComponentId,
    pub representative: AtomKey,
    pub atoms: usize,
    pub relations: Vec<(denotate_ir::RelationId, usize)>,
    /// View-local rule IDs; resolve through Engine::original_instance.
    pub cycle: Vec<Dependency>,
    pub omitted_edges: usize,
    pub cycle_search_complete: bool,
}
#[derive(Debug, Clone)]
pub struct NegativeComponents {
    pub total: usize,
    pub components: Vec<NegativeComponent>,
    pub incomplete: Option<Inconclusive>,
}
impl Engine {
    /// No SAT calls. The caller supplies a separate reporting allowance. A cutoff
    /// preserves the completed prefix and cannot change a checking verdict.
    pub fn negative_components(
        &self,
        keys: &SemanticKeys,
        limits: &Limits,
    ) -> Result<NegativeComponents> {
        let p = &self.program;
        let mut result = NegativeComponents {
            total: p
                .core
                .components
                .iter()
                .filter(|c| c.cycle.is_some())
                .count(),
            components: vec![],
            incomplete: None,
        };
        let mut b = Budget::new(limits);
        let run = (|| -> Result<()> {
            let mut components = Vec::new();
            for c in &p.core.components {
                b.tick("negative component inventory")?;
                if c.cycle.is_none() {
                    continue;
                }
                let mut atoms = BTreeMap::new();
                for a in &c.atoms {
                    b.charge(a.arguments.len() + 1, "negative component inventory")?;
                    atoms.insert(a.clone(), AtomKey::from_atom(keys, a)?);
                }
                components.push((atoms.values().min().unwrap().clone(), c, atoms));
            }
            components.sort_by(|a, b| a.0.cmp(&b.0));
            for (representative, c, atoms) in components {
                let mut relations = BTreeMap::new();
                let mut adjacent = BTreeMap::<_, Vec<Dependency>>::new();
                for a in &c.atoms {
                    *relations.entry(a.relation).or_insert(0) += 1;
                }
                let mut relations = relations.into_iter().collect::<Vec<_>>();
                relations.sort_by_key(|(r, _)| keys.relation(*r).unwrap());
                result.components.push(NegativeComponent {
                    id: c.id,
                    representative,
                    atoms: c.atoms.len(),
                    relations,
                    cycle: vec![],
                    omitted_edges: 0,
                    cycle_search_complete: false,
                });
                for r in p.residual_component_producers(c.id) {
                    for l in &r.body {
                        b.tick("negative component cycle")?;
                        if atoms.contains_key(&l.term.atom) {
                            adjacent
                                .entry(r.head.atom.clone())
                                .or_default()
                                .push(Dependency {
                                    consumer: r.head.atom.clone(),
                                    provider: l.term.atom.clone(),
                                    rule: r.id,
                                    premise: l.term.occurrence,
                                    polarity: l.polarity,
                                });
                        }
                    }
                }
                let edge_key = |e: &Dependency| {
                    (
                        &atoms[&e.consumer],
                        &atoms[&e.provider],
                        keys.rule(self.original_instance(e.rule).unwrap().source)
                            .unwrap(),
                        keys.bindings().key(e.premise).unwrap(),
                    )
                };
                let mut negative = None;
                for edges in adjacent.values_mut() {
                    edges.sort_by(|a, b| edge_key(a).cmp(&edge_key(b)));
                    for e in edges.iter().filter(|e| e.polarity == Polarity::Negative) {
                        if negative.as_ref().is_none_or(|n| edge_key(e) < edge_key(n)) {
                            negative = Some(e.clone());
                        }
                    }
                }
                let edge = negative.ok_or(CheckError::Internal(
                    "negative component without negative edge",
                ))?;
                let mut queue = VecDeque::from([edge.provider.clone()]);
                let mut visited = BTreeSet::from([edge.provider.clone()]);
                let mut previous = BTreeMap::new();
                while let Some(a) = queue.pop_front() {
                    b.tick("negative component cycle")?;
                    if a == edge.consumer {
                        break;
                    }
                    for e in adjacent.get(&a).into_iter().flatten() {
                        b.tick("negative component cycle")?;
                        if visited.insert(e.provider.clone()) {
                            previous.insert(e.provider.clone(), e.clone());
                            queue.push_back(e.provider.clone());
                        }
                    }
                }
                let mut path = Vec::new();
                let mut a = edge.consumer.clone();
                while a != edge.provider {
                    b.tick("negative component cycle")?;
                    let e = previous
                        .get(&a)
                        .ok_or(CheckError::Internal("missing cycle return path"))?;
                    path.push(e.clone());
                    a = e.consumer.clone();
                }
                path.reverse();
                let mut cycle = vec![edge];
                cycle.extend(path);
                let omitted_edges = cycle.len().saturating_sub(12);
                cycle.truncate(12);
                let current = result.components.last_mut().unwrap();
                current.cycle = cycle;
                current.omitted_edges = omitted_edges;
                current.cycle_search_complete = true;
            }
            Ok(())
        })();
        if let Err(e) = run {
            result.incomplete = Some(query_inconclusive(e)?);
        }
        Ok(result)
    }
}
