//! Optional in-component observations. No semantic queries or budget charges.
use super::*;
use crate::profile::{RecursiveComponentShape, RecursiveRelation, RecursiveSnapshot};

pub(super) struct Observation<'a> {
    profile: &'a Profile,
    component: &'a Component,
    last: Instant,
    traffic: (u64, u64),
    rounds: usize,
    visits: usize,
    evaluations: usize,
    restarts: usize,
    changed: BTreeSet<&'a GroundAtom>,
    previous_changed: usize,
    scheduler_entries: usize,
}
impl<'a> Observation<'a> {
    pub fn new(
        program: &GroundProgram,
        component: &'a Component,
        profile: &'a Profile,
    ) -> Option<Self> {
        if !component.recursive || !profile.conditions_enabled() {
            return None;
        }
        profile.condition(|| ConditionObservation::RecursiveShape(shape(program, component)));
        Some(Self {
            profile,
            component,
            last: Instant::now(),
            traffic: profile.result_traffic(),
            rounds: 0,
            visits: 0,
            evaluations: 0,
            restarts: 0,
            changed: BTreeSet::new(),
            previous_changed: 0,
            scheduler_entries: 0,
        })
    }
    pub fn scheduler(&mut self, entries: usize) {
        self.scheduler_entries = entries;
    }
    pub fn visit<const W: bool>(&mut self, meaning: &SymbolicMeaning<'_, W>, retained: usize) {
        self.visits += 1;
        // Do not read the clock or scan the component on every producer.
        if self.visits % 256 == 0 && self.last.elapsed() >= Duration::from_secs(1) {
            self.emit(meaning, retained, "running", None);
        }
    }
    pub fn evaluated(&mut self) {
        self.evaluations += 1;
    }
    pub fn changed(&mut self, atom: &'a GroundAtom) {
        self.changed.insert(atom);
    }
    pub fn round(&mut self) {
        self.rounds += 1;
        self.previous_changed = self.changed.len();
        self.changed.clear();
    }
    pub fn restart(&mut self) {
        self.restarts += 1;
        self.changed.clear();
    }
    pub fn emit<const W: bool>(
        &mut self,
        meaning: &SymbolicMeaning<'_, W>,
        retained: usize,
        state: &'static str,
        error: Option<&CheckError>,
    ) {
        self.profile.condition(|| {
            let mut relations = BTreeMap::<_, (usize, usize, usize)>::new();
            let mut largest = Vec::new();
            let mut conditions = Vec::new();
            let mut counted = 0;
            for atom in &self.component.atoms {
                let r = relations.entry(atom.relation).or_default();
                r.0 += 1;
                if let Some(c) = meaning.conditions.get(atom) {
                    let nodes = c.node_count();
                    r.1 += 1;
                    r.2 += nodes;
                    counted += nodes;
                    conditions.push(c);
                    if largest.len() < 10
                        || largest
                            .last()
                            .is_some_and(|(a, n)| nodes > *n || (nodes == *n && atom < a))
                    {
                        largest.push((atom.clone(), nodes));
                        largest.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                        largest.truncate(10);
                    }
                }
            }
            let storage = crate::boolean::condition_storage(conditions);
            let mut relations: Vec<_> = relations
                .into_iter()
                .map(|(relation, (atoms, conditions, nodes))| RecursiveRelation {
                    relation,
                    atoms,
                    conditions,
                    nodes,
                })
                .collect();
            relations.sort_by(|a, b| {
                b.nodes
                    .cmp(&a.nodes)
                    .then_with(|| a.relation.cmp(&b.relation))
            });
            let omitted_relations = relations.len().saturating_sub(20);
            relations.truncate(20);
            let traffic = self.profile.result_traffic();
            ConditionObservation::RecursiveSnapshot(RecursiveSnapshot {
                component: self.component.id.index + 1,
                state,
                error: error.cloned(),
                completed_rounds: self.rounds,
                rule_visits: self.visits,
                rule_evaluations: self.evaluations,
                changed_heads: self.changed.len(),
                previous_round_changed_heads: self.previous_changed,
                restarts: self.restarts,
                scheduler_entries: self.scheduler_entries,
                accounted_nodes: retained,
                component_nodes: counted,
                storage,
                result_arrays: traffic.0.saturating_sub(self.traffic.0),
                result_nodes: traffic.1.saturating_sub(self.traffic.1),
                largest,
                relations,
                omitted_relations,
            })
        });
        self.last = Instant::now();
    }
}

fn shape(program: &GroundProgram, component: &Component) -> RecursiveComponentShape {
    let mut relations = BTreeMap::new();
    for a in &component.atoms {
        *relations.entry(a.relation).or_insert(0) += 1;
    }
    let mut relations: Vec<_> = relations.into_iter().collect();
    relations.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let omitted_relations = relations.len().saturating_sub(20);
    relations.truncate(20);
    // A bounded graph sample, not an exhaustive cycle census. Keep actual closed
    // paths only; failure to find a short cycle does not imply acyclicity.
    let mut graph = BTreeMap::<&GroundAtom, Vec<&GroundAtom>>::new();
    let mut edges = 0;
    let mut truncated = false;
    'rules: for i in &program.component_rules[component.id.index] {
        let rule = &program.rules[*i];
        for literal in rule.dependency_literals() {
            if edges == 4096 {
                truncated = true;
                break 'rules;
            }
            edges += 1;
            let provider = &literal.term.atom;
            // dependency_literals owns its literals, so borrow the canonical atom.
            if let Some(&a) = program.atom_index.get(provider) {
                if program.atom_components[a] == component.id {
                    graph
                        .entry(&rule.head.atom)
                        .or_default()
                        .push(&program.atoms[a]);
                }
            }
        }
    }
    let mut cycles = Vec::new();
    let mut steps = 0;
    'roots: for root in graph.keys() {
        let mut path = vec![*root];
        let mut next = vec![0];
        while let Some(cursor) = next.last_mut() {
            if steps == 4096 || cycles.len() == 3 {
                truncated = true;
                break 'roots;
            }
            steps += 1;
            let atom = *path.last().unwrap();
            let neighbors = graph.get(atom).map(Vec::as_slice).unwrap_or(&[]);
            if let Some(&to) = neighbors.get(*cursor) {
                *cursor += 1;
                if to == *root {
                    let mut cycle: Vec<_> = path.iter().map(|a| (*a).clone()).collect();
                    cycle.push(to.clone());
                    cycles.push(cycle);
                } else if path.len() < 12 && !path.contains(&to) {
                    path.push(to);
                    next.push(0);
                } else {
                    truncated = true;
                }
            } else {
                path.pop();
                next.pop();
            }
        }
    }
    RecursiveComponentShape {
        component: component.id.index + 1,
        atoms: component.atoms.len(),
        rules: program.component_rules[component.id.index].len(),
        relations,
        omitted_relations,
        cycles,
        cycle_search_truncated: truncated,
    }
}
