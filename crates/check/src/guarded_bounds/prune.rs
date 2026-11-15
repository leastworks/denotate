//! Monotone deadness, not a second symbolic bounds computation. All marks hold
//! under D in every supported interpretation, even with the reading rule free
//! to fire anywhere inside its settled guard. Unseeded cycles stay possible.
use super::*;
use biodivine_lib_bdd::op_function::{and_not, or};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeadReason {
    SettledCondition,
    Positive(GroundAtom),
    Negative {
        atom: GroundAtom,
        exact_producers: Vec<GroundRuleId>,
    },
}

#[derive(Debug, Clone)]
pub struct Pruning<S = Arc<ProducerSummary>> {
    pub reasons: BTreeMap<GroundRuleId, DeadReason>,
    /// Transitive proof support omitted from the executable cone. Never fed to
    /// bounds or the candidate probe as additional executable producers.
    pub sources: Vec<S>,
}
impl<S> Default for Pruning<S> {
    fn default() -> Self {
        Self {
            reasons: BTreeMap::new(),
            sources: Vec::new(),
        }
    }
}
impl<S> Pruning<S> {
    pub(super) fn temporary_nodes(&self) -> usize {
        self.sources.len()
            + self
                .reasons
                .values()
                .map(|r| {
                    3 + match r {
                        DeadReason::Negative {
                            exact_producers, ..
                        } => exact_producers.len(),
                        _ => 0,
                    }
                })
                .sum::<usize>()
    }
}
impl Pruning<&ProducerSummary> {
    pub(super) fn owned(&self, budget: &mut Budget<'_>) -> Result<Pruning> {
        budget.charge(self.temporary_nodes(), "guarded pruning certificate")?;
        let mut sources = Vec::new();
        for source in &self.sources {
            budget.charge(
                1 + source.rule.body.len() + source.settled.len(),
                "guarded pruning certificate",
            )?;
            sources.push(Arc::new((*source).clone()));
        }
        Ok(Pruning {
            reasons: self.reasons.clone(),
            sources,
        })
    }
}

// Optional indexing is bounded separately from the ordinary cone. This limits
// both allocation and repeated scans; the global work charge is never refunded.
const MAX_ITEMS: usize = 65_536;

// Optional allocation failure is reported by the guarded attempt's fallback
// field, not as a stopped checking phase or an exhausted semantic query receipt.
fn reserve(total: usize, old: usize, new: usize, budget: &mut Budget<'_>) -> Result<usize> {
    let next = total.checked_sub(old).and_then(|n| n.checked_add(new));
    if next.is_none_or(|n| n > budget.limits.max_condition_nodes) {
        return Err(CheckError::limit(
            "guarded pruning",
            "condition nodes",
            budget.limits.max_condition_nodes,
            next,
        ));
    }
    crate::symbolic::retain(total, old, new, budget)
}

#[cfg(test)]
mod tests;

pub(super) fn prepare<'a>(
    cone: Arc<BorrowedCone<'a>>,
    root: &GroundAtom,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
    stats: &mut Preparation,
) -> Result<Arc<BorrowedCone<'a>>> {
    stats.before_atoms = Some(cone.atoms.len());
    stats.before_producers = Some(cone.producers.len());
    let mut scratch = *retained;
    match run(&cone, root, ctx, &mut scratch, budget, MAX_ITEMS) {
        Ok(pruned) => {
            budget.charge(pruned.producers.len(), "guarded pruning counts")?;
            // Stage all evidence before replacing the old cone. Failed staging
            // leaves its charges, contents, and ordinary bounds path intact.
            let next = retained.saturating_sub(cone.temporary_nodes());
            match reserve(next, 0, pruned.temporary_nodes(), budget) {
                Ok(next) => {
                    *retained = next;
                    stats.pruning = Some("complete");
                    stats.visited_atoms = pruned.atoms.len();
                    stats.visited_producers = pruned.producers.len();
                    stats.live_producers = pruned.producers.iter().filter(|p| p.live).count();
                    stats.live_atoms = pruned
                        .producers
                        .iter()
                        .filter(|p| p.live)
                        .map(|p| &p.rule.head.atom)
                        .collect::<BTreeSet<_>>()
                        .len();
                    return Ok(Arc::new(pruned));
                }
                Err(e) => return fallback(e, cone, stats),
            }
        }
        Err(e) => fallback(e, cone, stats),
    }
}

fn fallback<'a>(
    error: CheckError,
    cone: Arc<BorrowedCone<'a>>,
    stats: &mut Preparation,
) -> Result<Arc<BorrowedCone<'a>>> {
    match error {
        CheckError::LimitExceeded {
            resource: resource @ ("condition nodes" | "BDD nodes" | "BDD tasks" | "pruning items"),
            ..
        } => {
            stats.pruning = Some(resource);
            Ok(cone)
        }
        // Work, deadlines, cancellation and unexpected errors are never hidden.
        e => Err(e),
    }
}

fn run<'a>(
    cone: &BorrowedCone<'a>,
    root: &GroundAtom,
    ctx: &ConditionContext,
    scratch: &mut usize,
    budget: &mut Budget<'_>,
    max_items: usize,
) -> Result<BorrowedCone<'a>> {
    let mut items = cone.atoms.len() + cone.producers.len();
    for p in &cone.producers {
        budget.tick("guarded pruning size")?;
        items = items.saturating_add(p.rule.body.len());
        if items > max_items {
            return Err(CheckError::limit(
                "guarded pruning",
                "pruning items",
                max_items,
                Some(items),
            ));
        }
    }
    // Conservative slots for the indices, worklists, reasons, rebuilt vectors
    // and proof closure, coexisting with the old borrowed cone. Guarantees below
    // are charged separately and released as soon as that atom is tested.
    *scratch = reserve(*scratch, 0, items * 16, budget)?;
    let mut by_head = BTreeMap::<&GroundAtom, Vec<usize>>::new();
    let mut readers = BTreeMap::<&GroundAtom, Vec<usize>>::new();
    let mut reasons = BTreeMap::<usize, DeadReason>::new();
    let mut negative = BTreeMap::<&GroundAtom, Vec<usize>>::new();
    let mut remaining: BTreeMap<_, usize> = cone.atoms.iter().map(|a| (a, 0)).collect();
    for (i, p) in cone.producers.iter().enumerate() {
        budget.charge(1 + p.rule.body.len(), "guarded pruning index")?;
        by_head.entry(&p.rule.head.atom).or_default().push(i);
        if !p.live {
            reasons.insert(i, DeadReason::SettledCondition);
            continue;
        }
        *remaining.get_mut(&p.rule.head.atom).expect("cone head") += 1;
        if Some(p.rule.id) == cone.relaxed_rule {
            continue;
        }
        for literal in &p.rule.body {
            // Outside-component premises have already contributed to the
            // settled condition, or remain unknown. Never invent their meaning.
            if !remaining.contains_key(&literal.term.atom) {
                continue;
            }
            if literal.polarity == Polarity::Negative {
                negative.entry(&literal.term.atom).or_default().push(i);
            } else {
                readers.entry(&literal.term.atom).or_default().push(i);
            }
        }
    }
    // Each exact guarantee is built once per atom for this D and released after
    // its negative readers. No candidate-specific result escapes this pass.
    for (atom, users) in negative {
        budget.charge(users.len(), "guarded pruning negative readers")?;
        if users.iter().all(|i| reasons.contains_key(i)) {
            continue;
        }
        let mut lower = ctx.false_condition();
        let mut exact = Vec::new();
        for i in by_head.get(atom).into_iter().flatten() {
            let p = &cone.producers[*i];
            budget.tick("guarded pruning guarantee")?;
            if !p.live || !p.exact || Some(p.rule.id) == cone.relaxed_rule {
                continue;
            }
            let scoped = ctx.apply(&cone.domain, &p.condition, and, budget)?;
            let next = ctx.apply(&lower, &scoped, or, budget)?;
            *scratch = reserve(
                *scratch,
                if exact.is_empty() {
                    0
                } else {
                    lower.node_count()
                },
                next.node_count(),
                budget,
            )?;
            lower = next;
            exact.push(p.rule.id);
        }
        let guaranteed =
            !exact.is_empty() && ctx.apply(&cone.domain, &lower, and_not, budget)?.is_false();
        if !exact.is_empty() {
            *scratch -= lower.node_count();
        }
        if guaranteed {
            for i in users {
                budget.charge(1 + exact.len(), "guarded pruning negative")?;
                // Negative reasons own their exact producer IDs. Charge these
                // variable-size vectors in addition to the fixed staging slots.
                if reasons.contains_key(&i) {
                    continue;
                }
                *scratch = reserve(*scratch, 0, 2 * exact.len(), budget)?;
                reasons.insert(
                    i,
                    DeadReason::Negative {
                        atom: atom.clone(),
                        exact_producers: exact.clone(),
                    },
                );
                *remaining
                    .get_mut(&cone.producers[i].rule.head.atom)
                    .unwrap() -= 1;
            }
        }
    }
    let mut pending: BTreeSet<_> = remaining
        .iter()
        .filter_map(|(a, n)| (*n == 0).then_some(*a))
        .collect();
    while let Some(atom) = pending.pop_first() {
        budget.tick("guarded pruning dead atom")?;
        for &i in readers.get(atom).into_iter().flatten() {
            budget.tick("guarded pruning positive")?;
            if reasons.contains_key(&i) {
                continue;
            }
            reasons.insert(i, DeadReason::Positive(atom.clone()));
            let head = &cone.producers[i].rule.head.atom;
            let count = remaining.get_mut(head).unwrap();
            *count -= 1;
            if *count == 0 {
                pending.insert(head);
            }
        }
    }

    // Rebuild only reachability; keep dead producers at reachable heads. Their
    // source chains are proof evidence, not edges for the bounds computation.
    let mut atoms = BTreeSet::new();
    let mut selected = BTreeSet::new();
    let mut pending = BTreeSet::from([root]);
    while let Some(atom) = pending.pop_first() {
        budget.tick("guarded pruning cone")?;
        if !atoms.insert(atom.clone()) {
            continue;
        }
        for &i in by_head.get(atom).into_iter().flatten() {
            budget.tick("guarded pruning cone producer")?;
            selected.insert(i);
            if reasons.contains_key(&i) || Some(cone.producers[i].rule.id) == cone.relaxed_rule {
                continue;
            }
            for literal in &cone.producers[i].rule.body {
                budget.tick("guarded pruning cone premise")?;
                if remaining.contains_key(&literal.term.atom) && !atoms.contains(&literal.term.atom)
                {
                    pending.insert(&literal.term.atom);
                }
            }
        }
    }
    let mut proof = Pruning::default();
    let mut support = BTreeSet::new();
    let mut pending = selected.clone();
    let by_id: BTreeMap<_, _> = cone
        .producers
        .iter()
        .enumerate()
        .map(|(i, p)| (p.rule.id, i))
        .collect();
    while let Some(i) = pending.pop_first() {
        budget.tick("guarded pruning support")?;
        if !support.insert(i) {
            continue;
        }
        if let Some(reason) = reasons.get(&i) {
            match reason {
                DeadReason::Positive(atom) => {
                    for &j in by_head.get(atom).into_iter().flatten() {
                        budget.tick("guarded pruning positive support")?;
                        if !support.contains(&j) {
                            pending.insert(j);
                        }
                    }
                }
                DeadReason::Negative {
                    exact_producers, ..
                } => {
                    budget.charge(exact_producers.len(), "guarded pruning negative support")?;
                    for id in exact_producers {
                        let j = by_id[id];
                        if !support.contains(&j) {
                            pending.insert(j);
                        }
                    }
                }
                DeadReason::SettledCondition => {}
            }
            proof
                .reasons
                .insert(cone.producers[i].rule.id, reason.clone());
        }
        if !selected.contains(&i) {
            proof.sources.push(cone.producers[i].summary);
        }
    }
    Ok(GuardedCone {
        component: cone.component,
        snapshot: cone.snapshot,
        domain: cone.domain.clone(),
        relaxed_rule: cone
            .relaxed_rule
            .filter(|id| atoms.contains(&cone.producers[by_id[id]].rule.head.atom)),
        atoms: atoms.into_iter().collect(),
        producers: selected
            .into_iter()
            .map(|i| GuardedProducer {
                summary: cone.producers[i].summary,
                live: !reasons.contains_key(&i),
            })
            .collect(),
        pruning: proof,
    })
}
