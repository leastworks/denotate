//! Complete summary sets and their final symbolic readers, within one snapshot.
use crate::{
    admission_scope::AdmissionScope,
    admission_skips::Attempts,
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::and;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct SummaryPlan {
    /// Complete producer groups; every consumer is an attempted component.
    groups: BTreeMap<GroundAtom, Vec<GroundRuleId>>,
    users: BTreeMap<GroundAtom, BTreeSet<ComponentId>>,
    pub keep: BTreeSet<GroundAtom>,
    pub nodes: usize,
}
impl SummaryPlan {
    pub fn build(
        p: &GroundProgram,
        scope: &AdmissionScope,
        attempts: &Attempts,
        budget: &mut Budget<'_>,
    ) -> Result<Self> {
        let components = scope.ordered_targets(p, budget)?;
        let mut users = BTreeMap::<_, BTreeSet<_>>::new();
        for (component, _) in &components {
            if attempts.summary_skipped(&p.components[component.index].atoms[0]) {
                continue;
            }
            // All same-head producers are needed for coverage, and all component
            // producers for bounds/certificates. One-hop body providers supply
            // implied guards (positive upper covers and negative exact covers).
            for index in &p.component_rules[component.index] {
                let rule = &p.rules[*index];
                budget.tick("summary requirements")?;
                users
                    .entry(rule.head.atom.clone())
                    .or_default()
                    .insert(*component);
                if p.components[component.index].cycle.is_none() {
                    continue;
                }
                for literal in &rule.body {
                    budget.tick("summary supporting producers")?;
                    users
                        .entry(literal.term.atom.clone())
                        .or_default()
                        .insert(*component);
                }
            }
        }
        let mut groups = BTreeMap::<_, Vec<_>>::new();
        let mut keep = BTreeSet::new();
        for rule in p.rules.iter().filter(|r| scope.cone.rules.contains(&r.id)) {
            budget.tick("summary producer index")?;
            if users.contains_key(&rule.head.atom) {
                groups
                    .entry(rule.head.atom.clone())
                    .or_default()
                    .push(rule.id);
                for literal in rule.dependency_literals() {
                    budget.tick("summary symbolic frontier")?;
                    keep.insert(literal.term.atom);
                }
            }
        }
        let nodes = keep.len()
            + groups.values().map(|v| 1 + v.len()).sum::<usize>()
            + users.values().map(|v| 1 + v.len()).sum::<usize>();
        crate::symbolic::retain(0, 0, nodes, budget)?;
        Ok(Self {
            groups,
            users,
            keep,
            nodes,
        })
    }

    pub fn build_summaries(
        &self,
        p: &GroundProgram,
        meaning: &SymbolicMeaning<'_>,
        retained: &mut usize,
        attempts: &mut Attempts,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<BTreeMap<GroundRuleId, ProducerSummary>> {
        let mut summaries = BTreeMap::new();
        let mut blocked = BTreeSet::new();
        let mut position = 0;
        for (head, rules) in &self.groups {
            let users = &self.users[head];
            if users.iter().all(|c| blocked.contains(c)) {
                continue;
            }
            let baseline = *retained;
            // Partial producer groups are private to this closure. A failed
            // group can never masquerade as complete positive upper coverage.
            let result = (|| {
                let mut group = Vec::new();
                for id in rules {
                    position += 1;
                    let rule = p.rule(*id).unwrap();
                    progress.rule(p, "summaries", *id, position);
                    group.push(summary(rule, meaning, retained, budget)?);
                }
                Ok::<_, CheckError>(group)
            })();
            match result {
                Ok(group) => summaries.extend(group.into_iter().map(|s| (s.rule.id, s))),
                Err(error) if crate::symbolic::local_exhaustion(&error) => {
                    *retained = baseline;
                    let reason = Inconclusive::from_error(error.clone())?;
                    budget.record_failure(&error);
                    for component in users {
                        if blocked.insert(*component) {
                            let atom = &p.components[component.index].atoms[0];
                            attempts.summary_failed(atom, p, reason, progress);
                        }
                    }
                    // Groups no surviving attempt reads are no longer needed.
                    // Their complete values are released, never partly reused.
                    let mut remove = Vec::new();
                    for (id, s) in &summaries {
                        budget.tick("summary failure readers")?;
                        if self.users[&s.rule.head.atom]
                            .iter()
                            .all(|c| blocked.contains(c))
                        {
                            *retained -= s.nodes();
                            remove.push(*id);
                        }
                    }
                    for id in remove {
                        summaries.remove(&id);
                    }
                }
                Err(error) => return Err(error),
            }
        }
        Ok(summaries)
    }
}

pub(crate) fn report(
    p: &GroundProgram,
    meaning: Option<&SymbolicMeaning<'_>>,
    summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
    attempts: &Attempts,
    frontier_metadata_nodes: usize,
) -> AdmissionStorage {
    let pool = |accounted_nodes, retained_bdd| AdmissionConditionPool {
        accounted_nodes,
        retained_bdd,
    };
    AdmissionStorage {
        symbolic: pool(
            meaning.map_or(0, |m| m.metrics().retained_condition_nodes),
            crate::boolean::condition_storage(
                meaning
                    .into_iter()
                    .flat_map(|m| m.conditions.values().chain(m.context.stored_conditions())),
            ),
        ),
        summaries: pool(
            summaries.values().map(ProducerSummary::nodes).sum(),
            crate::boolean::condition_storage(
                summaries
                    .values()
                    .flat_map(ProducerSummary::profile_conditions),
            ),
        ),
        committed_proofs: pool(
            p.rewrite_storage_nodes(),
            crate::boolean::condition_storage(crate::rewrite::profile_proof_conditions(
                p.rewrite_proofs(),
            )),
        ),
        optional_caches: pool(
            attempts.nodes(),
            crate::boolean::condition_storage(
                attempts
                    .prepared
                    .values()
                    .flat_map(|p| p.profile_conditions()),
            ),
        ),
        frontier_metadata_nodes,
        kept_conditions: meaning.map_or(0, |m| m.conditions.len()),
        released_conditions: meaning.map_or(0, |m| m.released.len()),
        unknown_atoms: meaning.map_or(0, |m| m.unknown.len()),
    }
}

fn summary(
    rule: &GroundRule,
    meaning: &SymbolicMeaning<'_>,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<ProducerSummary> {
    budget.tick("rewrite summaries")?;
    let ctx = meaning.context();
    let mut condition = ctx.true_condition();
    let mut settled = Vec::new();
    let mut exact = true;
    for literal in &rule.body {
        budget.tick("rewrite summaries")?;
        match meaning.fact(&literal.term.atom)? {
            SymbolicFact::Blocked(_) | SymbolicFact::Inconclusive(_) => exact = false,
            SymbolicFact::Settled(mut value) => {
                if literal.polarity == Polarity::Negative {
                    value = ctx.complement(&value, budget)?;
                }
                condition = ctx.apply(&condition, &value, and, budget)?;
                *retained = crate::symbolic::retain(*retained, 0, value.node_count(), budget)?;
                settled.push(SettledPremise {
                    literal: literal.clone(),
                    condition: value,
                });
            }
        }
    }
    for replacement in &rule.replacements {
        match meaning.partial_expression(&replacement.expression, budget)? {
            crate::symbolic::PartialCondition::Known(value) => {
                condition = ctx.apply(&condition, &value, and, budget)?
            }
            crate::symbolic::PartialCondition::Unknown(_) => exact = false,
        }
    }
    *retained = crate::symbolic::retain(*retained, 0, condition.node_count(), budget)?;
    Ok(ProducerSummary {
        rule: rule.clone(),
        settled,
        condition,
        exact,
    })
}
