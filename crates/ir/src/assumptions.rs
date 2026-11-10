//! Assumptions are evaluated independently of the context they constrain.
use crate::*;
use std::collections::{BTreeMap, BTreeSet};

/// Preliminary classification. Ground validation belongs to the checker, which
/// has the program's resolved domains, input eligibility and resource limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssumptionCone {
    RelationStratified,
    NeedsGrounding,
}

impl Corpus {
    pub fn validate_assumptions(
        &self,
    ) -> Result<BTreeMap<RelationId, AssumptionCone>, ConstructionError> {
        self.validate_assumptions_with(|| Ok(()))
    }
    /// Call after constructing the rules. A relation-level negative cycle defers
    /// validation to the checker; it is not a declaration error or an acceptance.
    pub fn validate_assumptions_with<E: From<ConstructionError>>(
        &self,
        tick: impl FnMut() -> Result<(), E>,
    ) -> Result<BTreeMap<RelationId, AssumptionCone>, E> {
        self.validate_assumption_relations_with(
            self.assumptions().map(|a| a.restriction.relation()),
            tick,
        )
    }
    /// Also validates explicitly constructed request restrictions without requiring
    /// a named verification. Callers use the same relation-level rule graph.
    pub fn validate_assumption_relations_with<E: From<ConstructionError>>(
        &self,
        roots: impl IntoIterator<Item = RelationId>,
        mut tick: impl FnMut() -> Result<(), E>,
    ) -> Result<BTreeMap<RelationId, AssumptionCone>, E> {
        let mut edges = BTreeMap::<RelationId, Vec<(RelationId, bool)>>::new();
        for rule in self.rules() {
            tick()?;
            for literal in &rule.body {
                tick()?;
                edges.entry(rule.head.relation()).or_default().push((
                    literal.atom().relation(),
                    matches!(literal, Literal::Negative(_)),
                ));
            }
        }
        let mut unique_roots = BTreeSet::new();
        for relation in roots {
            tick()?;
            unique_roots.insert(relation);
        }
        let mut result = BTreeMap::new();
        'roots: for relation in unique_roots {
            self.relation(relation)
                .ok_or(ConstructionError::UnknownRelation(relation))?;
            let mut cone = BTreeSet::new();
            let mut pending = vec![relation];
            while let Some(id) = pending.pop() {
                tick()?;
                if !cone.insert(id) {
                    continue;
                }
                for (dep, _) in edges.get(&id).into_iter().flatten() {
                    tick()?;
                    pending.push(*dep);
                }
            }
            for source in &cone {
                for (target, negative) in edges.get(source).into_iter().flatten() {
                    tick()?;
                    if !negative {
                        continue;
                    }
                    let mut seen = BTreeSet::new();
                    let mut pending = vec![*target];
                    while let Some(id) = pending.pop() {
                        tick()?;
                        if id == *source {
                            result.insert(relation, AssumptionCone::NeedsGrounding);
                            continue 'roots;
                        }
                        if !seen.insert(id) {
                            continue;
                        }
                        for (dep, _) in edges.get(&id).into_iter().flatten() {
                            tick()?;
                            pending.push(*dep);
                        }
                    }
                }
            }
            result.insert(relation, AssumptionCone::RelationStratified);
        }
        Ok(result)
    }
    /// Directional warning: assuming a conclusion (or something computed from it).
    /// Depending on an assumed premise is ordinary assume-guarantee reasoning.
    pub fn assumption_conclusions(
        &self,
        verification: VerificationId,
    ) -> Vec<(AssumptionId, ObligationId)> {
        let Some(v) = self.verification(verification) else {
            return vec![];
        };
        let mut edges = BTreeMap::<RelationId, BTreeSet<RelationId>>::new();
        for r in self.rules() {
            edges
                .entry(r.head.relation())
                .or_default()
                .extend(r.body.iter().map(|l| l.atom().relation()));
        }
        let mut pairs = Vec::new();
        for a in &v.assumptions {
            let mut cone = BTreeSet::new();
            let mut pending = vec![self.assumption(*a).unwrap().restriction.relation()];
            while let Some(r) = pending.pop() {
                if cone.insert(r) {
                    pending.extend(edges.get(&r).into_iter().flatten().copied());
                }
            }
            for o in &v.obligations {
                if cone.contains(&self.obligation(*o).unwrap().requirement.relation()) {
                    pairs.push((*a, *o));
                }
            }
        }
        pairs
    }
}
