//! Structural validation shared by construction clients, text loading and checking.
use crate::*;
use std::collections::{BTreeMap, BTreeSet};

impl Corpus {
    /// Attach a provider after both signatures have been declared. Validate the
    /// completed rule graph with validate_input_domains (checking also does this).
    pub fn restrict_input(
        &mut self,
        input: RelationId,
        provider: RelationId,
    ) -> Result<(), ConstructionError> {
        self.check_input_domain_signature(input, provider)?;
        // Relation storage is private to model; use the internal setter.
        self.set_input_domain(input, provider)
    }

    pub(crate) fn check_input_domain_signature(
        &self,
        input: RelationId,
        provider: RelationId,
    ) -> Result<(), ConstructionError> {
        let r = self
            .relation(input)
            .ok_or(ConstructionError::UnknownRelation(input))?;
        let d = self
            .relation(provider)
            .ok_or(ConstructionError::UnknownRelation(provider))?;
        let reason = if r.role != RelationRole::Input {
            Some("only input relations can have a domain provider")
        } else if d.role != RelationRole::Derived {
            Some("domain provider must be derived, not an input")
        } else if !r
            .parameters
            .iter()
            .map(|p| p.sort)
            .eq(d.parameters.iter().map(|p| p.sort))
        {
            Some("domain provider must have the same arity and positional sorts")
        } else {
            None
        };
        if let Some(reason) = reason {
            return Err(ConstructionError::InvalidInputDomain {
                input,
                provider,
                reason,
            });
        }
        Ok(())
    }

    pub fn validate_input_domains(&self) -> Result<BTreeSet<RelationId>, ConstructionError> {
        self.input_domain_cone_with(|| Ok(()))
    }

    /// Bounded callers supply a work/cancellation checkpoint. Returns the entire
    /// input-free dependency cone, without evaluating any rules.
    pub fn input_domain_cone_with<E: From<ConstructionError>>(
        &self,
        mut tick: impl FnMut() -> Result<(), E>,
    ) -> Result<BTreeSet<RelationId>, E> {
        let mut edges: BTreeMap<RelationId, Vec<(RelationId, bool)>> = BTreeMap::new();
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
        let mut all = BTreeSet::new();
        for r in self.relations() {
            tick()?;
            let Some(provider) = r.input_domain else {
                continue;
            };
            self.check_input_domain_signature(r.id, provider)?;
            let invalid = |reason| ConstructionError::InvalidInputDomain {
                input: r.id,
                provider,
                reason,
            };
            let mut cone = BTreeSet::new();
            let mut pending = vec![provider];
            while let Some(id) = pending.pop() {
                tick()?;
                if !cone.insert(id) {
                    continue;
                }
                if self.relation(id).unwrap().role == RelationRole::Input {
                    return Err(invalid("domain provider depends on an input").into());
                }
                for (dependency, _) in edges.get(&id).into_iter().flatten() {
                    tick()?;
                    pending.push(*dependency);
                }
            }
            // A negative edge is cyclic exactly when its target can reach its
            // source through the dependency graph. Positive recursion is allowed.
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
                            return Err(
                                invalid("domain provider has a cycle through negation").into()
                            );
                        }
                        if !seen.insert(id) {
                            continue;
                        }
                        for (dependency, _) in edges.get(&id).into_iter().flatten() {
                            tick()?;
                            pending.push(*dependency);
                        }
                    }
                }
            }
            all.extend(cone);
        }
        Ok(all)
    }
}
