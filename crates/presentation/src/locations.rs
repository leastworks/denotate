use crate::*;
use denotate_check::{EvidenceStep, GroundAtom, GroundEvidence, PremiseEvidence, VerifiedOutcome};
use denotate_ir::*;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RelatedLocation {
    pub span: SourceSpan,
    pub label: String,
}
impl RelatedLocation {
    pub fn new(span: SourceSpan, label: impl Into<String>) -> Self {
        Self {
            span,
            label: label.into(),
        }
    }
}
#[derive(Debug)]
pub struct Diagnostic {
    pub program: String,
    pub verification: Option<VerificationKey>,
    pub identity: Identity,
    pub kind: Kind,
    pub message: String,
    pub notes: Vec<String>,
    pub primary: SourceSpan,
    pub related: Vec<RelatedLocation>,
    pub fallback: bool,
    pub evidence: Value,
}
impl Diagnostic {
    pub fn data(&self, keys: &SemanticKeys) -> Result<Value> {
        Ok(
            json!({"program":self.program,"finding":self.identity.data_in(keys, self.verification.as_ref())?,"kind":self.kind.code(),"fallback":self.fallback,"evidence":self.evidence}),
        )
    }
}
/// Current and embedded provenance are separate inputs even if their snapshots
/// have the same view label. Only current text can supply a primary location.
pub struct Placement<'a> {
    pub program: &'a str,
    pub verification: Option<&'a VerificationKey>,
    pub user_files: &'a BTreeSet<String>,
    pub sources: &'a Sources,
    pub current: &'a Provenance,
    pub upstream: &'a Provenance,
}
impl Placement<'_> {
    pub fn place(
        &self,
        identity: &Identity,
        kind: Kind,
        message: &str,
        notes: &[String],
        contributions: &[Contribution],
    ) -> Result<Vec<Diagnostic>> {
        self.place_with_coverage_constants(identity, kind, message, notes, contributions, false)
    }

    fn place_with_coverage_constants(
        &self,
        identity: &Identity,
        kind: Kind,
        message: &str,
        notes: &[String],
        contributions: &[Contribution],
        coverage_constants: bool,
    ) -> Result<Vec<Diagnostic>> {
        let (current, related) = self.contribution_locations(contributions)?;
        let own = current
            .iter()
            .filter(|(s, _)| {
                self.sources
                    .snapshot(s.snapshot())
                    .is_ok_and(|s| self.user_files.contains(&s.uri))
            })
            .copied()
            .collect::<Vec<_>>();
        let fallback = own.is_empty();
        let candidates = if fallback { &current } else { &own };
        // Prefer participating producing rules. Declarations are valid primary
        // sites when a consumer only contributes constants or the obligation.
        let rank = |r| match r {
            Role::Producer => 0,
            Role::Contributor => 1,
            Role::Declaration => 2,
            Role::Obligation => 3,
            Role::RelatedOnly
            | Role::DirectRewriteProof
            | Role::Condition
            | Role::EnclosingScope
            | Role::BlockingCycle
            | Role::AdmissionAttempt => {
                unreachable!("related-only origins cannot be primary")
            }
        };
        let best = candidates.iter().map(|(_, r)| rank(*r)).min();
        let mut out = Vec::new();
        for (primary, role) in candidates {
            if Some(rank(*role)) != best {
                continue;
            }
            out.push(Diagnostic {
                program: self.program.into(),
                verification: self.verification.cloned(),
                identity: identity.clone(),
                kind,
                message: if fallback {
                    format!("in {}: {message}", self.program)
                } else {
                    message.into()
                },
                notes: notes.to_vec(),
                primary: *primary,
                related: related
                    .iter()
                    .filter(|r| r.span != *primary || r.label == "upstream source origin")
                    .cloned()
                    .collect(),
                fallback,
                evidence: Value::Null,
            });
            if matches!(identity, Identity::Notice(_) | Identity::Assumption(_))
                || (matches!(identity, Identity::Coverage(_)) && !coverage_constants)
                || matches!(
                    kind,
                    Kind::Inconclusive | Kind::UnsupportedGroup | Kind::UnsupportedRegion
                )
            {
                break;
            }
        }
        // Unlocated builder IR still remains in the root's finding inventory.
        Ok(out)
    }
    pub(crate) fn contribution_locations(
        &self,
        contributions: &[Contribution],
    ) -> Result<(Vec<(SourceSpan, Role)>, Vec<RelatedLocation>)> {
        let mut current = Vec::new();
        let mut related = Vec::new();
        let mut occurrences = BTreeSet::new();
        let mut related_seen = BTreeSet::new();
        let mut current_indices = BTreeMap::<SourceSpan, usize>::new();
        for contribution in contributions {
            if !occurrences.insert((contribution.occurrence, contribution.role)) {
                continue;
            }
            for origin in self.current.origins(contribution.occurrence) {
                self.sources.text(origin.span)?;
                if !matches!(
                    contribution.role,
                    Role::RelatedOnly
                        | Role::DirectRewriteProof
                        | Role::Condition
                        | Role::EnclosingScope
                        | Role::BlockingCycle
                        | Role::AdmissionAttempt
                ) {
                    if let Some(index) = current_indices.get(&origin.span) {
                        let (_, role): &mut (SourceSpan, Role) = &mut current[*index];
                        *role = std::cmp::min(*role, contribution.role);
                    } else {
                        current_indices.insert(origin.span, current.len());
                        current.push((origin.span, contribution.role));
                    }
                }
                let location = RelatedLocation::new(origin.span, contribution.role.label());
                if related_seen.insert(location.clone()) {
                    related.push(location);
                }
            }
            for origin in self.upstream.origins(contribution.occurrence) {
                self.sources.text(origin.span)?;
                let location = RelatedLocation::new(origin.span, "upstream source origin");
                if related_seen.insert(location.clone()) {
                    related.push(location);
                }
            }
        }
        Ok((current, related))
    }

    fn has_own_location(&self, occurrence: OccurrenceId) -> Result<bool> {
        for origin in self.current.origins(occurrence) {
            self.sources.text(origin.span)?;
            if self
                .user_files
                .contains(&self.sources.snapshot(origin.span.snapshot())?.uri)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn library_obligation(&self, contributions: &[Contribution]) -> Result<bool> {
        let mut located = false;
        for c in contributions.iter().filter(|c| c.role == Role::Obligation) {
            if self.has_own_location(c.occurrence)? {
                return Ok(false);
            }
            located |= !self.current.origins(c.occurrence).is_empty();
        }
        // Unlocated declarations have unknown ownership; preserve their placement.
        Ok(located)
    }

    /// Walk retained positive support, never declarations or negative premises.
    /// Each root has its own fallback; shared support is visited once per root.
    fn frontier<'a>(
        &self,
        finding: &Finding<'_>,
        notes: &[String],
        contributions: &[Contribution],
        roots: impl IntoIterator<Item = &'a GroundAtom>,
        steps: &BTreeMap<GroundAtom, EvidenceStep>,
    ) -> Result<Vec<Diagnostic>> {
        let (_, related) = self.contribution_locations(contributions)?;
        let mut out = Vec::new();
        for root in roots {
            let mut pending = vec![root];
            let mut visited = BTreeSet::new();
            let mut frontier = Vec::new();
            let mut fallback = contributions
                .iter()
                .filter(|c| c.role == Role::Obligation)
                .copied()
                .collect::<Vec<_>>();
            while let Some(atom) = pending.pop() {
                if !visited.insert(atom) {
                    continue;
                }
                let step = steps
                    .get(atom)
                    .ok_or(Error::InvalidFinding("missing retained proof step"))?;
                step_contributions(atom, step, &mut fallback);
                if let GroundEvidence::Derived { rule, premises } = &step.evidence {
                    if self.has_own_location(rule.source.into())? {
                        frontier.push(Contribution {
                            occurrence: rule.source.into(),
                            role: Role::Producer,
                        });
                        continue;
                    }
                    for premise in premises {
                        if let PremiseEvidence::Positive { fact, .. } = premise {
                            pending.push(fact);
                        }
                    }
                }
            }
            let candidates = if frontier.is_empty() {
                &fallback
            } else {
                &frontier
            };
            for mut diagnostic in self.place(
                &finding.identity,
                finding.kind,
                &finding.message,
                notes,
                candidates,
            )? {
                // Narrow primaries only: keep original roles/labels and every
                // participating occurrence, including support below the frontier.
                diagnostic.related = related
                    .iter()
                    .filter(|r| r.span != diagnostic.primary || r.label == "upstream source origin")
                    .cloned()
                    .collect();
                merge_diagnostic(&mut out, diagnostic);
            }
        }
        Ok(out)
    }
    pub fn finding(&self, finding: &Finding<'_>) -> Result<Vec<Diagnostic>> {
        let narrow = self.library_obligation(&finding.contributions)?;
        if narrow {
            if let Evidence::Group(group) = &finding.evidence {
                if let VerifiedOutcome::Counterexample(example) = &group.outcome {
                    return self.frontier(
                        finding,
                        &finding.notes,
                        &finding.contributions,
                        &example.tuples,
                        &example.evidence,
                    );
                }
            }
        }
        if !finding.placement_groups.is_empty() {
            let mut out: Vec<Diagnostic> = Vec::new();
            for group in &finding.placement_groups {
                let mut notes = finding.notes.clone();
                notes.extend(group.notes.iter().cloned());
                let mut coverage_constants = false;
                let mut contributions = group.contributions.clone();
                if matches!(finding.identity, Identity::Coverage(_)) {
                    // Only current, locatable declarations in this program can
                    // replace the obligation. Upstream-only origins do not qualify.
                    for contribution in &contributions {
                        if contribution.role == Role::Declaration {
                            for origin in self.current.origins(contribution.occurrence) {
                                self.sources.text(origin.span)?;
                                let source = self.sources.snapshot(origin.span.snapshot())?;
                                coverage_constants |= self.user_files.contains(&source.uri);
                            }
                        }
                    }
                    if !coverage_constants {
                        // Keep the original obligation placement for this example;
                        // library constants must not become fallback primaries.
                        contributions.retain(|c| c.role == Role::Obligation);
                    }
                }
                let placed = if let Some(derivation) = group.derivation.as_ref().filter(|_| narrow)
                {
                    self.frontier(
                        finding,
                        &notes,
                        &contributions,
                        [derivation.tuple],
                        derivation.steps,
                    )?
                } else {
                    self.place_with_coverage_constants(
                        &finding.identity,
                        finding.kind,
                        &finding.message,
                        &notes,
                        &contributions,
                        coverage_constants,
                    )?
                };
                for diagnostic in placed {
                    merge_diagnostic(&mut out, diagnostic);
                }
            }
            return Ok(out);
        }
        self.place(
            &finding.identity,
            finding.kind,
            &finding.message,
            &finding.notes,
            &finding.contributions,
        )
    }
}

fn merge_diagnostic(out: &mut Vec<Diagnostic>, diagnostic: Diagnostic) {
    if let Some(existing) = out.iter_mut().find(|d| d.primary == diagnostic.primary) {
        for note in diagnostic.notes {
            if !existing.notes.contains(&note) {
                existing.notes.push(note);
            }
        }
        for related in diagnostic.related {
            if !existing.related.contains(&related) {
                existing.related.push(related);
            }
        }
    } else {
        out.push(diagnostic);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shared_spans_keep_the_strongest_role_and_supporting_proofs_stay_related() {
        let mut corpus = Corpus::new();
        let sort = corpus.declare_sort("S").unwrap();
        let a = corpus.declare_constant("a", sort).unwrap();
        let b = corpus.declare_constant("b", sort).unwrap();
        let support = corpus.declare_constant("c", sort).unwrap();
        let mut sources = Sources::new();
        let snapshot = sources.add("file:///x", 1, "denotate", "abc").unwrap();
        let mut current = Provenance::new();
        for (id, range) in [
            (OccurrenceId::from(sort), 0..1),
            (a.into(), 0..1),
            (b.into(), 1..2),
            (support.into(), 2..3),
        ] {
            current
                .attach(
                    &corpus,
                    &sources,
                    id,
                    [Origin::new(sources.span(snapshot, range).unwrap())],
                )
                .unwrap();
        }
        let upstream = Provenance::new();
        let files = BTreeSet::from(["file:///x".into()]);
        let placement = Placement {
            program: "root",
            verification: None,
            user_files: &files,
            sources: &sources,
            current: &current,
            upstream: &upstream,
        };
        let contributions = [
            (sort.into(), Role::Obligation),
            (a.into(), Role::Producer),
            (b.into(), Role::Producer),
            (support.into(), Role::RelatedOnly),
        ]
        .map(|(occurrence, role)| Contribution { occurrence, role });
        let out = placement
            .place(
                &Identity::Region(BTreeSet::new()),
                Kind::Rewrite,
                "redundant",
                &[],
                &contributions,
            )
            .unwrap();
        assert_eq!(
            out.iter()
                .map(|d| sources.text(d.primary).unwrap())
                .collect::<Vec<_>>(),
            ["a", "b"]
        );
        assert!(out.iter().all(|d| {
            d.related
                .iter()
                .any(|r| sources.text(r.span).unwrap() == "c")
        }));
    }
}
