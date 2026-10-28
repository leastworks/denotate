use crate::*;
use denotate_ir::*;
use serde_json::{Value, json};
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq)]
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
        let mut current = Vec::new();
        let mut related = Vec::new();
        for contribution in contributions {
            for origin in self.current.origins(contribution.occurrence) {
                self.sources.text(origin.span)?;
                if contribution.role != Role::RelatedOnly {
                    if let Some((_, role)) = current.iter_mut().find(|(s, _)| *s == origin.span) {
                        *role = std::cmp::min(*role, contribution.role);
                    } else {
                        current.push((origin.span, contribution.role));
                    }
                }
                let location = RelatedLocation::new(origin.span, contribution.role.label());
                if !related.contains(&location) {
                    related.push(location);
                }
            }
            for origin in self.upstream.origins(contribution.occurrence) {
                self.sources.text(origin.span)?;
                let location = RelatedLocation::new(origin.span, "upstream source origin");
                if !related.contains(&location) {
                    related.push(location);
                }
            }
        }
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
            Role::RelatedOnly => unreachable!("related-only origins cannot be primary"),
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
            if matches!(identity, Identity::Coverage(_))
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
    pub fn finding(&self, finding: &Finding<'_>) -> Result<Vec<Diagnostic>> {
        if !finding.placement_groups.is_empty() {
            let mut out: Vec<Diagnostic> = Vec::new();
            for group in &finding.placement_groups {
                let mut notes = finding.notes.clone();
                notes.extend(group.notes.iter().cloned());
                for diagnostic in self.place(
                    &finding.identity,
                    finding.kind,
                    &finding.message,
                    &notes,
                    &group.contributions,
                )? {
                    if let Some(existing) = out.iter_mut().find(|d| d.primary == diagnostic.primary)
                    {
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
