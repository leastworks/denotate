use crate::*;
use denotate_check::*;
use denotate_ir::*;
use std::collections::{BTreeMap, BTreeSet};

/// Display limits only; never checker budgets or limits on retained proofs.
pub const STRUCTURAL_NOTE_LIMIT: usize = 8;
pub const STRUCTURAL_LOCATION_LIMIT: usize = 16;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum RewriteDetail {
    #[default]
    Direct,
    Full,
}

pub struct Rewrite<'a> {
    pub rule: RuleId,
    pub literal: Option<OccurrenceId>,
    pub proofs: Vec<&'a RewriteProof>,
    pub covers_all_instances: bool,
    pub message: &'static str,
}
impl Rewrite<'_> {
    pub fn identity(&self) -> Identity {
        Identity::Rewrite {
            rule: self.rule,
            literal: self.literal,
        }
    }
    pub fn notes(
        &self,
        corpus: &Corpus,
        names: &dyn Fn(OccurrenceId) -> String,
    ) -> Result<Vec<String>> {
        let mut notes = BTreeSet::new();
        for proof in &self.proofs {
            if let Some(p) = proof.bound_removal() {
                notes.insert(format!("Bound proof: wherever this producer can apply, independently settled producers already make {} true. Exact producers also guarantee the atoms used to strengthen the cycle bounds; none of those producers is removed by this batch.", crate::evidence::atom_name(corpus, names, &p.proof.candidate.rule.head.atom)?));
                continue;
            }
            let Some(p) = proof.structural() else {
                continue;
            };
            let settled = |atom: &GroundAtom| -> Result<String> {
                let (value, reason) = p.settlement(atom);
                let reason = match reason {
                    StructuralSettlement::Producer => "through a settling producer",
                    StructuralSettlement::NoProducer => "with no possible ground producer",
                    StructuralSettlement::ProducersRemoved => {
                        "because all producers are dead or removed"
                    }
                    StructuralSettlement::NoDerivation => "with no derivation from its producers",
                };
                Ok(format!(
                    "{} is structurally {value} {reason}",
                    crate::evidence::atom_name(corpus, names, atom)?
                ))
            };
            notes.insert(match &p.reason {
                StructuralReason::TrueHead { atom } => format!("Structural proof: {}. See the direct justification.", settled(atom)?),
                StructuralReason::Dead { literal } => format!("Structural proof: {}{} cannot hold; {}.", if literal.polarity == Polarity::Negative { "!" } else { "" }, crate::evidence::atom_name(corpus, names, &literal.term.atom)?, settled(&literal.term.atom)?),
                StructuralReason::Subsumed { unfolded, .. } => if unfolded.is_empty() {
                    "Structural proof: the supporting definition requires a subset of these signed premises.".into()
                } else { "Structural proof: after unfolding single-producer positive premises, the supporting definition requires a subset of these signed premises. Unfolded definitions are related locations.".into() },
            });
            if let StructuralReason::Subsumed { settled: atoms, .. } = &p.reason {
                for atom in atoms {
                    notes.insert(format!(
                        "Settled premise removed before comparison: {}.",
                        settled(atom)?
                    ));
                }
            }
        }
        Ok(notes.into_iter().collect())
    }
    pub fn contributions(&self, detail: RewriteDetail) -> Vec<Contribution> {
        let mut out = vec![Contribution {
            occurrence: self.literal.unwrap_or(self.rule.into()),
            role: Role::Producer,
        }];
        let mut seen = BTreeSet::new();
        for proof in &self.proofs {
            let full = detail == RewriteDetail::Full;
            let structural = proof.structural().is_some() || proof.bound_removal().is_some();
            let rules = if full {
                proof.supporting_rules()
            } else {
                proof.direct_rules()
            };
            for rule in rules {
                let mut related = Vec::new();
                if structural && !full {
                    // One source definition is the direct justification. Argument
                    // tokens and its premises belong to the requested full view.
                    related.push(Contribution {
                        occurrence: rule.source.into(),
                        role: Role::DirectRewriteProof,
                    });
                } else {
                    rule_contributions(rule, &mut related);
                    for c in &mut related {
                        c.role = Role::RelatedOnly;
                    }
                }
                for c in related {
                    if seen.insert((c.occurrence, c.role)) {
                        out.push(c);
                    }
                }
            }
        }
        out
    }
}

impl Placement<'_> {
    /// Structural display bounds apply to the union for this source warning,
    /// after provenance resolution. Symbolic evidence is never truncated.
    pub fn rewrite(
        &self,
        rewrite: &Rewrite<'_>,
        corpus: &Corpus,
        names: &dyn Fn(OccurrenceId) -> String,
        detail: RewriteDetail,
    ) -> Result<Vec<Diagnostic>> {
        let structural = rewrite.proofs.iter().any(|p| p.structural().is_some());
        let bounded = rewrite.proofs.iter().any(|p| p.bound_removal().is_some());
        let mut notes = rewrite.notes(corpus, names)?;
        let omitted_notes = if detail == RewriteDetail::Direct {
            let omitted = notes.len().saturating_sub(STRUCTURAL_NOTE_LIMIT);
            notes.truncate(STRUCTURAL_NOTE_LIMIT);
            omitted
        } else {
            0
        };
        let mut diagnostics = self.place(
            &rewrite.identity(),
            Kind::Rewrite,
            rewrite.message,
            &notes,
            &rewrite.contributions(detail),
        )?;
        for d in &mut diagnostics {
            d.evidence = serde_json::json!({"kind":"rewrite-proof","coversAllInstances":rewrite.covers_all_instances});
            if structural || bounded {
                let mode = serde_json::json!(if detail == RewriteDetail::Full {
                    "full"
                } else {
                    "direct"
                });
                if structural {
                    d.evidence["structuralDetail"] = mode.clone();
                }
                if bounded {
                    d.evidence["boundDetail"] = mode;
                }
                d.evidence["omittedNotes"] = serde_json::json!(0);
                d.evidence["omittedRelatedLocations"] = serde_json::json!(0);
            }
        }
        if !(structural || bounded) || detail == RewriteDetail::Full {
            return Ok(diagnostics);
        }
        // Protect symbolic related locations even in a warning with mixed proofs.
        let symbolic = Rewrite {
            rule: rewrite.rule,
            literal: rewrite.literal,
            proofs: rewrite
                .proofs
                .iter()
                .copied()
                .filter(|p| p.symbolic().is_some())
                .collect(),
            covers_all_instances: rewrite.covers_all_instances,
            message: rewrite.message,
        };
        let protected: BTreeSet<_> = self
            .contribution_locations(&symbolic.contributions(RewriteDetail::Direct))?
            .1
            .into_iter()
            .collect();
        // Choose the same retained union for every primary location.
        let locations: BTreeSet<_> = diagnostics
            .iter()
            .flat_map(|d| &d.related)
            .filter(|r| !protected.contains(*r))
            .cloned()
            .collect();
        let omitted_locations = locations.len().saturating_sub(STRUCTURAL_LOCATION_LIMIT);
        let retained: BTreeSet<_> = locations
            .into_iter()
            .take(STRUCTURAL_LOCATION_LIMIT)
            .collect();
        for d in &mut diagnostics {
            if omitted_locations > 0 {
                d.related
                    .retain(|r| protected.contains(r) || retained.contains(r));
            }
            if omitted_notes > 0 || omitted_locations > 0 {
                let kind = if bounded { "rewrite" } else { "structural" };
                d.notes.push(format!("Omitted {omitted_notes} {kind} notes and {omitted_locations} related locations; request full rewrite evidence (CLI --verbose)."));
            }
            d.evidence["omittedNotes"] = serde_json::json!(omitted_notes);
            d.evidence["omittedRelatedLocations"] = serde_json::json!(omitted_locations);
        }
        Ok(diagnostics)
    }
}
/// Proof grouping and whole-instance coverage are shared. This grants no edit:
/// a frontend must separately certify a safe syntax transformation.
pub fn rewrites<'a>(corpus: &Corpus, program: &'a GroundProgram) -> Result<Vec<Rewrite<'a>>> {
    let mut grouped = BTreeMap::<_, Vec<_>>::new();
    for proof in program.rewrite_proofs() {
        let rule = proof.candidate().source;
        if corpus.rule(rule).is_none() {
            return Err(Error::InvalidFinding("rewrite belongs to another corpus"));
        }
        let literal = match proof.kind {
            RewriteKind::RedundantProducer => None,
            RewriteKind::Discharge { literal_occurrence } => {
                if program.rule(proof.candidate().id).is_none() {
                    continue;
                }
                Some(literal_occurrence)
            }
        };
        grouped.entry((rule, literal)).or_default().push(proof);
    }
    if grouped.is_empty() {
        return Ok(Vec::new());
    }
    // Count originals once, including subsequently removed instances. Restrict
    // the index to sources with warnings, rather than duplicating the graph.
    let mut instances: BTreeMap<_, usize> = grouped.keys().map(|(rule, _)| (*rule, 0)).collect();
    for rule in program.original_rules() {
        if let Some(count) = instances.get_mut(&rule.source) {
            *count += 1;
        }
    }
    Ok(grouped
        .into_iter()
        .map(|((rule, literal), proofs)| {
            // Every proof candidate is an original instance of this source rule.
            // Count distinct instances, not proofs, independently for each literal.
            let proved: BTreeSet<_> = proofs.iter().map(|p| p.candidate().id).collect();
            let covers_all_instances = proved.len() == instances[&rule];
            let message = if !covers_all_instances {
                "This condition or definition is redundant in some checked cases, but not all its uses are justified for removal."
            } else if literal.is_some() {
                "This negated condition is redundant: whenever its settled guard holds, the excluded condition cannot hold."
            } else if proofs.iter().all(|p| p.structural().is_some_and(|p| matches!(p.reason, StructuralReason::Dead { .. }))) {
                "This definition cannot apply: one of its premises is structurally false."
            } else {
                "This definition adds no result: other definitions already cover every case where it could apply."
            };
            Rewrite {
                rule,
                literal,
                proofs,
                covers_all_instances,
                message,
            }
        })
        .collect())
}
