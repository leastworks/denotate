use crate::*;
use denotate_check::*;
use denotate_ir::*;
use std::collections::{BTreeMap, BTreeSet};

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
    pub fn contributions(&self) -> Vec<Contribution> {
        let mut out = vec![Contribution {
            occurrence: self.literal.unwrap_or(self.rule.into()),
            role: Role::Producer,
        }];
        for proof in &self.proofs {
            for rule in &proof.producers {
                let mut related = Vec::new();
                rule_contributions(&rule.rule, &mut related);
                out.extend(related.into_iter().map(|mut c| {
                    c.role = Role::RelatedOnly;
                    c
                }));
            }
        }
        out
    }
}
/// Proof grouping and whole-instance coverage are shared. This grants no edit:
/// a frontend must separately certify a safe syntax transformation.
pub fn rewrites<'a>(corpus: &Corpus, program: &'a GroundProgram) -> Result<Vec<Rewrite<'a>>> {
    let mut grouped = BTreeMap::<_, Vec<_>>::new();
    for proof in program.rewrite_proofs() {
        let rule = proof.candidate.rule.source;
        if corpus.rule(rule).is_none() {
            return Err(Error::InvalidFinding("rewrite belongs to another corpus"));
        }
        let literal = match proof.kind {
            RewriteKind::RedundantProducer => None,
            RewriteKind::Discharge { literal_occurrence } => {
                if program.rule(proof.candidate.rule.id).is_none() {
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
            let proved: BTreeSet<_> = proofs.iter().map(|p| p.candidate.rule.id).collect();
            let covers_all_instances = proved.len() == instances[&rule];
            let message = if !covers_all_instances {
                "This condition or definition is redundant in some checked cases, but not all its uses are justified for removal."
            } else if literal.is_some() {
                "This negated condition is redundant: whenever its settled guard holds, the excluded condition cannot hold."
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
