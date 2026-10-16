//! Rewrite wording and edit eligibility belong to the frontend, not the IR.
use crate::{ast::*, lowering::LoweredProgram};
use denotate_check::*;
use denotate_ir::*;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Contribution {
    Library,
    Program,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceEdit {
    pub span: SourceSpan,
    pub replacement: String,
}
#[derive(Debug, Default)]
pub struct RewriteMetadata {
    pub owners: BTreeMap<RuleId, Contribution>,
    /// Frontend-certified, direct syntax removals. Not inferred by the checker
    /// from overlapping source spans or the spelling of generated relations.
    pub removals: BTreeMap<OccurrenceId, SourceEdit>,
}
#[derive(Debug)]
pub struct RewriteWarning {
    pub owner: Contribution,
    pub rule: RuleId,
    pub literal: Option<OccurrenceId>,
    pub proofs: Vec<RewriteProofId>,
    pub covers_all_instances: bool,
    pub message: String,
    /// Constructed/library IR may have no location in this view. Keep the
    /// creator warning without borrowing a user's unrelated source location.
    pub primary: Option<SourceSpan>,
    pub related: Vec<Origin>,
    pub edit: Option<SourceEdit>,
}

pub fn present_rewrites(
    lowered: &LoweredProgram,
    program: &GroundProgram,
    sources: &Sources,
    view: &str,
) -> Result<Vec<RewriteWarning>, crate::presentation::PresentationError> {
    use crate::presentation::PresentationError;
    let mut grouped = BTreeMap::<_, Vec<_>>::new();
    for proof in program.rewrite_proofs() {
        let rule = proof.candidate.rule.source;
        let literal = match proof.kind {
            RewriteKind::RedundantProducer => None,
            RewriteKind::Discharge { literal_occurrence } => {
                // Prefer whole-rule warnings if a later batch removed this instance.
                if !program.rules().any(|r| r.id == proof.candidate.rule.id) {
                    continue;
                }
                Some(literal_occurrence)
            }
        };
        grouped.entry((rule, literal)).or_default().push(proof);
    }
    let mut result = Vec::new();
    for ((rule, literal), proofs) in grouped {
        if lowered.corpus.rule(rule).is_none() {
            return Err(PresentationError::InvalidFinding(
                "rewrite belongs to another corpus",
            ));
        }
        let owner = *lowered.rewrite_metadata.owners.get(&rule).ok_or(
            PresentationError::InvalidFinding("missing rewrite contribution owner"),
        )?;
        let related: Vec<_> = lowered
            .provenance
            .in_view(literal.unwrap_or(rule.into()), sources, view)?
            .into_iter()
            .cloned()
            .collect();
        let primary = related
            .iter()
            .find(|o| o.role == if literal.is_some() { "not" } else { "mapping" })
            .or_else(|| related.first())
            .map(|o| o.span);
        let all_justified = program
            .original_rules()
            .filter(|r| r.source == rule)
            .all(|r| proofs.iter().any(|p| p.candidate.rule.id == r.id));
        let edit = literal.and_then(|literal| {
            let edit = lowered.rewrite_metadata.removals.get(&literal)?;
            (all_justified && sources.snapshot(edit.span.snapshot()).ok()?.view == view)
                .then(|| edit.clone())
        });
        result.push(RewriteWarning {
            owner, rule, literal, proofs: proofs.iter().map(|p| p.id).collect(), primary, related, edit,
            covers_all_instances: all_justified,
            message: if !all_justified {
                "This condition or definition is redundant in some checked cases, but not all its uses are justified for removal.".into()
            } else if literal.is_some() {
                "This negated condition is redundant: whenever its settled guard holds, the excluded condition cannot hold.".into()
            } else {
                "This definition adds no result: other definitions already cover every case where it could apply.".into()
            },
        });
    }
    Ok(result)
}

/// Only flat conjunctions of direct conditions are editable here. Compound
/// negation, grouping, OR splitting and generated helpers remain warn-only.
pub(crate) fn removals(
    mapping: &Mapping,
    sources: &Sources,
) -> Result<Vec<(SourceSpan, SourceEdit)>, ProvenanceError> {
    fn leaves<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) -> bool {
        match &expr.kind {
            ExprKind::And(a, b) => leaves(a, out) && leaves(b, out),
            ExprKind::Available(_) | ExprKind::Present(_) => {
                out.push(expr);
                true
            }
            ExprKind::Not { operand, .. }
                if matches!(operand.kind, ExprKind::Available(_) | ExprKind::Present(_)) =>
            {
                out.push(expr);
                true
            }
            _ => false,
        }
    }
    let Some(condition) = &mapping.condition else {
        return Ok(vec![]);
    };
    let mut parts = Vec::new();
    if !leaves(condition, &mut parts) {
        return Ok(vec![]);
    }
    let snapshot = condition.span.snapshot();
    if parts.iter().any(|p| p.span.snapshot() != snapshot)
        || mapping.input.span.snapshot() != snapshot
    {
        return Ok(vec![]);
    }
    let mut result = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        if !matches!(part.kind, ExprKind::Not { .. }) {
            continue;
        }
        let (bytes, separator) = if parts.len() == 1 {
            (
                mapping.input.span.byte_range().end..condition.span.byte_range().end,
                "when",
            )
        } else if i == 0 {
            (
                part.span.byte_range().start..parts[1].span.byte_range().start,
                "and",
            )
        } else {
            (
                parts[i - 1].span.byte_range().end..part.span.byte_range().end,
                "and",
            )
        };
        let span = sources.span(snapshot, bytes)?;
        let remainder = sources.text(span)?.replace(sources.text(part.span)?, "");
        if remainder.trim() == separator {
            result.push((
                part.span,
                SourceEdit {
                    span,
                    replacement: String::new(),
                },
            ));
        }
    }
    Ok(result)
}
