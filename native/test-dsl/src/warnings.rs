//! Rewrite wording and edit eligibility belong to the frontend, not the IR.
use crate::{
    ast::*,
    attribution::{RelatedLocation, SourceView},
    lowering::{
        LoweredProgram,
        semantic::{AstPath, ExprPath, Step},
    },
};
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
    pub related: Vec<RelatedLocation>,
    pub edit: Option<SourceEdit>,
}

/// A frontend coverage warning, not a checker rewrite or an admission proof.
/// No rule is removed. An unconditional mask makes every other mask for the
/// same Slot redundant, regardless of that other mask's guard.
pub struct MaskWarning {
    pub primary: SourceSpan,
    pub related: Vec<RelatedLocation>,
    pub message: String,
}

pub fn covered_masks(
    lowered: &LoweredProgram,
    sources: &Sources,
) -> Result<Vec<MaskWarning>, crate::presentation::PresentationError> {
    lowered.attribution.validate(&lowered.corpus, sources)?;
    let mut unconditional = BTreeMap::<_, Vec<_>>::new();
    let mut conditional = BTreeMap::new();
    for mask in lowered.attribution.masks.values() {
        if mask.condition.is_none() {
            let spans = unconditional.entry(mask.target).or_default();
            if !spans.contains(&mask.statement) {
                spans.push(mask.statement);
            }
        } else {
            conditional.insert(mask.statement, mask.target);
        }
    }
    let mut warnings = Vec::new();
    for (primary, target) in conditional {
        if let Some(covering) = unconditional.get(&target) {
            let target = lowered.corpus.constant(target).ok_or(
                crate::presentation::PresentationError::InvalidFinding("unknown mask target"),
            )?;
            warnings.push(MaskWarning {
                primary,
                related: covering
                    .iter()
                    .map(|s| RelatedLocation::new(*s, "unconditional mask"))
                    .collect(),
                message: format!(
                    "This mask adds no effect: Slot {} is already masked unconditionally.",
                    target.name
                ),
            });
        }
    }
    Ok(warnings)
}

pub fn present_rewrites(
    lowered: &LoweredProgram,
    program: &GroundProgram,
    sources: &Sources,
    view: &str,
) -> Result<Vec<RewriteWarning>, crate::presentation::PresentationError> {
    use crate::presentation::PresentationError;
    let view = SourceView::try_from(view)?;
    lowered.attribution.validate(&lowered.corpus, sources)?;
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
        // The DSL coverage warning already explains this whole statement.
        // Keep the checker's proof in the report, without publishing it twice.
        if view == SourceView::TestDsl
            && literal.is_none()
            && lowered.attribution.masks.get(&rule).is_some_and(|mask| {
                mask.condition.is_some()
                    && lowered
                        .attribution
                        .masks
                        .values()
                        .any(|m| m.target == mask.target && m.condition.is_none())
            })
        {
            continue;
        }
        let owner = *lowered.attribution.rewrites.owners.get(&rule).ok_or(
            PresentationError::InvalidFinding("missing rewrite contribution owner"),
        )?;
        let primary = lowered
            .attribution
            .origin(literal.unwrap_or(rule.into()), sources, view)?;
        let related = primary
            .into_iter()
            .map(|span| {
                RelatedLocation::new(
                    span,
                    if literal.is_some() {
                        "redundant condition"
                    } else {
                        "redundant definition"
                    },
                )
            })
            .collect();
        let all_justified = program
            .original_rules()
            .filter(|r| r.source == rule)
            .all(|r| proofs.iter().any(|p| p.candidate.rule.id == r.id));
        let edit = literal.and_then(|literal| {
            let edit = lowered.attribution.rewrites.removals.get(&literal)?;
            (all_justified && sources.snapshot(edit.span.snapshot()).ok()?.view == view.as_str())
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
) -> Result<Vec<(AstPath, SourceEdit)>, ProvenanceError> {
    condition_removals(mapping.condition.as_ref(), mapping.input.span, sources)
}

pub(crate) fn condition_removals(
    condition: Option<&Expr>,
    before_when: SourceSpan,
    sources: &Sources,
) -> Result<Vec<(AstPath, SourceEdit)>, ProvenanceError> {
    fn leaves<'a>(expr: &'a Expr, path: ExprPath, out: &mut Vec<(&'a Expr, ExprPath)>) -> bool {
        match &expr.kind {
            ExprKind::And(a, b) => {
                leaves(a, path.child(Step::Left), out) && leaves(b, path.child(Step::Right), out)
            }
            ExprKind::Available(_) | ExprKind::Present(_) => {
                out.push((expr, path));
                true
            }
            ExprKind::Not { operand, .. }
                if matches!(operand.kind, ExprKind::Available(_) | ExprKind::Present(_)) =>
            {
                out.push((expr, path));
                true
            }
            _ => false,
        }
    }
    let Some(condition) = condition else {
        return Ok(vec![]);
    };
    let mut parts = Vec::new();
    if !leaves(condition, ExprPath::default(), &mut parts) {
        return Ok(vec![]);
    }
    let snapshot = condition.span.snapshot();
    if parts.iter().any(|(p, _)| p.span.snapshot() != snapshot)
        || before_when.snapshot() != snapshot
    {
        return Ok(vec![]);
    }
    let mut result = Vec::new();
    for (i, (part, path)) in parts.iter().enumerate() {
        if !matches!(part.kind, ExprKind::Not { .. }) {
            continue;
        }
        let (bytes, separator) = if parts.len() == 1 {
            (
                before_when.byte_range().end..condition.span.byte_range().end,
                "when",
            )
        } else if i == 0 {
            (
                part.span.byte_range().start..parts[1].0.span.byte_range().start,
                "and",
            )
        } else {
            (
                parts[i - 1].0.span.byte_range().end..part.span.byte_range().end,
                "and",
            )
        };
        let span = sources.span(snapshot, bytes)?;
        let remainder = sources.text(span)?.replace(sources.text(part.span)?, "");
        if remainder.trim() == separator {
            result.push((
                AstPath::Expression(path.clone()),
                SourceEdit {
                    span,
                    replacement: String::new(),
                },
            ));
        }
    }
    Ok(result)
}
