//! Implication uses a definition other than the rewritten head's equation.
//! Sequential structural steps read the current view, never stale definitions.
use super::*;

pub(super) fn record(
    original: &Cone,
    report: &mut PruningReport,
    row: usize,
    context: PruningContext,
    scope: &'static str,
    scope_heads: usize,
    rule: GroundRuleId,
    head: usize,
    literal: usize,
    structural: bool,
) {
    report.removed_literals += 1;
    report.components[row].removed_literals += 1;
    retain(
        report,
        PruningRecord {
            context,
            kind: PruningKind::ImpliedBodyLiteral,
            head: original.atoms[head].clone(),
            rules: vec![rule],
            removed: 0,
            removed_literals: 1,
            scope,
            scope_heads,
            pins: vec![],
            omitted_pins: 0,
            literal: Some(original.atoms[literal].clone()),
            structural,
        },
    );
}
