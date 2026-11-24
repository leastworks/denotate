//! Implication uses a definition other than the rewritten head's equation.
//! Sequential structural steps read the current view, never stale definitions.
use super::*;

pub(super) fn structural(
    original: &Cone,
    result: &mut Cone,
    targets: &symbolic::targets::Targets,
    scope: &'static str,
    context: PruningContext,
    scope_heads: usize,
    report: &mut PruningReport,
    budget: &mut Budget<'_>,
    successes: &mut Successes,
) -> Result<bool> {
    let mut supports = vec![BTreeSet::new(); original.fixed.len()];
    for r in &original.rules {
        budget.tick("completion implied literals index")?;
        if let [(atom, true)] = r.body.as_slice() {
            supports[r.head].insert(*atom);
        }
    }
    let mut changed = false;
    for head in &targets.heads {
        let row = targets.components[head];
        for &ri in &targets.rules[head] {
            for &(lit, positive) in &original.rules[ri].body {
                budget.tick("completion implied literals")?;
                if !positive
                    || lit == *head
                    || original.input[lit]
                    || targets.components.get(&lit) != Some(&row)
                {
                    continue;
                }
                budget.charge(result.rules[ri].body.len(), "completion implied literals")?;
                let implied = result.rules[ri].body.iter().any(|(atom, positive)| {
                    *positive && *atom != lit && supports[lit].contains(atom)
                });
                if !implied {
                    continue;
                }
                let ground = original.rules[ri]
                    .ground
                    .ok_or(CheckError::Internal("implied literal has no source"))?;
                result.rules[ri].body.retain(|l| *l != (lit, true));
                // A shortening can create a new one-atom producer. Existing
                // one-atom producers cannot be shortened by this fast path.
                if let [(atom, true)] = result.rules[ri].body.as_slice() {
                    supports[*head].insert(*atom);
                }
                report.attempts += 1;
                report.components[row].considered += 1;
                report.components[row].proved += 1;
                report.components[row].last_head = Some(original.atoms[*head].clone());
                successes.heads.insert(*head);
                record(
                    original,
                    report,
                    row,
                    context,
                    scope,
                    scope_heads,
                    ground,
                    *head,
                    lit,
                    true,
                );
                changed = true;
            }
        }
    }
    Ok(changed)
}

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
