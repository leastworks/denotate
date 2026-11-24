//! Equation-preserving reductions before graph analysis. No W/H or SAT query.
//! Rule slots/heads remain present to preserve scope identity and source replay;
//! fixed heads and false bodies have no active producers or dependency edges.
use super::*;
use std::collections::VecDeque;

pub(super) struct Removed {
    pub rule: GroundRuleId,
    pub head: usize,
    pub literal: usize,
}
pub(super) struct Reduced {
    pub cone: Cone,
    pub removed: usize,
    pub examples: Vec<Removed>,
}
/// Optional optimization: retain the original equations on a cutoff. The caller
/// still owns the spent budget; cancellation/internal errors are never swallowed.
pub(super) fn optional(c: &Cone, b: &mut Budget<'_>) -> Result<(Reduced, Option<Inconclusive>)> {
    match reduce(c, b) {
        Ok(r) => Ok((r, None)),
        Err(error) => Ok((
            Reduced {
                cone: c.clone(),
                removed: 0,
                examples: vec![],
            },
            Some(inconclusive(error)?),
        )),
    }
}
pub(super) fn reduce(original: &Cone, b: &mut Budget<'_>) -> Result<Reduced> {
    let mut cone = original.clone();
    cone.fixed = encoding::fitting(original, b)?;
    let mut supports = vec![BTreeSet::new(); cone.fixed.len()];
    let mut readers = vec![Vec::new(); cone.fixed.len()];
    let mut queue = VecDeque::new();
    let mut queued = vec![false; cone.rules.len()];
    for (ri, r) in original.rules.iter().enumerate() {
        b.charge(r.body.len() + 1, "completion structural reduction")?;
        if cone.input[r.head]
            || cone.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| cone.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        if r.body.iter().any(|(i, _)| cone.fixed[*i].is_some()) {
            cone.rules[ri]
                .body
                .retain(|(i, _)| cone.fixed[*i].is_none());
        }
        let body = &cone.rules[ri].body;
        for (i, p) in body {
            if *p {
                readers[*i].push(ri);
            }
        }
        if let [(i, true)] = body.as_slice() {
            supports[r.head].insert(*i);
        }
        queue.push_back(ri);
        queued[ri] = true;
    }
    let mut removed = 0;
    let mut examples = vec![];
    while let Some(ri) = queue.pop_front() {
        queued[ri] = false;
        b.tick("completion structural reduction")?;
        let head = cone.rules[ri].head;
        let mut at = 0;
        while at < cone.rules[ri].body.len() {
            let (literal, positive) = cone.rules[ri].body[at];
            b.tick("completion structural reduction")?;
            if !positive || literal == head || cone.input[literal] {
                at += 1;
                continue;
            }
            let body = &cone.rules[ri].body;
            b.charge(body.len(), "completion structural reduction")?;
            if !body
                .iter()
                .any(|(i, p)| *p && *i != literal && supports[literal].contains(i))
            {
                at += 1;
                continue;
            }
            cone.rules[ri].body.remove(at);
            removed += 1;
            if examples.len() < 64 {
                if let Some(rule) = cone.rules[ri].ground {
                    examples.push(Removed {
                        rule,
                        head,
                        literal,
                    });
                }
            }
        }
        // A unary positive producer cannot itself be shortened by this rule.
        // Supports therefore only grow, and only readers of a new support rerun.
        if let [(i, true)] = cone.rules[ri].body.as_slice() {
            if supports[head].insert(*i) {
                b.charge(
                    readers[head].len(),
                    "completion structural reduction readers",
                )?;
                for reader in &readers[head] {
                    if !queued[*reader] {
                        queued[*reader] = true;
                        queue.push_back(*reader);
                    }
                }
            }
        }
    }
    Ok(Reduced {
        cone,
        removed,
        examples,
    })
}
