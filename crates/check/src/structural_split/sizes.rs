//! Profiling-only inspection. Its private budget and BDD temporaries never enter
//! admission accounting, certificates or reusable results.
use super::*;
use std::time::{Duration, Instant};

pub(super) fn measure(
    proofs: &[GuardedSettlementProof],
    meaning: &SymbolicMeaning<'_>,
    caller: &Limits,
) -> Result<SplitReplacementSizes> {
    let _span = caller.profile.span("structural-split-sizes", None);
    let limits = Limits {
        cancellation: caller.cancellation.clone(),
        max_work: 5_000_000,
        max_bdd_nodes: 100_000,
        max_bdd_tasks: 1_000_000,
        max_condition_nodes: 1_000_000,
        timeout: Duration::from_millis(250),
        ..Limits::default()
    };
    measure_with_limits(proofs, meaning, &limits)
}

#[cfg(test)]
mod tests;

fn measure_with_limits(
    proofs: &[GuardedSettlementProof],
    meaning: &SymbolicMeaning<'_>,
    limits: &Limits,
) -> Result<SplitReplacementSizes> {
    let start = Instant::now();
    let mut report = SplitReplacementSizes {
        replacements: proofs.len(),
        ..Default::default()
    };
    let mut budget = Budget::new(limits);
    let result = inspect(proofs, meaning, &mut report, &mut budget);
    report.elapsed = start.elapsed();
    report.state = match result {
        Ok(()) => "complete",
        Err(CheckError::Cancelled) => return Err(CheckError::Cancelled),
        Err(CheckError::LimitExceeded {
            phase,
            resource,
            details,
        }) => {
            report.failure = Some(Inconclusive {
                phase,
                resource,
                details,
            });
            "incomplete"
        }
        Err(CheckError::Deadline { phase, details }) => {
            report.failure = Some(Inconclusive {
                phase,
                resource: "deadline",
                details,
            });
            "incomplete"
        }
        // Inspection cannot invalidate an otherwise completed certificate.
        Err(_) => "unavailable",
    };
    Ok(report)
}

fn inspect(
    proofs: &[GuardedSettlementProof],
    meaning: &SymbolicMeaning<'_>,
    report: &mut SplitReplacementSizes,
    budget: &mut Budget<'_>,
) -> Result<()> {
    let mut retained = 0;
    let mut roots = Vec::new();
    let mut root_ids = BTreeSet::new();
    for proof in proofs {
        budget.tick("replacement size roots")?;
        if root_ids.insert(Arc::as_ptr(&proof.replacement) as usize) {
            retained = crate::symbolic::retain(retained, 0, 4, budget)?;
            roots.push(proof);
        }
    }
    report.distinct_expressions = Some(roots.len());
    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    for proof in &roots {
        visit(
            &proof.replacement,
            &mut seen,
            &mut order,
            &mut retained,
            budget,
        )?;
    }
    report.expression_nodes = Some(order.len());
    let mut remaining = BTreeMap::<usize, usize>::new();
    for expression in &order {
        let children = match expression.as_ref() {
            SettledExpression::Not(c) => std::slice::from_ref(c),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => cs.as_slice(),
            _ => &[],
        };
        for child in children {
            budget.tick("replacement size references")?;
            *remaining.entry(Arc::as_ptr(child) as usize).or_default() += 1;
        }
    }
    let ctx = meaning.context();
    let mut values = BTreeMap::<usize, Condition>::new();
    for expression in order {
        budget.tick("replacement size evaluation")?;
        let key = Arc::as_ptr(expression) as usize;
        let value = match expression.as_ref() {
            SettledExpression::Constant(v) => {
                if *v {
                    ctx.true_condition()
                } else {
                    ctx.false_condition()
                }
            }
            SettledExpression::Atom(atom) => match meaning.fact(atom)? {
                SymbolicFact::Settled(value) => value,
                _ => return Err(CheckError::Internal("size inspection needs a settled atom")),
            },
            SettledExpression::Not(c) => {
                ctx.complement(&values[&(Arc::as_ptr(c) as usize)], budget)?
            }
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                let all = matches!(expression.as_ref(), SettledExpression::All(_));
                let mut value = if all {
                    ctx.true_condition()
                } else {
                    ctx.false_condition()
                };
                let mut held = 0;
                for c in cs {
                    let next = ctx.apply(
                        &value,
                        &values[&(Arc::as_ptr(c) as usize)],
                        if all { and } else { or },
                        budget,
                    )?;
                    retained = crate::symbolic::retain(retained, held, next.node_count(), budget)?;
                    held = next.node_count();
                    value = next;
                }
                retained -= held;
                value
            }
        };
        retained = crate::symbolic::retain(retained, 0, value.node_count(), budget)?;
        values.insert(key, value);
        report.measured_expressions += usize::from(root_ids.contains(&key));
        let children = match expression.as_ref() {
            SettledExpression::Not(c) => std::slice::from_ref(c),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => cs.as_slice(),
            _ => &[],
        };
        for child in children {
            budget.tick("replacement size release")?;
            let child_key = Arc::as_ptr(child) as usize;
            let uses = remaining.get_mut(&child_key).unwrap();
            *uses -= 1;
            if *uses == 0 && !root_ids.contains(&child_key) {
                retained -= values.remove(&child_key).unwrap().node_count();
            }
        }
    }
    let mut restricted = Vec::new();
    for proof in &roots {
        // Coverage is signed; negative coverage may be true outside W. Mask it
        // explicitly, never label that raw complement as a restricted truth.
        let value = ctx.restrict(&proof.proof.coverage, budget)?;
        retained = crate::symbolic::retain(retained, 0, value.node_count() + 1, budget)?;
        restricted.push(value);
    }
    budget.charge(roots.len() * 2, "replacement size totals")?;
    let unrestricted = || {
        roots
            .iter()
            .map(|p| &values[&(Arc::as_ptr(&p.replacement) as usize)])
    };
    report.unrestricted_bdd = Some(crate::boolean::condition_storage(unrestricted()));
    report.domain_restricted_bdd = Some(crate::boolean::condition_storage(&restricted));
    report.max_unrestricted_bdd_nodes = unrestricted().map(Condition::node_count).max();
    report.max_domain_restricted_bdd_nodes = restricted.iter().map(Condition::node_count).max();
    Ok(())
}

fn visit<'a>(
    expression: &'a Expr,
    seen: &mut BTreeSet<usize>,
    order: &mut Vec<&'a Expr>,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<()> {
    budget.tick("replacement size traversal")?;
    if !seen.insert(Arc::as_ptr(expression) as usize) {
        return Ok(());
    }
    // DAG visitation, result map and traversal metadata; certificate depth is bounded.
    *retained = crate::symbolic::retain(*retained, 0, 11, budget)?;
    match expression.as_ref() {
        SettledExpression::Not(c) => visit(c, seen, order, retained, budget)?,
        SettledExpression::All(cs) | SettledExpression::Any(cs) => {
            for c in cs {
                visit(c, seen, order, retained, budget)?;
            }
        }
        _ => {}
    }
    order.push(expression);
    Ok(())
}
