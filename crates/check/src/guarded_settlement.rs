//! Guard-relative, rank-ordered settlement. A candidate is relaxed before bounds
//! are computed and cannot supply a live settling producer for its own proof.
use crate::{
    admission_skips::{Attempt, Attempts},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, or};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

// Optimization cutoffs: no rewrite is installed when a complete certificate does
// not fit. Global work/BDD/dependency limits remain independent.
pub(crate) const EXPRESSION_NODES: usize = 1024;
pub(crate) const EXPRESSION_DEPTH: usize = 64;
pub(crate) const CERTIFICATE_NODES: usize = 8192;

#[derive(Debug, Clone)]
pub struct GuardedSettlementStep {
    pub atom: GroundAtom,
    pub expression: Arc<SettledExpression<GroundAtom>>,
    pub producers: Vec<GroundRuleId>,
    pub false_by_bound: bool,
}

#[derive(Debug, Clone)]
pub struct GuardedSettlementProof {
    pub proof: SymbolicRewriteProof,
    pub occurrence: denotate_ir::OccurrenceId,
    pub replacement: Arc<SettledExpression<GroundAtom>>,
    /// Earlier entries justify later ones. Upper-bound seeds need no marks.
    pub steps: Vec<GuardedSettlementStep>,
}

type Expr = Arc<SettledExpression<GroundAtom>>;
fn constant(v: bool) -> Expr {
    Arc::new(SettledExpression::Constant(v))
}
fn signed(e: Expr, negative: bool) -> Expr {
    if !negative {
        return e;
    }
    match e.as_ref() {
        SettledExpression::Constant(v) => constant(!v),
        SettledExpression::Not(c) => Arc::clone(c),
        _ => Arc::new(SettledExpression::Not(e)),
    }
}
fn join(mut expressions: Vec<Expr>, all: bool) -> Expr {
    expressions.retain(|e| !matches!(e.as_ref(), SettledExpression::Constant(v) if *v == all));
    if expressions
        .iter()
        .any(|e| matches!(e.as_ref(), SettledExpression::Constant(v) if *v != all))
    {
        return constant(!all);
    }
    if expressions.len() == 1 {
        return expressions.pop().unwrap();
    }
    if expressions.is_empty() {
        return constant(all);
    }
    Arc::new(if all {
        SettledExpression::All(expressions)
    } else {
        SettledExpression::Any(expressions)
    })
}
fn bounded(e: &Expr, budget: &mut Budget<'_>) -> Result<bool> {
    let mut pending = vec![(e.as_ref(), 1)];
    let mut nodes = 0;
    while let Some((node, depth)) = pending.pop() {
        budget.tick("guarded expression size")?;
        nodes += 1;
        if nodes > EXPRESSION_NODES || depth > EXPRESSION_DEPTH {
            return Ok(false);
        }
        match node {
            SettledExpression::Not(c) => pending.push((c, depth + 1)),
            SettledExpression::All(cs) | SettledExpression::Any(cs) => {
                pending.extend(cs.iter().map(|c| (c.as_ref(), depth + 1)))
            }
            _ => {}
        }
    }
    Ok(true)
}

impl GroundProgram {
    pub(crate) fn guarded_settlements(
        &self,
        meaning: &SymbolicMeaning<'_>,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        targets: &BTreeSet<GroundRuleId>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
        attempts: &mut Attempts,
    ) -> Result<Vec<GuardedSettlementProof>> {
        let ctx = meaning.context();
        let mut done = BTreeSet::new();
        let mut proofs = Vec::new();
        for candidate in summaries
            .values()
            .filter(|s| targets.contains(&s.rule.id) && !s.exact)
        {
            budget.tick("guarded settlement candidates")?;
            let component = self.component_for(&candidate.rule.head.atom)?;
            if component.cycle.is_none() || done.contains(&component.id) {
                continue;
            }
            let mut candidates = Vec::new();
            let mut signed_atoms = BTreeSet::new();
            for literal in &candidate.rule.body {
                budget.tick("guarded settlement candidates")?;
                if self
                    .atom_index
                    .get(&literal.term.atom)
                    .is_none_or(|i| self.atom_components[*i] != component.id)
                {
                    continue;
                }
                // The same signed atom under the same guard has the same proof
                // result. Keep its first source occurrence for this snapshot.
                if !signed_atoms.insert((
                    literal.term.atom.clone(),
                    literal.polarity == Polarity::Positive,
                )) {
                    continue;
                }
                if !attempts.reuse_negative(
                    &Attempt::GuardedSettlement(candidate.rule.id, literal.term.occurrence),
                    budget,
                    progress,
                )? {
                    candidates.push(literal);
                }
            }
            if candidates.is_empty() {
                continue;
            }
            progress.rule(self, "guarded-bounds", candidate.rule.id, 0);
            let observe = |iteration| progress.iteration(self, iteration);
            let bounds = attempts.run(
                Attempt::GuardedBounds(candidate.rule.id),
                &candidate.rule.head.atom,
                self,
                retained,
                budget,
                progress,
                |retained, budget| {
                    crate::upper_bounds::compute_relaxed(
                        self,
                        component,
                        summaries,
                        ctx,
                        retained,
                        budget,
                        progress.enabled().then_some(&observe),
                        true,
                        Some(candidate.rule.id),
                    )
                },
            )?;
            let Some(bounds) = bounds else {
                continue;
            };
            for literal in candidates {
                progress.rule(self, "guarded-settlement", candidate.rule.id, 0);
                let proof = attempts
                    .proof(
                        Attempt::GuardedSettlement(candidate.rule.id, literal.term.occurrence),
                        &candidate.rule.head.atom,
                        self,
                        retained,
                        budget,
                        progress,
                        Option::is_none,
                        |retained, budget| {
                            self.settle_guarded(
                                candidate, literal, meaning, &bounds, retained, budget, progress,
                            )
                        },
                    )?
                    .flatten();
                if let Some(proof) = proof {
                    done.insert(component.id);
                    proofs.push(proof);
                    break; // Independent components may commit together; one replacement per component.
                }
            }
            *retained -= bounds.nodes();
        }
        Ok(proofs)
    }

    fn settle_guarded(
        &self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        meaning: &SymbolicMeaning<'_>,
        bounds: &Arc<ComponentUpperBounds>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<GuardedSettlementProof>> {
        let baseline = *retained;
        let ctx = meaning.context();
        let guard = &candidate.condition;
        if ctx.restrict(guard, budget)?.is_false() {
            return Ok(None);
        }
        let mut marks: BTreeMap<GroundAtom, (Expr, Condition)> = BTreeMap::new();
        let mut steps = Vec::new();
        let mut expression_nodes = 0;
        let cutoff = |progress: &crate::admission_progress::AdmissionReporter<'_>| {
            progress.cutoff(AdmissionAttemptKind::GuardedSettlement)
        };
        // These bounds relax the reading rule to G. Thus they bound supported
        // models before AND after any guarded replacement of that rule.
        for (atom, upper) in &bounds.conditions {
            budget.tick("guarded settlement seeds")?;
            if ctx
                .restrict(&ctx.apply(guard, upper, and, budget)?, budget)?
                .is_false()
            {
                expression_nodes += 1;
                if expression_nodes > CERTIFICATE_NODES {
                    cutoff(progress);
                    *retained = baseline;
                    return Ok(None);
                }
                budget.charge(1, "guarded expression storage")?;
                marks.insert(atom.clone(), (constant(false), ctx.false_condition()));
                steps.push(GuardedSettlementStep {
                    atom: atom.clone(),
                    expression: constant(false),
                    producers: vec![],
                    false_by_bound: true,
                });
                *retained = crate::symbolic::retain(
                    *retained,
                    0,
                    ctx.false_condition().node_count(),
                    budget,
                )?;
            }
        }
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        for p in &bounds.producers {
            budget.tick("guarded producer index")?;
            producers.entry(&p.rule.head.atom).or_default().push(p);
        }
        loop {
            let mut changed = false;
            for atom in bounds.conditions.keys() {
                budget.tick("guarded settlement")?;
                if marks.contains_key(atom) {
                    continue;
                }
                let mut alternatives = Vec::new();
                let mut value = ctx.false_condition();
                let mut exact = true;
                let mut live = Vec::new();
                for producer in producers.get(atom).into_iter().flatten() {
                    budget.tick("guarded producer")?;
                    let mut body = producer.condition.clone();
                    let mut terms = producer
                        .rule
                        .replacements
                        .iter()
                        .map(|r| Arc::clone(&r.expression))
                        .collect::<Vec<_>>();
                    let mut complete = true;
                    for premise in &producer.rule.body {
                        budget.tick("guarded settlement body")?;
                        let negative = premise.polarity == Polarity::Negative;
                        let pair = match meaning.fact(&premise.term.atom)? {
                            SymbolicFact::Settled(v) => Some((
                                Arc::new(SettledExpression::Atom(premise.term.atom.clone())),
                                v,
                            )),
                            SymbolicFact::Inconclusive(c) => return Err(c.into()),
                            SymbolicFact::Blocked(_) => marks.get(&premise.term.atom).cloned(),
                        };
                        if let Some((e, mut v)) = pair {
                            if negative {
                                v = ctx.complement(&v, budget)?;
                            }
                            body = ctx.apply(&body, &v, and, budget)?;
                            budget.tick("guarded expression storage")?;
                            if terms.len() >= EXPRESSION_NODES {
                                cutoff(progress);
                                *retained = baseline;
                                return Ok(None);
                            }
                            terms.push(signed(e, negative));
                        } else {
                            complete = false;
                        }
                    }
                    if ctx
                        .restrict(&ctx.apply(guard, &body, and, budget)?, budget)?
                        .is_false()
                    {
                        continue;
                    }
                    // Never justify the replacement using its own live producer.
                    if !complete || producer.rule.id == candidate.rule.id {
                        exact = false;
                        break;
                    }
                    let e = join(terms, true);
                    if !bounded(&e, budget)? {
                        cutoff(progress);
                        *retained = baseline;
                        return Ok(None);
                    }
                    budget.tick("guarded expression storage")?;
                    if alternatives.len() >= EXPRESSION_NODES {
                        cutoff(progress);
                        *retained = baseline;
                        return Ok(None);
                    }
                    alternatives.push(e);
                    live.push(producer.rule.id);
                    value = ctx.apply(&value, &body, or, budget)?;
                }
                if exact {
                    let e = join(alternatives, false);
                    if !bounded(&e, budget)?
                        || expression_nodes.saturating_add(e.nodes()) > CERTIFICATE_NODES
                    {
                        cutoff(progress);
                        *retained = baseline;
                        return Ok(None);
                    }
                    expression_nodes += e.nodes();
                    budget.charge(e.nodes(), "guarded expression storage")?;
                    *retained = crate::symbolic::retain(*retained, 0, value.node_count(), budget)?;
                    steps.push(GuardedSettlementStep {
                        atom: atom.clone(),
                        expression: Arc::clone(&e),
                        producers: live,
                        false_by_bound: false,
                    });
                    marks.insert(atom.clone(), (e, value));
                    changed = true;
                }
            }
            if marks.contains_key(&literal.term.atom) || !changed {
                break;
            }
        }
        let Some((expression, truth)) = marks.get(&literal.term.atom) else {
            *retained = baseline;
            return Ok(None);
        };
        // Leave constant cases to the existing removal/discharge passes, preserving
        // their public findings and proof identities.
        let yes = ctx.restrict(&ctx.apply(guard, truth, and, budget)?, budget)?;
        let no = ctx.restrict(
            &ctx.apply(guard, &ctx.complement(truth, budget)?, and, budget)?,
            budget,
        )?;
        if yes.is_false() || no.is_false() {
            *retained = baseline;
            return Ok(None);
        }
        let expression = signed(
            Arc::clone(expression),
            literal.polarity == Polarity::Negative,
        );
        if !bounded(&expression, budget)? {
            cutoff(progress);
            *retained = baseline;
            return Ok(None);
        }
        let coverage = if literal.polarity == Polarity::Negative {
            ctx.complement(truth, budget)?
        } else {
            truth.clone()
        };
        let covering = producers
            .get(&literal.term.atom)
            .into_iter()
            .flatten()
            .map(|p| (*p).clone())
            .collect();
        budget.charge(
            candidate.rule.body.len() + expression_nodes + bounds.producers.len(),
            "guarded proof storage",
        )?;
        *retained = baseline;
        let proof = GuardedSettlementProof {
            proof: SymbolicRewriteProof {
                candidate: candidate.clone(),
                producers: covering,
                coverage,
                upper_bounds: Some(Arc::clone(bounds)),
            },
            occurrence: literal.term.occurrence,
            replacement: expression,
            steps,
        };
        // Retained certificate accounting is conservative, as for other rewrites.
        *retained = crate::symbolic::retain(
            *retained,
            0,
            bounds.nodes()
                + candidate.nodes()
                + proof.proof.coverage.node_count()
                + proof
                    .proof
                    .producers
                    .iter()
                    .map(ProducerSummary::nodes)
                    .sum::<usize>(),
            budget,
        )?;
        Ok(Some(proof))
    }
}
