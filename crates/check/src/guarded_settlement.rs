//! Guard-relative, rank-ordered settlement. A candidate is relaxed before bounds
//! are computed and cannot supply a live settling producer for its own proof.
use crate::{
    admission_skips::{Attempt, Attempts},
    guarded_bounds::{BorrowedBounds, BorrowedCone, Preparation},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, or};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::Instant,
};

// Optimization cutoffs: no rewrite is installed when a complete certificate does
// not fit. Global work/BDD/dependency limits remain independent.
pub(crate) const EXPRESSION_NODES: usize = 1024;
pub(crate) const EXPRESSION_DEPTH: usize = 64;
pub(crate) const CERTIFICATE_NODES: usize = 8192;
// Provisional scheduling only; neither the cone nor its certificate changes.
const LOOKAHEAD: usize = 32;
const RANK_STORAGE: usize = 16;

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
    pub bounds: Arc<GuardedBounds>,
    pub occurrence: denotate_ir::OccurrenceId,
    pub replacement: Arc<SettledExpression<GroundAtom>>,
    /// Earlier entries justify later ones. Upper-bound seeds need no marks.
    pub steps: Vec<GuardedSettlementStep>,
    pub implied_guard: Option<ImpliedGuardProof>,
}

pub(crate) type Expr = Arc<SettledExpression<GroundAtom>>;
pub(crate) fn constant(v: bool) -> Expr {
    Arc::new(SettledExpression::Constant(v))
}
pub(crate) fn signed(e: Expr, negative: bool) -> Expr {
    if !negative {
        return e;
    }
    match e.as_ref() {
        SettledExpression::Constant(v) => constant(!v),
        SettledExpression::Not(c) => Arc::clone(c),
        _ => Arc::new(SettledExpression::Not(e)),
    }
}
pub(crate) fn join(mut expressions: Vec<Expr>, all: bool) -> Expr {
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
pub(crate) fn bounded(e: &Expr, budget: &mut Budget<'_>) -> Result<bool> {
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
        // Cheap structural indexing/ordering only. No candidate BDD or full cone
        // is computed before the first attempt.
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        let mut hints = BTreeMap::<GroundAtom, crate::implied_guard::Hint>::new();
        for p in summaries.values() {
            budget.tick("guarded producer index")?;
            hints.entry(p.rule.head.atom.clone()).or_default().add(p);
            producers
                .entry(&p.rule.head.atom)
                .or_default()
                .push(p.rule.id);
        }
        let mut candidates = Vec::new();
        for candidate in summaries
            .values()
            .filter(|s| targets.contains(&s.rule.id) && !s.exact)
        {
            budget.tick("guarded settlement candidates")?;
            let component = self.component_for(&candidate.rule.head.atom)?;
            if component.cycle.is_none() {
                continue;
            }
            let hint = crate::implied_guard::hint(candidate, &hints, budget)?;
            let mut signed_atoms = BTreeSet::new();
            for literal in &candidate.rule.body {
                budget.tick("guarded settlement candidates")?;
                if self
                    .atom_index
                    .get(&literal.term.atom)
                    .is_none_or(|i| self.atom_components[*i] != component.id)
                    || !signed_atoms.insert((
                        literal.term.atom.clone(),
                        literal.polarity == Polarity::Positive,
                    ))
                {
                    continue;
                }
                // An unrestricted guard cannot prune producers; try informative guards first.
                let cost = (
                    candidate.condition.is_true() && hint.is_none(),
                    hint.unwrap_or(candidate.condition.node_count()),
                    producers.get(&literal.term.atom).map_or(0, Vec::len),
                );
                candidates.push((cost, candidate, literal, component));
            }
        }
        progress.candidate_probe_register(candidates.len());
        budget.charge(
            candidates
                .len()
                .saturating_mul(candidates.len().max(1).ilog2() as usize + 1),
            "guarded candidate order",
        )?;
        // The queue sorts priorities; keep the original source/occurrence index
        // for ties even when discovery later demotes an unhelpful hint.
        // One-entry snapshot-local cache: retain only the most recent complete
        // computation (or failure key), so optional reuse cannot accumulate BDDs.
        let mut cache: Option<(Arc<BorrowedCone<'_>>, Option<Arc<BorrowedBounds<'_>>>)> = None;
        let mut queue = candidates
            .into_iter()
            .enumerate()
            .map(|(index, (cost, candidate, literal, component))| {
                (
                    (cost, index),
                    (
                        candidate,
                        literal,
                        component,
                        true,
                        None::<crate::implied_guard::Inferred>,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut union_cache = None;
        let mut pending_inference = false;
        let mut release_inference = 0;
        // Only metadata waits in this bounded window, never cones or inferred
        // source snapshots. Reconstruct the selected candidate at the same graph
        // snapshot under the same budgets. Completed proofs still own their data.
        let mut ranked = BTreeMap::new();
        let mut remaining = LOOKAHEAD;
        let mut position = 0;
        let mut ranking = true;
        loop {
            *retained -= release_inference;
            release_inference = 0;
            let selected = ranking && (remaining == 0 || queue.is_empty());
            let entry = if selected {
                if let Some(((deferred, _, _, cost, index), value)) = ranked.pop_first() {
                    *retained -= RANK_STORAGE;
                    let (candidate, literal, component) = value;
                    Some((
                        (cost, index),
                        (candidate, literal, component, true, None),
                        Some(deferred),
                    ))
                } else if queue.is_empty() {
                    break;
                } else {
                    // Every preparation in the previous window failed locally.
                    remaining = LOOKAHEAD;
                    continue;
                }
            } else {
                queue.pop_first().map(|(key, value)| (key, value, None))
            };
            let Some((
                (cost, index),
                (candidate, literal, component, discover, mut inferred),
                deferred,
            )) = entry
            else {
                break;
            };
            release_inference = inferred
                .as_ref()
                .map_or(0, crate::implied_guard::Inferred::nodes);
            if inferred.is_some() && !selected {
                pending_inference = false;
            }
            if selected {
                remaining = LOOKAHEAD - ranked.len();
            }
            budget.tick("guarded candidate queue")?;
            if done.contains(&component.id)
                || attempts.reuse_negative(
                    &Attempt::GuardedSettlement(candidate.rule.id, literal.term.occurrence),
                    budget,
                    progress,
                )?
            {
                continue;
            }
            if discover {
                // At most one refined candidate waits in the queue. This prevents
                // global inference before the first proof. Others retain their
                // ordinary priority while that candidate awaits its turn.
                if !pending_inference || selected {
                    progress.rule(self, "implied-guard", candidate.rule.id, index + 1);
                    if let Some(result) = attempts.run(
                        Attempt::ImpliedGuard(candidate.rule.id),
                        &candidate.rule.head.atom,
                        self,
                        retained,
                        budget,
                        progress,
                        |retained, budget| {
                            crate::implied_guard::discover(
                                candidate,
                                summaries,
                                &producers,
                                union_cache.as_ref(),
                                ctx,
                                retained,
                                budget,
                            )
                        },
                    )? {
                        if result.cutoff {
                            progress.cutoff(AdmissionAttemptKind::ImpliedGuard);
                        }
                        if let Some(next) = result.union {
                            if let Some(old) = union_cache.replace(next) {
                                *retained -= old.nodes();
                            }
                        }
                        inferred = result.inferred;
                    }
                }
                let guard = inferred
                    .as_ref()
                    .map_or(&candidate.condition, |i| &i.condition);
                let actual = (guard.is_true(), guard.node_count(), cost.2);
                if !selected {
                    pending_inference |= inferred.is_some();
                    queue.insert(
                        (actual, index),
                        (candidate, literal, component, false, inferred),
                    );
                    continue;
                }
                release_inference = inferred
                    .as_ref()
                    .map_or(0, crate::implied_guard::Inferred::nodes);
            }
            if !selected && ranking {
                remaining -= 1;
            }
            let mut effective = candidate.clone();
            if let Some(i) = &inferred {
                effective.condition = i.condition.clone();
            }
            progress.guarded_start(
                self,
                index + 1,
                &candidate.rule,
                &literal.term.atom,
                deferred.unwrap_or(false),
            );
            let mut preprocessing = None;
            let mut preparation = Preparation::default();
            let before_preparation = *retained;
            let mut released_cache = 0;
            let prepared = attempts.run(
                Attempt::GuardedCone(candidate.rule.id, literal.term.occurrence),
                &candidate.rule.head.atom,
                self,
                retained,
                budget,
                progress,
                |retained, budget| {
                    let started = Instant::now();
                    let mut prepare = |retained: &mut usize,
                                       budget: &mut Budget<'_>,
                                       rank: bool| {
                        crate::guarded_bounds::prepare(
                            self,
                            component,
                            &effective,
                            &literal.term.atom,
                            summaries,
                            &producers,
                            ctx,
                            retained,
                            budget,
                            &mut preparation,
                        )
                        .and_then(|cone| {
                            if rank {
                                *retained =
                                    crate::symbolic::retain(*retained, 0, RANK_STORAGE, budget)?;
                            }
                            Ok(cone)
                        })
                    };
                    let mut result = prepare(retained, budget, ranking && !selected);
                    if matches!(
                        &result,
                        Err(CheckError::LimitExceeded {
                            phase: "symbolic storage",
                            resource: "condition nodes",
                            ..
                        })
                    ) {
                        released_cache = cache.take().map_or(0, |old| {
                            old.1
                                .as_ref()
                                .map_or_else(|| old.0.temporary_nodes(), |b| b.temporary_nodes())
                        }) + union_cache.take().map_or(0, |old| old.nodes());
                        let was_ranking = ranking;
                        // Ranking is optional too. Return waiting candidates to
                        // their original queue and retry without its metadata.
                        released_cache += ranked.len() * RANK_STORAGE;
                        for ((_, _, _, cost, index), (candidate, literal, component)) in
                            std::mem::take(&mut ranked)
                        {
                            queue
                                .insert((cost, index), (candidate, literal, component, true, None));
                        }
                        ranking = false;
                        if released_cache > 0 || was_ranking {
                            // The partial cone has dropped. Optional reuse must
                            // yield storage to the next attempt. Retry once; keep
                            // all work charges and enforce the same storage cap.
                            *retained = before_preparation - released_cache;
                            result = prepare(retained, budget, false);
                        }
                    }
                    preprocessing = Some(started.elapsed());
                    result
                },
            );
            if matches!(&prepared, Ok(None)) {
                // Attempts restored its entry baseline after a local failure;
                // the evicted cache is no longer part of that baseline.
                *retained -= released_cache;
            }
            progress.guarded_prepared(
                self,
                preprocessing.map(|_| &preparation),
                preprocessing.unwrap_or_default(),
                match &prepared {
                    Ok(Some(_)) if selected => "iterating",
                    Ok(Some(_)) => "ranked",
                    Ok(None) => "skipped",
                    Err(_) => "failed",
                },
            );
            let Some(cone) = prepared? else {
                if preprocessing.is_none() {
                    progress.guarded_end(self, Default::default(), true, "skipped");
                }
                continue;
            };
            if !selected && ranking {
                // Compare live atoms with all atoms in the candidate's current
                // unresolved SCC, not just the visited cone. Near-full cones are
                // deliberately deferred too (e.g. 621/622).
                let deferred = preparation.live_atoms.saturating_mul(10)
                    >= component.atoms.len().saturating_mul(9);
                progress.guarded_order(self, deferred, None, component.atoms.len());
                ranked.insert(
                    (
                        deferred,
                        preparation.live_atoms,
                        preparation.live_producers,
                        cost,
                        index,
                    ),
                    (candidate, literal, component),
                );
                *retained -= cone.temporary_nodes();
                continue;
            }
            position += 1;
            progress.guarded_order(
                self,
                deferred.unwrap_or(false),
                Some(position),
                component.atoms.len(),
            );
            // Lookahead may have skipped implied-guard discovery while another
            // candidate waited. Diagnose only the final guard used for bounds,
            // never an earlier preview of this same rule/occurrence/snapshot.
            progress.candidate_probe(self, &cone, ctx, &effective, literal, budget)?;
            let reused = match &cache {
                Some((old, _)) => cone.same_computation(old, budget)?,
                None => false,
            };
            let mut iteration = None;
            progress.rule(self, "guarded-bounds", candidate.rule.id, 0);
            if reused {
                *retained -= cone.temporary_nodes(); // equivalent key is unnecessary
                if cache.as_ref().unwrap().1.is_some() {
                    progress.reused_result(AdmissionAttemptKind::GuardedBounds);
                } else {
                    progress.reused(AdmissionAttemptKind::GuardedBounds, true);
                }
            } else {
                if let Some((old, bounds)) = cache.take() {
                    *retained -= bounds
                        .as_ref()
                        .map_or_else(|| old.temporary_nodes(), |b| b.temporary_nodes());
                }
                let observe = |iteration| progress.iteration(self, iteration);
                let result = attempts.run(
                    Attempt::GuardedBounds(candidate.rule.id, literal.term.occurrence),
                    &candidate.rule.head.atom,
                    self,
                    retained,
                    budget,
                    progress,
                    |retained, budget| {
                        let started = Instant::now();
                        let result = crate::guarded_bounds::compute(
                            &cone,
                            ctx,
                            retained,
                            budget,
                            progress.enabled().then_some(&observe),
                        );
                        iteration = Some(started.elapsed());
                        result
                    },
                );
                if result.is_err() {
                    progress.guarded_end(self, iteration.unwrap_or_default(), false, "failed");
                }
                cache = Some((cone, result?));
            }
            let bounds = cache.as_ref().unwrap().1.as_ref();
            progress.guarded_end(
                self,
                iteration.unwrap_or_default(),
                reused || iteration.is_none(),
                if bounds.is_some() {
                    "completed"
                } else {
                    "skipped"
                },
            );
            let Some(bounds) = bounds else {
                continue;
            };
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
                            candidate,
                            literal,
                            meaning,
                            bounds,
                            inferred.as_ref(),
                            retained,
                            budget,
                            progress,
                        )
                    },
                )?
                .flatten();
            if let Some(proof) = proof {
                done.insert(component.id);
                proofs.push(proof);
            }
        }
        *retained -= release_inference + ranked.len() * RANK_STORAGE;
        if let Some(union) = union_cache {
            *retained -= union.nodes();
        }
        if let Some((cone, bounds)) = cache {
            *retained -= bounds
                .as_ref()
                .map_or_else(|| cone.temporary_nodes(), |b| b.temporary_nodes());
        }
        Ok(proofs)
    }

    pub(crate) fn settle_guarded(
        &self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        meaning: &SymbolicMeaning<'_>,
        bounds: &Arc<BorrowedBounds<'_>>,
        implied: Option<&crate::implied_guard::Inferred>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<GuardedSettlementProof>> {
        let baseline = *retained;
        let ctx = meaning.context();
        let guard = implied.map_or(&candidate.condition, |i| &i.condition);
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
        for p in &bounds.cone.producers {
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
                    if !producer.live {
                        continue;
                    }
                    if producer.rule.id == candidate.rule.id {
                        exact = false;
                        break;
                    }
                    let mut body = crate::upper_bounds::scoped_condition(
                        &producer.condition,
                        true,
                        Some(&bounds.cone.domain),
                        ctx,
                        budget,
                    )?;
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
                                // A surrounding negation can flip this leaf's
                                // polarity. Preserve static truth directly so an
                                // impossible atom never becomes a positive edge
                                // in the sparse executable dependency graph.
                                if v.is_true() {
                                    constant(true)
                                } else if v.is_false() {
                                    constant(false)
                                } else {
                                    Arc::new(SettledExpression::Atom(premise.term.atom.clone()))
                                },
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
        let expression = match implied {
            Some(i) => join(vec![Arc::clone(&i.proof.expression), expression], true),
            None => expression,
        };
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
            .map(|p| p.summary.clone())
            .collect();
        budget.charge(
            candidate.rule.body.len() + expression_nodes + bounds.cone.producers.len(),
            "guarded proof storage",
        )?;
        *retained = baseline;
        let owned_bounds = bounds.owned(budget)?;
        let proof = GuardedSettlementProof {
            proof: SymbolicRewriteProof {
                candidate: candidate.clone(),
                producers: covering,
                coverage,
                upper_bounds: None,
            },
            bounds: owned_bounds,
            occurrence: literal.term.occurrence,
            replacement: expression,
            steps,
            implied_guard: implied.map(|i| i.proof.clone()),
        };
        // Retained certificate accounting is conservative, as for other rewrites.
        *retained = crate::symbolic::retain(
            *retained,
            0,
            proof
                .implied_guard
                .as_ref()
                .map_or(0, ImpliedGuardProof::nodes)
                + proof.bounds.nodes()
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
