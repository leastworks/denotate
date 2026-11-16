//! Guard-relative settlement in upstream-first component turns, ranked within
//! each component. A candidate is relaxed before bounds
//! are computed and cannot supply a live settling producer for its own proof.
use crate::{
    admission_skips::{Attempt, Attempts},
    guarded_bounds::{BorrowedBounds, BorrowedCone, Preparation},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, or};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
    time::Instant,
};

mod certificate;
pub use certificate::GuardedCertificate;
use certificate::Settlement;
mod cases;

// Optimization cutoffs: no rewrite is installed when a complete certificate does
// not fit. Global work/BDD/dependency limits remain independent.
pub(crate) const EXPRESSION_NODES: usize = 1024;
pub(crate) const EXPRESSION_DEPTH: usize = 64;
pub(crate) const CERTIFICATE_NODES: usize = 8192;
// Provisional scheduling only; neither the cone nor its certificate changes.
const LOOKAHEAD: usize = 32;
// Scheduling turns, not an operation limit. A lone component can continue;
// otherwise four bounds candidates give way to the next upstream-ordered queue.
pub(crate) const BOUNDS_PER_TURN: usize = 4;
const RANK_STORAGE: usize = 16;
// Extra discovery/preparation work after an all-deferred window, per snapshot.
// Finish the current queue operation before testing this scheduling allowance;
// never turn it into a failed proof or a checker exhaustion.

struct Lookahead {
    work: usize,
    limit: usize,
    since: Option<usize>,
}
impl Lookahead {
    fn used(&self, budget: &Budget<'_>) -> usize {
        self.work + self.since.map_or(0, |start| budget.used() - start)
    }
    fn finish(&mut self, budget: &Budget<'_>) {
        self.work = self.used(budget);
        self.since = None;
    }
}

type Cost = (bool, usize, usize);
type Candidate<'a> = (&'a ProducerSummary, &'a GroundLiteral, &'a Component);
struct ComponentQueue<'a> {
    // Only borrowed candidates, charged ranking metadata and at most one inferred
    // guard per component. Prepared descriptors remain in Attempts; temporary
    // bounds still share just one cache entry across all components.
    queue: BTreeMap<
        (Cost, usize),
        (
            &'a ProducerSummary,
            &'a GroundLiteral,
            &'a Component,
            bool,
            Option<crate::implied_guard::Inferred>,
        ),
    >,
    ranked: BTreeMap<(bool, usize, usize, Cost, usize), Candidate<'a>>,
    remaining: usize,
    ranking: bool,
    pending_inference: bool,
}
impl ComponentQueue<'_> {
    fn new() -> Self {
        Self {
            queue: BTreeMap::new(),
            ranked: BTreeMap::new(),
            remaining: LOOKAHEAD,
            ranking: true,
            pending_inference: false,
        }
    }
    fn nodes(&self) -> usize {
        self.ranked.len() * RANK_STORAGE
            + self
                .queue
                .values()
                .filter_map(|(_, _, _, _, inferred)| inferred.as_ref())
                .map(crate::implied_guard::Inferred::nodes)
                .sum::<usize>()
    }
    fn release_optional(&mut self) -> usize {
        let mut nodes = self.ranked.len() * RANK_STORAGE;
        for ((_, _, _, cost, index), (candidate, literal, component)) in
            std::mem::take(&mut self.ranked)
        {
            self.queue
                .insert((cost, index), (candidate, literal, component, true, None));
        }
        // A waiting inferred guard is optional too. Keep the candidate and
        // rediscover its guard when resumed. At most one is queued per component;
        // scan only when that flag is set, then clear it before another eviction.
        if self.pending_inference {
            for (_, _, _, discover, inferred) in self.queue.values_mut() {
                if let Some(value) = inferred.take() {
                    nodes += value.nodes();
                    drop(value);
                    *discover = true;
                    break;
                }
            }
        }
        self.pending_inference = false;
        self.ranking = false;
        nodes
    }
}

#[derive(Debug, Clone)]
pub struct GuardedSettlementStep {
    pub atom: GroundAtom,
    pub expression: Arc<SettledExpression<GroundAtom>>,
    pub producers: Vec<GroundRuleId>,
    pub false_by_bound: bool,
    pub true_by_guarantee: bool,
}

#[derive(Debug, Clone)]
pub struct GuardedSettlementProof {
    pub proof: SymbolicRewriteProof,
    pub certificate: GuardedCertificate,
    pub occurrence: denotate_ir::OccurrenceId,
    pub replacement: Arc<SettledExpression<GroundAtom>>,
    pub implied_guard: Option<ImpliedGuardProof>,
}

impl GuardedSettlementProof {
    pub(crate) fn nodes(&self) -> usize {
        self.certificate.nodes()
            + self
                .implied_guard
                .as_ref()
                .map_or(0, ImpliedGuardProof::nodes)
            + self.proof.candidate.nodes()
            + self.proof.coverage.node_count()
            + self
                .proof
                .producers
                .iter()
                .map(ProducerSummary::nodes)
                .sum::<usize>()
    }
}

/// The symmetric check lets certificates be applied sequentially in any order.
/// Dead producers and transitive pruning/implied sources are dependencies too.
#[derive(Default)]
struct IndependentBatch {
    rules: BTreeSet<GroundRuleId>,
    dependencies: BTreeSet<GroundRuleId>,
}
impl IndependentBatch {
    fn reads(&self, rule: GroundRuleId) -> bool {
        self.rules.contains(&rule) || self.dependencies.contains(&rule)
    }
    fn accepts(&self, rule: GroundRuleId, dependencies: &BTreeSet<GroundRuleId>) -> bool {
        !self.reads(rule) && self.rules.is_disjoint(dependencies)
    }
    fn insert(&mut self, rule: GroundRuleId, dependencies: BTreeSet<GroundRuleId>) {
        self.rules.insert(rule);
        self.dependencies.extend(dependencies);
    }
}

pub(crate) fn dependencies<S: std::ops::Deref<Target = ProducerSummary>>(
    candidate: &ProducerSummary,
    cone: &GuardedCone<S>,
    implied: Option<&ImpliedGuardProof>,
    budget: &mut Budget<'_>,
) -> Result<BTreeSet<GroundRuleId>> {
    let mut dependencies = BTreeSet::from([candidate.rule.id]);
    for source in cone
        .summaries()
        .chain(implied.into_iter().flat_map(ImpliedGuardProof::summaries))
    {
        budget.tick("guarded proof dependencies")?;
        dependencies.insert(source.rule.id);
    }
    Ok(dependencies)
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
        let mut batch = IndependentBatch::default();
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
        let mut cache_reason = None; // diagnostic cause travels with a reused skipped result
        let mut queues = BTreeMap::new();
        for (index, (cost, candidate, literal, component)) in candidates.into_iter().enumerate() {
            queues
                .entry(component.id)
                .or_insert_with(ComponentQueue::new)
                .queue
                .insert((cost, index), (candidate, literal, component, true, None));
        }
        let order = crate::admission_scope::component_order(
            self,
            &queues.keys().copied().collect(),
            budget,
        )?;
        let mut turns: VecDeque<_> = order
            .into_iter()
            .map(|id| queues.remove(&id).unwrap())
            .collect();
        let mut union_cache = None;
        let mut position = 0;
        let mut lookahead = Lookahead {
            work: 0,
            limit: budget.limits.max_work / 10,
            since: None,
        };
        #[cfg(test)]
        if let Some(limit) = attempts.lookahead_work {
            lookahead.limit = limit;
        }
        while let Some(ComponentQueue {
            mut queue,
            mut ranked,
            mut remaining,
            mut ranking,
            mut pending_inference,
        }) = turns.pop_front()
        {
            let mut turn_attempts = 0;
            let mut release_inference = 0;
            loop {
                *retained -= release_inference;
                release_inference = 0;
                lookahead.finish(budget);
                progress.guarded_lookahead(lookahead.work, lookahead.limit);
                if turn_attempts >= BOUNDS_PER_TURN && !turns.is_empty() {
                    break;
                }
                let useful = ranked
                    .first_key_value()
                    .is_some_and(|((deferred, _, _, _, _), _)| !deferred);
                let extend = ranking
                    && remaining == 0
                    && !useful
                    && !queue.is_empty()
                    && lookahead.work < lookahead.limit;
                lookahead.since = extend.then(|| budget.used());
                let selected = ranking && ((!extend && remaining == 0) || queue.is_empty());
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
                    remaining = LOOKAHEAD.saturating_sub(ranked.len());
                }
                budget.tick("guarded candidate queue")?;
                #[cfg(test)]
                if !attempts.batch_guarded
                    && proofs.iter().any(|p: &GuardedSettlementProof| {
                        p.certificate
                            .bounds()
                            .any(|b| b.cone.component == component.id)
                    })
                {
                    continue;
                }
                if batch.reads(candidate.rule.id)
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
                    remaining = remaining.saturating_sub(1);
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
                    (lookahead.used(budget), lookahead.limit),
                );
                let mut preprocessing = None;
                let mut preparation = Preparation::default();
                let before_preparation = *retained;
                let mut released_cache = 0;
                let cone_key = Attempt::GuardedCone(candidate.rule.id, literal.term.occurrence);
                budget.tick("guarded descriptor lookup")?;
                let mut saved = std::mem::take(&mut attempts.prepared);
                let mut reused_preparation = false;
                let reuse = if let Some(old) = saved.get(&cone_key) {
                    let bound = old
                        .bind(
                            self,
                            &effective.condition,
                            &ctx.permitted_worlds(),
                            summaries,
                            retained,
                            budget,
                        )
                        .and_then(|cone| {
                            if cone.is_some() && ranking && !selected {
                                *retained =
                                    crate::symbolic::retain(*retained, 0, RANK_STORAGE, budget)?;
                            }
                            Ok(cone)
                        });
                    match bound {
                        Ok(Some(cone)) => {
                            preparation = old.stats.clone();
                            preparation.existing_nodes = before_preparation;
                            preparation.added_nodes = cone.temporary_nodes();
                            reused_preparation = true;
                            progress.reused_result(AdmissionAttemptKind::GuardedPreprocessing);
                            Some(cone)
                        }
                        Ok(None) => None,
                        Err(CheckError::LimitExceeded {
                            phase: "symbolic storage",
                            resource: "condition nodes",
                            ..
                        }) => {
                            released_cache += saved.values().map(|c| c.nodes()).sum::<usize>();
                            saved.clear();
                            *retained = before_preparation - released_cache;
                            None
                        }
                        Err(e) => return Err(e),
                    }
                } else {
                    None
                };
                // A miss evicts the obsolete descriptor before preparing its replacement.
                if !reused_preparation {
                    if let Some(old) = saved.remove(&cone_key) {
                        released_cache += old.nodes();
                        *retained -= old.nodes();
                    }
                }
                let attempt_baseline = *retained;
                let previously_released = released_cache;
                let prepared = if let Some(cone) = reuse {
                    Ok(Some(cone))
                } else {
                    attempts.run(
                        cone_key.clone(),
                        &candidate.rule.head.atom,
                        self,
                        retained,
                        budget,
                        progress,
                        |retained, budget| {
                            let started = Instant::now();
                            let mut prepare =
                                |retained: &mut usize, budget: &mut Budget<'_>, rank: bool| {
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
                                            *retained = crate::symbolic::retain(
                                                *retained,
                                                0,
                                                RANK_STORAGE,
                                                budget,
                                            )?;
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
                                released_cache +=
                                    cache.take().map_or(0, |old| {
                                        old.1.as_ref().map_or_else(
                                            || old.0.temporary_nodes(),
                                            |b| b.temporary_nodes(),
                                        )
                                    }) + union_cache.take().map_or(0, |old| old.nodes());
                                released_cache += saved.values().map(|c| c.nodes()).sum::<usize>();
                                saved.clear();
                                // Waiting components' optional ranks and guards must
                                // yield storage too, without losing their candidates.
                                for waiting in &mut turns {
                                    released_cache += waiting.release_optional();
                                }
                                let was_ranking = ranking;
                                // Ranking is optional too. Return waiting candidates to
                                // their original queue and retry without its metadata.
                                released_cache += ranked.len() * RANK_STORAGE;
                                for ((_, _, _, cost, index), (candidate, literal, component)) in
                                    std::mem::take(&mut ranked)
                                {
                                    queue.insert(
                                        (cost, index),
                                        (candidate, literal, component, true, None),
                                    );
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
                    )
                };
                attempts.prepared = saved;
                if matches!(&prepared, Ok(None)) {
                    // Attempts restored its entry baseline after a local failure;
                    // the evicted cache is no longer part of that baseline.
                    *retained = attempt_baseline - (released_cache - previously_released);
                }
                progress.guarded_lookahead(lookahead.used(budget), lookahead.limit);
                progress.guarded_prepared(
                    self,
                    (preprocessing.is_some() || reused_preparation).then_some(&preparation),
                    preprocessing.unwrap_or_default(),
                    match &prepared {
                        Ok(Some(_)) if selected => "iterating",
                        Ok(Some(_)) => "ranked",
                        Ok(None) => "skipped",
                        Err(_) => "failed",
                    },
                );
                if !matches!(&prepared, Ok(Some(_))) {
                    let reason = attempts.reason(&Attempt::GuardedCone(
                        candidate.rule.id,
                        literal.term.occurrence,
                    ));
                    budget.excluding_time(|| {
                        self.dump(
                            progress.dump,
                            AdmissionDumpEvent::GuardedOutcome {
                                rule: candidate.rule.id,
                                occurrence: literal.term.occurrence,
                                stage: "preparation",
                                state: if prepared.is_err() {
                                    "failed"
                                } else {
                                    "skipped"
                                },
                                reason,
                            },
                        )
                    });
                }
                let Some(cone) = prepared? else {
                    if preprocessing.is_none() {
                        progress.guarded_end(self, Default::default(), true, "skipped");
                    }
                    continue;
                };
                let dependencies = dependencies(
                    candidate,
                    &cone,
                    inferred.as_ref().map(|i| &i.proof),
                    budget,
                )?;
                budget.charge(
                    dependencies.len() + batch.rules.len(),
                    "guarded batch independence",
                )?;
                if !batch.accepts(candidate.rule.id, &dependencies) {
                    *retained -= cone.temporary_nodes()
                        + if ranking && !selected {
                            RANK_STORAGE
                        } else {
                            0
                        };
                    continue;
                }
                // A cached negative also depends on unsuccessful guard discovery.
                // A producer ignored today (e.g. non-exact for a negative premise)
                // can supply a stronger guard after a later rewrite. Keep all these
                // one-hop inputs, not only the sources of a successful inference.
                let mut retry_dependencies = dependencies.clone();
                for premise in &candidate.rule.body {
                    for id in producers.get(&premise.term.atom).into_iter().flatten() {
                        budget.tick("guarded inference retry inputs")?;
                        retry_dependencies.insert(*id);
                    }
                }
                attempts.remember_dependencies(
                    candidate.rule.id,
                    literal.term.occurrence,
                    retry_dependencies.clone(),
                    retained,
                    budget,
                )?;
                if !reused_preparation {
                    attempts.keep_prepared(
                        cone_key,
                        crate::guarded_preparation::PreparedCone::capture(
                            &candidate.rule.head.atom,
                            &cone,
                            &effective.condition,
                            ctx.permitted_worlds(),
                            &preparation,
                        ),
                        retained,
                        budget,
                    )?;
                }
                if !selected && ranking {
                    // Compare live atoms with all atoms in the candidate's current
                    // unresolved SCC, not just the visited cone. Near-full cones are
                    // deliberately deferred too (e.g. 621/622).
                    let deferred = preparation.live_atoms.saturating_mul(10)
                        >= component.atoms.len().saturating_mul(9);
                    progress.guarded_lookahead(lookahead.used(budget), lookahead.limit);
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
                // Storage pressure may have disabled ranking in this operation.
                // Stop charging lookahead before its immediate bounds fallback too.
                lookahead.finish(budget);
                progress.guarded_lookahead(lookahead.work, lookahead.limit);
                position += 1;
                turn_attempts += 1;
                progress.guarded_order(
                    self,
                    deferred.unwrap_or(false),
                    Some(position),
                    component.atoms.len(),
                );
                // Lookahead may have skipped implied-guard discovery while another
                // candidate waited. Diagnose only the final guard used for bounds,
                // never an earlier preview of this same rule/occurrence/snapshot.
                budget.excluding_time(|| {
                    self.dump(
                        progress.dump,
                        AdmissionDumpEvent::Guarded {
                            candidate,
                            literal,
                            cone: &cone,
                            implied: inferred.as_ref().map(|i| &i.proof),
                            before_atoms: preparation.before_atoms,
                            before_rules: preparation.before_producers,
                            pruning: preparation.pruning,
                        },
                    )
                });
                progress.dump_cutoff.set(false);
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
                        budget.excluding_time(|| {
                            self.dump(
                                progress.dump,
                                AdmissionDumpEvent::GuardedOutcome {
                                    rule: candidate.rule.id,
                                    occurrence: literal.term.occurrence,
                                    stage: "bounds",
                                    state: "failed",
                                    reason: None,
                                },
                            )
                        });
                    }
                    if progress.dump.is_some() {
                        cache_reason = attempts.reason(&Attempt::GuardedBounds(
                            candidate.rule.id,
                            literal.term.occurrence,
                        ));
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
                if bounds.is_none() {
                    let reason = attempts
                        .reason(&Attempt::GuardedBounds(
                            candidate.rule.id,
                            literal.term.occurrence,
                        ))
                        .or(cache_reason);
                    budget.excluding_time(|| {
                        self.dump(
                            progress.dump,
                            AdmissionDumpEvent::GuardedOutcome {
                                rule: candidate.rule.id,
                                occurrence: literal.term.occurrence,
                                stage: "bounds",
                                state: "skipped",
                                reason,
                            },
                        )
                    });
                }
                progress.rule(self, "guarded-settlement", candidate.rule.id, 0);
                let mut released_cache = 0;
                let proof = attempts.proof(
                    Attempt::GuardedSettlement(candidate.rule.id, literal.term.occurrence),
                    &candidate.rule.head.atom,
                    self,
                    retained,
                    budget,
                    progress,
                    Option::is_none,
                    |retained, budget| {
                        if let Some(bounds) = cache.as_ref().and_then(|(_, b)| b.as_ref()) {
                            if let Some(proof) = self.settle_guarded(
                                candidate,
                                literal,
                                meaning,
                                bounds,
                                inferred.as_ref(),
                                retained,
                                budget,
                                progress,
                            )? {
                                return Ok(Some(proof));
                            }
                        }
                        // If every settled producer condition is fixed by this
                        // domain, no split can change the graph. Keep the optional
                        // bounds reusable instead of allocating a scoring graph.
                        let mut varying = false;
                        let domain = &cache.as_ref().unwrap().0.domain;
                        for index in &self.component_rules[component.id.index] {
                            budget.tick("case split eligibility")?;
                            if let Some(s) = summaries.get(&self.rules[*index].id) {
                                if !s.condition.is_true()
                                    && !s.condition.is_false()
                                    && !ctx.apply(domain, &s.condition, and, budget)?.is_false()
                                    && !ctx
                                        .apply(
                                            domain,
                                            &s.condition,
                                            biodivine_lib_bdd::op_function::and_not,
                                            budget,
                                        )?
                                        .is_false()
                                {
                                    varying = true;
                                    break;
                                }
                            }
                        }
                        if !varying {
                            return Ok(None);
                        }
                        // Release the broad domain's optional bounds before narrower
                        // branches: it must not consume the space they could fit in.
                        if let Some((cone, bounds)) = cache.take() {
                            released_cache = bounds
                                .as_ref()
                                .map_or_else(|| cone.temporary_nodes(), |b| b.temporary_nodes());
                            *retained -= released_cache;
                        }
                        self.case_settlement(
                            candidate,
                            literal,
                            component,
                            meaning,
                            summaries,
                            &producers,
                            inferred.as_ref(),
                            &mut retry_dependencies,
                            cases::CaseLimits::default(),
                            retained,
                            budget,
                            progress,
                        )
                    },
                );
                if matches!(proof, Ok(None)) {
                    // Local failure restored the attempt's initial accounting,
                    // but the optional broad-domain cache was actually released.
                    *retained -= released_cache;
                }
                let reason = attempts.reason(&Attempt::GuardedSettlement(
                    candidate.rule.id,
                    literal.term.occurrence,
                ));
                let state = match &proof {
                    Err(_) => "failed",
                    Ok(None) => "skipped",
                    Ok(Some(Some(_))) => "settled",
                    Ok(Some(None)) if progress.dump_cutoff.get() => "certificate-cutoff",
                    Ok(Some(None)) => "negative",
                };
                budget.excluding_time(|| {
                    self.dump(
                        progress.dump,
                        AdmissionDumpEvent::GuardedOutcome {
                            rule: candidate.rule.id,
                            occurrence: literal.term.occurrence,
                            stage: "settlement",
                            state,
                            reason,
                        },
                    )
                });
                let proof = proof?.flatten();
                attempts.remember_dependencies(
                    candidate.rule.id,
                    literal.term.occurrence,
                    retry_dependencies,
                    retained,
                    budget,
                )?;
                if let Some(proof) = proof {
                    let mut complete = dependencies;
                    for source in proof.certificate.summaries() {
                        budget.tick("case certificate dependencies")?;
                        complete.insert(source.rule.id);
                    }
                    budget.charge(
                        complete.len() + batch.rules.len(),
                        "guarded batch independence",
                    )?;
                    if batch.accepts(candidate.rule.id, &complete) {
                        batch.insert(candidate.rule.id, complete);
                        proofs.push(proof);
                    } else {
                        *retained -= proof.nodes();
                    }
                }
            }
            *retained -= release_inference;
            let state = ComponentQueue {
                queue,
                ranked,
                remaining,
                ranking,
                pending_inference,
            };
            if !proofs.is_empty() {
                // Commit before another component's preparation or proof can exhaust.
                // Drop all queued conditions/metadata before releasing their charges.
                let nodes = state.nodes() + turns.iter().map(ComponentQueue::nodes).sum::<usize>();
                drop(state);
                turns.clear();
                *retained -= nodes;
                break;
            }
            if !state.queue.is_empty() || !state.ranked.is_empty() {
                turns.push_back(state);
            }
        }
        if let Some(union) = union_cache {
            *retained -= union.nodes();
        }
        if let Some((cone, bounds)) = cache {
            *retained -= bounds
                .as_ref()
                .map_or_else(|| cone.temporary_nodes(), |b| b.temporary_nodes());
        }
        *retained -= attempts.prune_dependencies();
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
        let guard = implied.map_or(&candidate.condition, |i| &i.condition);
        let Some(settled) = self.settle_guarded_leaf(
            candidate, literal, meaning, bounds, guard, false, retained, budget, progress,
        )?
        else {
            return Ok(None);
        };
        self.finish_guarded(
            candidate, literal, meaning, implied, settled, retained, budget, progress,
        )
    }

    fn settle_guarded_leaf(
        &self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        meaning: &SymbolicMeaning<'_>,
        bounds: &Arc<BorrowedBounds<'_>>,
        guard: &Condition,
        allow_constant: bool,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<Settlement>> {
        let baseline = *retained;
        let ctx = meaning.context();
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
                    true_by_guarantee: false,
                });
                *retained = crate::symbolic::retain(
                    *retained,
                    0,
                    ctx.false_condition().node_count(),
                    budget,
                )?;
            }
        }
        if allow_constant {
            for (atom, guarantee) in &bounds.guarantees {
                budget.tick("case branch exact guarantee")?;
                if marks.contains_key(atom)
                    || !ctx
                        .apply(
                            &bounds.cone.domain,
                            guarantee,
                            biodivine_lib_bdd::op_function::and_not,
                            budget,
                        )?
                        .is_false()
                {
                    continue;
                }
                expression_nodes += 1;
                if expression_nodes > CERTIFICATE_NODES {
                    cutoff(progress);
                    *retained = baseline;
                    return Ok(None);
                }
                let mut producers = Vec::new();
                for p in &bounds.cone.producers {
                    budget.tick("case branch guarantee source")?;
                    if p.rule.head.atom == *atom
                        && p.live
                        && p.exact
                        && p.rule.id != candidate.rule.id
                    {
                        producers.push(p.rule.id);
                    }
                }
                // These lower bounds contain exact producers only. The relaxed
                // reader is excluded, so this true seed cannot justify itself.
                marks.insert(atom.clone(), (constant(true), bounds.cone.domain.clone()));
                steps.push(GuardedSettlementStep {
                    atom: atom.clone(),
                    expression: constant(true),
                    producers,
                    false_by_bound: false,
                    true_by_guarantee: true,
                });
                *retained =
                    crate::symbolic::retain(*retained, 0, bounds.cone.domain.node_count(), budget)?;
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
                        true_by_guarantee: false,
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
        if !allow_constant && (yes.is_false() || no.is_false()) {
            *retained = baseline;
            return Ok(None);
        }
        let expression = if yes.is_false() {
            constant(false)
        } else if no.is_false() {
            constant(true)
        } else {
            Arc::clone(expression)
        };
        let truth = truth.clone();
        budget.charge(
            expression_nodes + bounds.cone.producers.len(),
            "guarded proof storage",
        )?;
        let certificate = GuardedCertificate::Leaf {
            bounds: bounds.owned(budget)?,
            steps,
        };
        let result = Settlement {
            expression,
            truth,
            certificate,
        };
        *retained = crate::symbolic::retain(baseline, 0, result.nodes(), budget)?;
        Ok(Some(result))
    }

    fn finish_guarded(
        &self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        meaning: &SymbolicMeaning<'_>,
        implied: Option<&crate::implied_guard::Inferred>,
        settled: Settlement,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<GuardedSettlementProof>> {
        let baseline = *retained - settled.nodes();
        let ctx = meaning.context();
        let guard = implied.map_or(&candidate.condition, |i| &i.condition);
        // Ordinary leaves already applied this policy before retaining evidence.
        if !matches!(settled.certificate, GuardedCertificate::Leaf { .. }) {
            let yes = ctx.restrict(&ctx.apply(guard, &settled.truth, and, budget)?, budget)?;
            let no = ctx.restrict(
                &ctx.apply(guard, &ctx.complement(&settled.truth, budget)?, and, budget)?,
                budget,
            )?;
            // Constant leaves are useful; a constant complete result keeps the
            // existing removal/discharge install policy.
            if yes.is_false() || no.is_false() {
                *retained = baseline;
                return Ok(None);
            }
        }
        let expression = signed(settled.expression, literal.polarity == Polarity::Negative);
        let expression = match implied {
            Some(i) => join(vec![Arc::clone(&i.proof.expression), expression], true),
            None => expression,
        };
        if !bounded(&expression, budget)?
            || settled.certificate.expression_nodes() > CERTIFICATE_NODES
        {
            progress.cutoff(AdmissionAttemptKind::GuardedSettlement);
            *retained = baseline;
            return Ok(None);
        }
        let coverage = if literal.polarity == Polarity::Negative {
            ctx.complement(&settled.truth, budget)?
        } else {
            settled.truth
        };
        let mut covering = BTreeMap::new();
        for source in settled.certificate.summaries() {
            budget.tick("guarded direct evidence")?;
            if source.rule.head.atom == literal.term.atom {
                covering
                    .entry(source.rule.id)
                    .or_insert_with(|| source.clone());
            }
        }
        budget.charge(candidate.rule.body.len(), "guarded proof storage")?;
        let proof = GuardedSettlementProof {
            proof: SymbolicRewriteProof {
                candidate: candidate.clone(),
                producers: covering.into_values().collect(),
                coverage,
                upper_bounds: None,
            },
            certificate: settled.certificate,
            occurrence: literal.term.occurrence,
            replacement: expression,
            implied_guard: implied.map(|i| i.proof.clone()),
        };
        *retained = crate::symbolic::retain(baseline, 0, proof.nodes(), budget)?;
        Ok(Some(proof))
    }
}

#[cfg(test)]
mod batch_tests {
    use super::*;
    use crate::test_support::rewrites::{rel, rule, summaries};

    #[test]
    fn complete_dependencies_reject_both_batch_orders_including_pruned_and_implied_sources() {
        let mut c = denotate_ir::Corpus::new();
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        rule(&mut c, a, &[(b, true)]);
        rule(&mut c, b, &[(a, true)]);
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let m = p.symbolic(&l).unwrap();
        let all = summaries(&p, &m, &l);
        let mut values = all.values();
        let candidate = values.next().unwrap();
        let source = values.next().unwrap();
        for role in ["live", "dead", "pruned", "implied"] {
            let mut cone = GuardedCone {
                component: p.component_for(&candidate.rule.head.atom).unwrap().id,
                snapshot: p.graph_revision,
                domain: m.context().true_condition(),
                relaxed_rule: None,
                atoms: vec![source.rule.head.atom.clone()],
                producers: vec![],
                pruning: crate::guarded_bounds::Pruning::default(),
            };
            let mut implied = None;
            match role {
                "live" | "dead" => cone.producers.push(crate::guarded_bounds::GuardedProducer {
                    summary: source,
                    live: role == "live",
                }),
                "pruned" => cone.pruning.sources.push(source),
                "implied" => {
                    implied = Some(ImpliedGuardProof {
                        expression: constant(true),
                        premises: vec![ImpliedGuardPremise {
                            literal: candidate.rule.body[0].clone(),
                            producers: vec![Arc::new(source.clone())],
                        }],
                    })
                }
                _ => unreachable!(),
            }
            let deps =
                dependencies(candidate, &cone, implied.as_ref(), &mut Budget::new(&l)).unwrap();
            assert!(deps.contains(&source.rule.id), "{role}");
            let mut batch = IndependentBatch::default();
            batch.insert(source.rule.id, BTreeSet::new());
            assert!(!batch.accepts(candidate.rule.id, &deps), "{role}");
            let mut batch = IndependentBatch::default();
            batch.insert(candidate.rule.id, deps);
            assert!(!batch.accepts(source.rule.id, &BTreeSet::new()), "{role}");
            assert!(
                !batch.accepts(candidate.rule.id, &BTreeSet::new()),
                "one replacement per rule"
            );
        }
    }
}

#[cfg(test)]
mod queue_tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule, summaries};
    use denotate_ir::Corpus;

    #[test]
    fn evicted_waiting_guard_is_reconstructed_without_losing_its_candidate() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let a = rel(&mut c, "a", false);
        let b = rel(&mut c, "b", false);
        let source = rule(&mut c, a, &[(b, true)]);
        rule(&mut c, b, &[(x, false)]);
        rule(&mut c, b, &[(a, true)]);
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let m = p.symbolic(&l).unwrap();
        let summaries = summaries(&p, &m, &l);
        let candidate = summaries
            .values()
            .find(|s| s.rule.source == source)
            .unwrap();
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        for s in summaries.values() {
            producers
                .entry(&s.rule.head.atom)
                .or_default()
                .push(s.rule.id);
        }
        let mut retained = 0;
        let mut budget = Budget::new(&l);
        let mut discovered = crate::implied_guard::discover(
            candidate,
            &summaries,
            &producers,
            None,
            m.context(),
            &mut retained,
            &mut budget,
        )
        .unwrap();
        if let Some(union) = discovered.union.take() {
            let nodes = union.nodes();
            drop(union);
            retained -= nodes;
        }
        let inferred = discovered.inferred.take().expect("a requires !x");
        let worlds = [vec![], vec![atom(x)]];
        let observations = |guard: &Condition| {
            worlds
                .iter()
                .map(|w| m.context().evaluate(guard, w.iter().cloned(), &l).unwrap())
                .collect::<Vec<_>>()
        };
        assert_eq!(observations(&inferred.condition), [true, false]);
        let key = ((false, inferred.condition.node_count(), 2), 0);
        let mut waiting = ComponentQueue::new();
        waiting.queue.insert(
            key,
            (
                candidate,
                &candidate.rule.body[0],
                p.component_for(&atom(a)).unwrap(),
                false,
                Some(inferred),
            ),
        );
        waiting.pending_inference = true;
        retained -= waiting.release_optional();
        assert_eq!(retained, 0, "only the saved guard owned these charges");
        assert_eq!(waiting.nodes(), 0);
        let (candidate, _, _, discover, saved) = waiting.queue.get(&key).unwrap();
        assert!(*discover && saved.is_none());
        let restored = crate::implied_guard::discover(
            candidate,
            &summaries,
            &producers,
            None,
            m.context(),
            &mut retained,
            &mut budget,
        )
        .unwrap();
        assert_eq!(
            observations(&restored.inferred.unwrap().condition),
            [true, false]
        );
    }
}
