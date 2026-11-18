//! One certificate for an entire component, evaluated on the original graph.
//! Partitions choose an acyclic order; no candidate relaxation or bounds enter it.
use crate::{
    admission_progress::AdmissionReporter,
    guarded_bounds::{BorrowedCone, component_cone},
    guarded_settlement::cases::{cyclic_size, recoverable},
    guarded_settlement::{Expr, constant, join, signed},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, and_not, or};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

mod cones;
mod expressions;
mod sizes;
use cones::{Cones, ScoredCone};
use expressions::Expressions;

// Scoring is cooperative at complete candidate boundaries. One candidate can
// cross this allowance; its operations still obey the global work/BDD limits.
#[derive(Clone, Copy)]
struct SplitLimits {
    scoring_work: usize,
    depth: usize,
    leaves: usize,
}
impl From<&Limits> for SplitLimits {
    fn from(limits: &Limits) -> Self {
        Self {
            scoring_work: limits.max_structural_split_scoring_work,
            depth: limits.max_structural_split_depth.min(256),
            leaves: limits.max_structural_split_leaves,
        }
    }
}
#[cfg(test)]
impl Default for SplitLimits {
    fn default() -> Self {
        Self::from(&Limits::default())
    }
}

fn optional_failure(error: &CheckError) -> bool {
    recoverable(error)
        || matches!(
            error,
            CheckError::LimitExceeded {
                phase: "structural split",
                resource: "structural split work" | "expression nodes" | "expression depth",
                ..
            }
        )
}

#[derive(Clone)]
struct Value {
    expression: Expr,
    truth: Condition,
}
struct Tree {
    certificate: GuardedCertificate,
    values: BTreeMap<GroundAtom, Value>,
}
impl Tree {
    fn nodes(&self) -> usize {
        self.certificate.structural_nodes()
            + self
                .values
                .values()
                .map(|v| 1 + v.truth.node_count())
                .sum::<usize>()
    }
}
struct Search<'a, 'm> {
    program: &'a GroundProgram,
    component: &'a Component,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    meaning: &'a SymbolicMeaning<'m>,
    limits: SplitLimits,
    work_start: usize,
    stats: GuardedSplitProgress,
    expressions: Expressions,
    cones: Cones<'a>,
}

impl GroundProgram {
    pub(crate) fn structural_splits(
        &self,
        component: &Component,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        meaning: &SymbolicMeaning<'_>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
        cutoff: &mut bool,
    ) -> Result<Vec<GuardedSettlementProof>> {
        *cutoff = false;
        let baseline = *retained;
        progress.work(self, "structural-split", Some(component.id), 0, true);
        let started = progress.attempt_start(AdmissionAttemptKind::StructuralSplit, None);
        let mut search = Search {
            program: self,
            component,
            summaries,
            meaning,
            limits: SplitLimits::from(budget.limits),
            work_start: budget.used(),
            expressions: Expressions::default(),
            cones: Cones::default(),
            stats: GuardedSplitProgress {
                leaves: 1,
                search_limit: Some(budget.limits.max_structural_split_work),
                depth_limit: Some(budget.limits.max_structural_split_depth.min(256)),
                leaf_limit: Some(budget.limits.max_structural_split_leaves),
                ..Default::default()
            },
        };
        let work_start = budget.used();
        let result = budget.structural_split(|budget| {
            if search.limits.depth == 0 || search.limits.leaves == 0 {
                search.cutoff("disabled", budget, progress);
                return Ok(Vec::new());
            }
            let domain = meaning.context().permitted_worlds();
            if domain.is_false() {
                return Ok(Vec::new());
            }
            search.cones.reserve(retained, budget)?;
            let mut result = search.node(&domain, 0, None, retained, budget, progress);
            let storage_obstructed = matches!(
                &result,
                Err(CheckError::LimitExceeded {
                    phase: "symbolic storage",
                    resource: "condition nodes",
                    ..
                })
            ) || matches!(&result, Ok(None))
                && search.stats.cones.storage_fallbacks != 0;
            if search.cones.reserved != 0 && storage_obstructed {
                // Optional retention may not force a negative result. Restart
                // on the same immutable graph without it; never refund work.
                search.cones.release(retained, &mut search.stats.cones);
                search.expressions = Expressions::default();
                *retained = baseline;
                search.stats.leaves = 1;
                search.stats.evaluated_leaves = 0;
                search.stats.cones.uncached_retries += 1;
                result = search.node(&domain, 0, None, retained, budget, progress);
            }
            search.cones.release(retained, &mut search.stats.cones);
            let Some(tree) = result? else {
                return Ok(Vec::new());
            };
            search.stats.state = "staging";
            search.report(budget, progress);
            search.stage(tree, retained, budget, progress)
        });
        search.stats.search_work = Some(budget.used() - work_start);
        search.stats.expression_nodes = Some(search.expressions.len());
        let outcome = match &result {
            Ok(p) if p.is_empty() => "negative",
            Ok(_) => "completed",
            Err(e) if optional_failure(e) => "skipped",
            Err(_) => "failed",
        };
        progress.attempt_end(AdmissionAttemptKind::StructuralSplit, started, outcome);
        *retained = baseline;
        match result {
            Ok(proofs) => {
                let shared = proofs
                    .first()
                    .and_then(|p| match &p.certificate {
                        GuardedCertificate::Joint(j) => Some(j.nodes()),
                        _ => None,
                    })
                    .unwrap_or(0);
                let nodes = shared + proofs.iter().map(|p| p.nodes() - shared).sum::<usize>();
                *retained = crate::symbolic::retain(baseline, 0, nodes, budget)?;
                *cutoff = proofs.is_empty() && search.stats.state.contains("cutoff");
                search.stats.state = if proofs.is_empty() {
                    "negative"
                } else {
                    "certified"
                };
                if !proofs.is_empty() && budget.limits.profile.enabled() && progress.enabled() {
                    let limits = budget.limits;
                    search.stats.replacement_sizes =
                        Some(budget.excluding_time(|| sizes::measure(&proofs, meaning, limits))?);
                }
                progress.structural_split(self, &search.stats, None);
                Ok(proofs)
            }
            Err(e) if optional_failure(&e) => {
                *cutoff = true;
                budget.record_failure(&e);
                search.stats.cutoff_stage = Some(search.stats.state);
                search.stats.state = "fallback";
                progress.structural_split(self, &search.stats, Some(Inconclusive::from_error(e)?));
                // An optional failed optimization is not an unsupported-region
                // cause. The ordinary pipeline still gets to answer the query.
                Ok(Vec::new())
            }
            Err(e) => Err(e),
        }
    }
}

impl<'a> Search<'a, '_> {
    fn report(&mut self, budget: &Budget<'_>, progress: &AdmissionReporter<'_>) {
        self.stats.search_work = Some(budget.used() - self.work_start);
        self.stats.expression_nodes = Some(self.expressions.len());
        progress.structural_split(self.program, &self.stats, None);
    }
    fn cutoff(
        &mut self,
        state: &'static str,
        budget: &Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) {
        self.stats.cutoffs += 1;
        self.stats.state = state;
        progress.cutoff(AdmissionAttemptKind::StructuralSplit);
        self.report(budget, progress);
    }
    fn node(
        &mut self,
        domain: &Condition,
        depth: usize,
        cached: Option<usize>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) -> Result<Option<Tree>> {
        let baseline = *retained;
        let expressions = self.expressions.storage;
        let result = self.node_inner(domain, depth, cached, retained, budget, progress);
        *retained = baseline + self.expressions.storage - expressions;
        if let Ok(Some(tree)) = &result {
            *retained = crate::symbolic::retain(*retained, 0, tree.nodes(), budget)?;
        }
        result
    }
    fn node_inner(
        &mut self,
        domain: &Condition,
        depth: usize,
        cached: Option<usize>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) -> Result<Option<Tree>> {
        let baseline = *retained;
        budget.tick("structural split branch")?;
        self.stats.depth = depth;
        self.stats.max_depth = self.stats.max_depth.max(depth);
        let ctx = self.meaning.context();
        let ScoredCone { cone, cyclic: size } = match self.cones.take(cached) {
            Some(value) => {
                self.stats.cones.reused += 1;
                *retained =
                    crate::symbolic::retain(*retained, 0, value.cone.temporary_nodes(), budget)?;
                value
            }
            None => self.prepare_cone(domain, retained, budget)?,
        };
        self.stats.cyclic_atoms = Some(size);
        self.stats.chosen = None;
        self.stats.candidates_available = None;
        self.stats.node_candidates_scored = None;
        self.stats.scoring_work = None;
        self.stats.scoring_limit = None;
        self.stats.branch_cyclic_atoms = None;
        self.stats.branch_cone_atoms = Some(cone.atoms.len());
        self.stats.branch_live_atoms = Some(
            cone.producers
                .iter()
                .filter(|p| p.live)
                .map(|p| &p.rule.head.atom)
                .collect::<BTreeSet<_>>()
                .len(),
        );
        self.stats.state = if size == 0 { "evaluating" } else { "scoring" };
        self.report(budget, progress);
        if size == 0 {
            return self.evaluate(&cone, retained, budget, progress);
        }
        if depth >= self.limits.depth || self.stats.leaves >= self.limits.leaves {
            self.cutoff(
                if depth >= self.limits.depth {
                    "depth-cutoff"
                } else {
                    "leaf-cutoff"
                },
                budget,
                progress,
            );
            return Ok(None);
        }
        // Rank by affected producers, counting an atom only once per producer.
        // Exclusivity is only a tie-break from the already-selected input groups;
        // no implication queries or new assumptions are introduced by ranking.
        let mut atoms = BTreeMap::<GroundAtom, (usize, usize)>::new();
        for p in cone.producers.iter().filter(|p| p.live) {
            let mut seen = BTreeSet::new();
            for atom in p.rule.body.iter().map(|l| &l.term.atom).chain(
                p.rule
                    .replacements
                    .iter()
                    .flat_map(|r| r.expression.atoms()),
            ) {
                budget.tick("structural split candidate")?;
                if self.component.atoms.binary_search(atom).is_err()
                    && matches!(self.meaning.fact(atom)?, SymbolicFact::Settled(_))
                    && seen.insert(atom)
                {
                    if !atoms.contains_key(atom) {
                        *retained = crate::symbolic::retain(*retained, 0, 3, budget)?;
                    }
                    atoms.entry(atom.clone()).or_insert((0, usize::MAX)).0 += 1;
                }
            }
        }
        for group in self
            .program
            .input_groups
            .iter()
            .chain(self.program.universe_groups.iter().map(|g| &g.atoms))
        {
            for atom in group {
                budget.tick("structural split exclusive group ranking")?;
                if let Some((_, size)) = atoms.get_mut(atom) {
                    *size = (*size).min(group.len());
                }
            }
        }
        let mut atoms: Vec<_> = atoms.into_iter().collect();
        // Charge an upper bound on comparisons before sorting. The final atom
        // tie-break is deterministic and independent of hash iteration order.
        budget.charge(
            atoms
                .len()
                .saturating_mul(atoms.len().max(1).ilog2() as usize + 1),
            "structural split ranking",
        )?;
        atoms.sort_by(|(a, (ac, ag)), (b, (bc, bg))| bc.cmp(ac).then(ag.cmp(bg)).then(a.cmp(b)));
        self.stats.candidates_available = Some(atoms.len());
        self.stats.node_candidates_scored = Some(0);
        self.stats.scoring_work = Some(0);
        self.stats.scoring_limit = Some(self.limits.scoring_work);
        self.report(budget, progress);
        // Only this node's best pair and in-flight score may use the shared
        // reservation. Waiting ancestor siblings yield before deeper scoring.
        self.cones.clear(&mut self.stats.cones);
        let mut best = None;
        let mut best_score = (size, size.saturating_mul(2));
        let mut scoring_used = 0;
        for (atom, _) in atoms {
            if scoring_used >= self.limits.scoring_work {
                self.stats.scoring_work = Some(scoring_used);
                self.cutoff("scoring-cutoff", budget, progress);
                break;
            }
            let candidate_start = budget.used();
            let SymbolicFact::Settled(condition) = self.meaning.fact(&atom)? else {
                unreachable!()
            };
            let yes = ctx.apply(domain, &condition, and, budget)?;
            let no = ctx.apply(domain, &condition, and_not, budget)?;
            if yes.is_false() || no.is_false() {
                self.stats.fixed_candidates += 1;
                continue;
            }
            *self.stats.node_candidates_scored.as_mut().unwrap() += 1;
            self.stats.candidates_scored += 1;
            let mut sizes = [0; 2];
            let mut cached = [None; 2];
            for (i, d) in [&yes, &no].into_iter().enumerate() {
                let before = *retained;
                let c = self.prepare_cone(d, retained, budget)?;
                sizes[i] = c.cyclic;
                cached[i] = self.cones.keep(c);
                *retained = before;
            }
            scoring_used += budget.used() - candidate_start;
            self.stats.scoring_work = Some(scoring_used);
            let score = (sizes[0].max(sizes[1]), sizes[0].saturating_add(sizes[1]));
            if score < best_score {
                let old = best.as_ref().map_or(
                    0,
                    |(_, a, b, _, _): &(
                        GroundAtom,
                        Condition,
                        Condition,
                        [usize; 2],
                        [Option<usize>; 2],
                    )| { 1 + a.node_count() + b.node_count() },
                );
                *retained = crate::symbolic::retain(
                    *retained,
                    old,
                    1 + yes.node_count() + no.node_count(),
                    budget,
                )?;
                if let Some((_, _, _, _, previous)) = &best {
                    self.cones.discard(*previous, &mut self.stats.cones);
                }
                best = Some((atom, yes, no, sizes, cached));
                best_score = score;
                if score == (0, 0) {
                    break;
                }
            } else {
                self.cones.discard(cached, &mut self.stats.cones);
            }
        }
        let Some((atom, yes, no, sizes, cached)) = best else {
            return Ok(None);
        };
        // Ranking and the parent cone have no readers below this point. Do not
        // retain that scratch on every recursive frame.
        drop(cone);
        *retained =
            crate::symbolic::retain(baseline, 0, 1 + yes.node_count() + no.node_count(), budget)?;
        self.stats.leaves += 1;
        self.stats.chosen = Some(atom.clone());
        self.stats.branch_cyclic_atoms = Some(sizes);
        self.stats.state = "split";
        self.report(budget, progress);
        let Some(left) = self.node(&yes, depth + 1, cached[0], retained, budget, progress)? else {
            return Ok(None);
        };
        let Some(right) = self.node(&no, depth + 1, cached[1], retained, budget, progress)? else {
            return Ok(None);
        };
        self.stats.state = "combining";
        self.report(budget, progress);
        let choice = self.expressions.intern(
            Arc::new(SettledExpression::Atom(atom.clone())),
            retained,
            budget,
        )?;
        let mut values = BTreeMap::new();
        for (target, a) in left.values {
            budget.tick("structural split combination")?;
            let b = &right.values[&target];
            let expression = self.expressions.choose(
                choice.clone(),
                a.expression,
                b.expression.clone(),
                retained,
                budget,
            )?;
            let truth = ctx.apply(
                &ctx.apply(&yes, &a.truth, and, budget)?,
                &ctx.apply(&no, &b.truth, and, budget)?,
                or,
                budget,
            )?;
            *retained = crate::symbolic::retain(*retained, 0, 1 + truth.node_count(), budget)?;
            values.insert(target, Value { expression, truth });
        }
        let certificate = GuardedCertificate::Split {
            atom,
            when_true: Box::new(left.certificate),
            when_false: Box::new(right.certificate),
        };
        Ok(Some(Tree {
            certificate,
            values,
        }))
    }

    fn prepare_cone(
        &mut self,
        domain: &Condition,
        retained: &mut usize,
        budget: &mut Budget<'_>,
    ) -> Result<ScoredCone<'a>> {
        let cone = component_cone(
            self.program,
            self.component,
            self.summaries,
            domain,
            self.meaning.context(),
            retained,
            budget,
            &mut self.stats.cones,
        )?;
        let start = budget.used();
        let result = cyclic_size(&cone, retained, budget);
        self.stats.cones.scc_work += budget.used() - start;
        Ok(ScoredCone {
            cone,
            cyclic: result?,
        })
    }

    fn evaluate(
        &mut self,
        cone: &BorrowedCone<'_>,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) -> Result<Option<Tree>> {
        let ctx = self.meaning.context();
        let mut dependencies: BTreeMap<_, usize> = cone.atoms.iter().map(|a| (a, 0)).collect();
        let mut readers = BTreeMap::<_, Vec<_>>::new();
        let mut producers = BTreeMap::<_, Vec<_>>::new();
        *retained = crate::symbolic::retain(
            *retained,
            0,
            cone.atoms.len() * 4 + cone.producers.len(),
            budget,
        )?;
        for p in cone.producers.iter().filter(|p| p.live) {
            budget.tick("structural split order")?;
            producers.entry(&p.rule.head.atom).or_default().push(p);
            for literal in &p.rule.body {
                budget.tick("structural split order edge")?;
                if dependencies.contains_key(&literal.term.atom) {
                    *dependencies.get_mut(&p.rule.head.atom).unwrap() += 1;
                    readers
                        .entry(&literal.term.atom)
                        .or_default()
                        .push(&p.rule.head.atom);
                    *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
                }
            }
        }
        let mut ready: BTreeSet<_> = dependencies
            .iter()
            .filter(|(_, n)| **n == 0)
            .map(|(a, _)| *a)
            .collect();
        let mut values = BTreeMap::<GroundAtom, Value>::new();
        let mut steps = Vec::new();

        while let Some(atom) = ready.pop_first() {
            budget.tick("structural split evaluation")?;
            let mut alternatives = Vec::new();
            let mut truth = ctx.false_condition();
            let mut sources = Vec::new();
            for p in producers.get(atom).into_iter().flatten() {
                let mut terms = Vec::new();
                let mut body = cone.domain.clone();
                for literal in &p.rule.body {
                    budget.tick("structural split premise")?;
                    let (expression, value) = if let Some(v) = values.get(&literal.term.atom) {
                        (v.expression.clone(), v.truth.clone())
                    } else {
                        match self.meaning.fact(&literal.term.atom)? {
                            SymbolicFact::Settled(v) => (
                                if v.is_true() {
                                    constant(true)
                                } else if v.is_false() {
                                    constant(false)
                                } else {
                                    Arc::new(SettledExpression::Atom(literal.term.atom.clone()))
                                },
                                v,
                            ),
                            SymbolicFact::Blocked(_) | SymbolicFact::Inconclusive(_) => {
                                self.stats.state = "unresolved-external";
                                self.report(budget, progress);
                                return Ok(None);
                            }
                        }
                    };
                    let negative = literal.polarity == Polarity::Negative;
                    body =
                        ctx.apply(&body, &value, if negative { and_not } else { and }, budget)?;
                    *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
                    terms.push(signed(expression, negative));
                }
                for replacement in &p.rule.replacements {
                    let v = self
                        .meaning
                        .settled_expression(&replacement.expression, budget)?;
                    body = ctx.apply(&body, &v, and, budget)?;
                    *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
                    terms.push(replacement.expression.clone());
                }
                let expression = join(terms, true);
                let expression = self.expressions.intern(expression, retained, budget)?;
                *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
                alternatives.push(expression);
                truth = ctx.apply(&truth, &body, or, budget)?;
                sources.push(p.rule.id);
            }
            let expression = if truth.is_false() {
                constant(false)
            } else if ctx.apply(&cone.domain, &truth, and_not, budget)?.is_false() {
                constant(true)
            } else {
                join(alternatives, false)
            };
            let expression = self.expressions.intern(expression, retained, budget)?;
            budget.charge(sources.len(), "structural split value storage")?;
            *retained = crate::symbolic::retain(
                *retained,
                0,
                2 + 2 * truth.node_count() + sources.len(),
                budget,
            )?;
            steps.push(GuardedSettlementStep {
                atom: atom.clone(),
                expression: expression.clone(),
                producers: sources,
                false_by_bound: false,
                true_by_guarantee: false,
            });
            values.insert(atom.clone(), Value { expression, truth });
            for head in readers.get(atom).into_iter().flatten() {
                budget.tick("structural split order advance")?;
                let count = dependencies.get_mut(head).unwrap();
                *count -= 1;
                if *count == 0 {
                    ready.insert(head);
                }
            }
        }
        if values.len() != cone.atoms.len() {
            return Err(CheckError::Internal("cyclic structural leaf"));
        }
        budget.charge(
            cone.pruning.reasons.len(),
            "structural split pruning evidence",
        )?;
        self.stats.evaluated_leaves += 1;
        let certificate = GuardedCertificate::Acyclic {
            domain: cone.domain.clone(),
            steps,
            values: values
                .iter()
                .map(|(a, v)| (a.clone(), v.truth.clone()))
                .collect(),
            pruning: cone.pruning.reasons.clone(),
        };
        Ok(Some(Tree {
            certificate,
            values,
        }))
    }

    fn stage(
        &mut self,
        tree: Tree,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &AdmissionReporter<'_>,
    ) -> Result<Vec<GuardedSettlementProof>> {
        *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
        let mut producers = Vec::new();
        for id in &self.program.component_rules[self.component.id.index] {
            let source = &self.summaries[&self.program.rules[*id].id];
            budget.charge(
                1 + source.rule.body.len() + source.settled.len(),
                "structural split evidence staging",
            )?;
            *retained = crate::symbolic::retain(*retained, 0, source.nodes(), budget)?;
            producers.push(Arc::new(source.clone()));
        }
        // Both signs are shared before freezing the joint storage count.
        for value in tree.values.values() {
            self.expressions
                .intern(signed(value.expression.clone(), true), retained, budget)?;
        }
        let retained_nodes = 2
            + tree.certificate.structural_nodes()
            + self.expressions.storage
            + producers.iter().map(|p| p.nodes()).sum::<usize>();
        let joint = Arc::new(JointCertificate {
            retained_nodes,
            snapshot: self.program.graph_revision,
            component: self.component.id,
            producers,
            tree: tree.certificate,
        });
        let mut by_head = BTreeMap::<_, Vec<_>>::new();
        for producer in &joint.producers {
            budget.tick("structural split direct evidence index")?;
            *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
            by_head
                .entry(&producer.rule.head.atom)
                .or_default()
                .push(producer);
        }
        let mut proofs = Vec::new();
        for candidate in &joint.producers {
            for literal in &candidate.rule.body {
                budget.tick("structural split replacement staging")?;
                let Some(value) = tree.values.get(&literal.term.atom) else {
                    continue;
                };
                let negative = literal.polarity == Polarity::Negative;
                let replacement = self.expressions.intern(
                    signed(value.expression.clone(), negative),
                    retained,
                    budget,
                )?;
                let coverage = if negative {
                    self.meaning.context().complement(&value.truth, budget)?
                } else {
                    value.truth.clone()
                };
                // Keep the global replacement intact. Only the presentation
                // classification is guard-relative, and computed under the same
                // bounded staging operation as its certificate.
                let ctx = self.meaning.context();
                let redundant_negation = negative
                    && ctx
                        .restrict(
                            &ctx.apply(&candidate.condition, &coverage, and_not, budget)?,
                            budget,
                        )?
                        .is_false();
                // Direct locations are the target's original producers; the
                // shared certificate retains *all* producers, including dead ones.
                let mut direct = Vec::new();
                for source in by_head.get(&literal.term.atom).into_iter().flatten() {
                    budget.charge(
                        1 + source.rule.body.len() + source.settled.len(),
                        "structural split direct evidence staging",
                    )?;
                    direct.push((***source).clone());
                }
                budget.charge(
                    1 + candidate.rule.body.len() + direct.len(),
                    "structural split replacement staging",
                )?;
                let proof = GuardedSettlementProof {
                    proof: SymbolicRewriteProof {
                        candidate: (**candidate).clone(),
                        producers: direct,
                        coverage,
                        upper_bounds: None,
                    },
                    certificate: GuardedCertificate::Joint(joint.clone()),
                    occurrence: literal.term.occurrence,
                    replacement,
                    implied_guard: None,
                    redundant_negation,
                };
                *retained =
                    crate::symbolic::retain(*retained, 0, proof.nodes() - joint.nodes(), budget)?;
                proofs.push(proof);
            }
        }
        self.report(budget, progress);
        Ok(proofs)
    }
}

#[cfg(test)]
mod tests;
