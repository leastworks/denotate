//! Bounded world partitions. Executable cones only rank choices; every installed
//! leaf is proved again on a candidate-relaxed, branch-local cone.
use super::*;

#[derive(Clone, Copy)]
pub(crate) struct CaseLimits {
    pub candidates: usize,
    pub depth: usize,
    pub leaves: usize,
}
impl Default for CaseLimits {
    fn default() -> Self {
        Self {
            candidates: 16,
            depth: 3,
            leaves: 8,
        }
    }
}

struct Search<'a, 'm> {
    program: &'a GroundProgram,
    component: &'a Component,
    candidate: &'a ProducerSummary,
    literal: &'a GroundLiteral,
    meaning: &'a SymbolicMeaning<'m>,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &'a BTreeMap<&'a GroundAtom, Vec<GroundRuleId>>,
    limits: CaseLimits,
    stats: GuardedSplitProgress,
}
struct Choice {
    atom: GroundAtom,
    condition: Condition,
    cyclic: [usize; 2],
}

pub(crate) fn recoverable(error: &CheckError) -> bool {
    matches!(
        error,
        CheckError::LimitExceeded {
            phase: "BDD operation" | "BDD preflight",
            resource: "BDD nodes" | "BDD tasks",
            ..
        } | CheckError::LimitExceeded {
            phase: "symbolic storage",
            resource: "condition nodes",
            ..
        }
    )
}

impl GroundProgram {
    pub(super) fn case_settlement(
        &self,
        candidate: &ProducerSummary,
        literal: &GroundLiteral,
        component: &Component,
        meaning: &SymbolicMeaning<'_>,
        summaries: &BTreeMap<GroundRuleId, ProducerSummary>,
        producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
        implied: Option<&crate::implied_guard::Inferred>,
        dependencies: &mut BTreeSet<GroundRuleId>,
        limits: CaseLimits,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<GuardedSettlementProof>> {
        let baseline = *retained;
        // A negative search depends on its scoring graph too, not just on the
        // eventual leaf cones. Keep a conservative component footprint for retry.
        let rules = &self.component_rules[component.id.index];
        budget.charge(rules.len(), "case split retry footprint")?;
        *retained = crate::symbolic::retain(*retained, 0, rules.len(), budget)?;
        dependencies.extend(rules.iter().map(|i| self.rules[*i].id));
        let guard = implied.map_or(&candidate.condition, |i| &i.condition);
        let domain = meaning.context().restrict(guard, budget)?;
        *retained = crate::symbolic::retain(*retained, 0, domain.node_count(), budget)?;
        let mut search = Search {
            program: self,
            component,
            candidate,
            literal,
            meaning,
            summaries,
            producers,
            limits,
            stats: GuardedSplitProgress {
                leaves: 1,
                ..Default::default()
            },
        };
        progress.rule(self, "guarded-cases", candidate.rule.id, 0);
        // The outer attempt has already tried this domain. No branch uses the
        // rule/occurrence caches: their keys intentionally contain no branch.
        let result = search.node(&domain, 0, false, retained, budget, progress)?;
        search.stats.state = if result.is_some() {
            "certified"
        } else {
            "negative"
        };
        progress.guarded_split(self, &search.stats);
        let proof = match result {
            Some(result) => self.finish_guarded(
                candidate, literal, meaning, implied, result, retained, budget, progress,
            )?,
            None => None,
        };
        *retained = crate::symbolic::retain(
            baseline,
            0,
            proof.as_ref().map_or(0, GuardedSettlementProof::nodes),
            budget,
        )?;
        Ok(proof)
    }
}

impl Search<'_, '_> {
    fn cutoff(
        &mut self,
        reason: &'static str,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) {
        self.stats.cutoffs += 1;
        self.stats.state = reason;
        progress.cutoff(AdmissionAttemptKind::GuardedSettlement);
        progress.guarded_split(self.program, &self.stats);
    }
    fn node(
        &mut self,
        domain: &Condition,
        depth: usize,
        certify: bool,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<Settlement>> {
        let baseline = *retained;
        let result = self.node_inner(domain, depth, certify, retained, budget, progress);
        // All scratch and unsuccessful partial branches have dropped. Only an
        // owned complete result can escape; work is never refunded.
        *retained = baseline;
        if let Ok(Some(value)) = &result {
            *retained = crate::symbolic::retain(baseline, 0, value.nodes(), budget)?;
        }
        result
    }
    fn node_inner(
        &mut self,
        domain: &Condition,
        depth: usize,
        certify: bool,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<Settlement>> {
        budget.tick("case split branch")?;
        self.stats.depth = depth;
        self.stats.max_depth = self.stats.max_depth.max(depth);
        let ctx = self.meaning.context();
        if domain.is_false() {
            return Ok(Some(Settlement {
                expression: constant(false),
                truth: ctx.false_condition(),
                certificate: GuardedCertificate::Empty {
                    domain: domain.clone(),
                },
            }));
        }
        let mut local_failure = None;
        if certify {
            let baseline = *retained;
            let result = (|| {
                let mut scoped = self.candidate.clone();
                scoped.condition = domain.clone();
                let mut stats = Preparation::default();
                let cone = crate::guarded_bounds::prepare(
                    self.program,
                    self.component,
                    &scoped,
                    &self.literal.term.atom,
                    self.summaries,
                    self.producers,
                    ctx,
                    retained,
                    budget,
                    &mut stats,
                )?;
                self.stats.branch_cone_atoms = Some(cone.atoms.len());
                self.stats.branch_live_atoms = Some(stats.live_atoms);
                self.stats.state = "branch-bounds";
                progress.guarded_split(self.program, &self.stats);
                let bounds = crate::guarded_bounds::compute(&cone, ctx, retained, budget, None)?;
                self.program.settle_guarded_leaf(
                    self.candidate,
                    self.literal,
                    self.meaning,
                    &bounds,
                    domain,
                    true,
                    retained,
                    budget,
                    progress,
                )
            })();
            match result {
                Ok(Some(result)) => return Ok(Some(result)),
                Ok(None) => {}
                Err(e) if recoverable(&e) => {
                    budget.record_failure(&e);
                    local_failure = Some(e);
                }
                Err(e) => return Err(e),
            }
            *retained = baseline;
        }
        if depth >= self.limits.depth || self.stats.leaves >= self.limits.leaves {
            self.cutoff(
                if depth >= self.limits.depth {
                    "depth-cutoff"
                } else {
                    "leaf-cutoff"
                },
                progress,
            );
            return match local_failure {
                Some(e) => Err(e),
                None => Ok(None),
            };
        }
        let Some(choice) = self.rank(domain, retained, budget, progress)? else {
            return match local_failure {
                Some(e) => Err(e),
                None => Ok(None),
            };
        };
        let yes = ctx.apply(domain, &choice.condition, and, budget)?;
        let no = ctx.apply(
            domain,
            &ctx.complement(&choice.condition, budget)?,
            and,
            budget,
        )?;
        *retained =
            crate::symbolic::retain(*retained, 0, yes.node_count() + no.node_count(), budget)?;
        self.stats.leaves += 1;
        self.stats.chosen = Some(choice.atom.clone());
        self.stats.branch_cyclic_atoms = Some(choice.cyclic);
        self.stats.state = "split";
        progress.guarded_split(self.program, &self.stats);
        let Some(left) = self.node(&yes, depth + 1, true, retained, budget, progress)? else {
            return Ok(None);
        };
        let Some(right) = self.node(&no, depth + 1, true, retained, budget, progress)? else {
            return Ok(None);
        };
        let atom = Arc::new(SettledExpression::Atom(choice.atom.clone()));
        let expression = join(
            vec![
                join(vec![atom.clone(), left.expression], true),
                join(vec![signed(atom, true), right.expression], true),
            ],
            false,
        );
        let truth = ctx.apply(
            &ctx.apply(&yes, &left.truth, and, budget)?,
            &ctx.apply(&no, &right.truth, and, budget)?,
            or,
            budget,
        )?;
        let certificate = GuardedCertificate::Split {
            atom: choice.atom,
            when_true: Box::new(left.certificate),
            when_false: Box::new(right.certificate),
        };
        if !bounded(&expression, budget)? || certificate.expression_nodes() > CERTIFICATE_NODES {
            self.cutoff("certificate-cutoff", progress);
            return Ok(None);
        }
        Ok(Some(Settlement {
            expression,
            truth,
            certificate,
        }))
    }

    fn rank(
        &mut self,
        domain: &Condition,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<Choice>> {
        let baseline = *retained;
        let result = self.rank_inner(domain, retained, budget, progress);
        *retained = baseline;
        if let Ok(Some(choice)) = &result {
            *retained =
                crate::symbolic::retain(baseline, 0, 1 + choice.condition.node_count(), budget)?;
        }
        result
    }
    fn rank_inner(
        &mut self,
        domain: &Condition,
        retained: &mut usize,
        budget: &mut Budget<'_>,
        progress: &crate::admission_progress::AdmissionReporter<'_>,
    ) -> Result<Option<Choice>> {
        let ctx = self.meaning.context();
        let mut scoped = self.candidate.clone();
        scoped.condition = domain.clone();
        let cone = crate::guarded_bounds::executable(
            self.program,
            self.component,
            &scoped,
            &self.literal.term.atom,
            self.summaries,
            self.producers,
            ctx,
            retained,
            budget,
            &mut Preparation::default(),
        )?;
        let n = cyclic_size(&cone, retained, budget)?;
        self.stats.cyclic_atoms = Some(n);
        if n == 0 {
            return Ok(None);
        }
        let mut atoms = BTreeSet::new();
        for producer in cone.producers.iter().filter(|p| p.live) {
            for atom in producer.rule.body.iter().map(|p| &p.term.atom).chain(
                producer
                    .rule
                    .replacements
                    .iter()
                    .flat_map(|r| r.expression.atoms()),
            ) {
                budget.tick("case split candidates")?;
                if self
                    .program
                    .atom_index
                    .get(atom)
                    .is_some_and(|i| self.program.atom_components[*i] == self.component.id)
                {
                    continue;
                }
                if matches!(self.meaning.fact(atom)?, SymbolicFact::Settled(_))
                    && atoms.insert(atom.clone())
                {
                    *retained = crate::symbolic::retain(*retained, 0, 1, budget)?;
                }
            }
        }
        let mut score = (n, n.saturating_mul(2));
        let mut best: Option<Choice> = None;
        let mut scored = 0;
        for atom in atoms {
            budget.tick("case split candidate")?;
            let SymbolicFact::Settled(condition) = self.meaning.fact(&atom)? else {
                unreachable!()
            };
            let yes = ctx.apply(domain, &condition, and, budget)?;
            let no = ctx.apply(domain, &ctx.complement(&condition, budget)?, and, budget)?;
            if yes.is_false() || no.is_false() {
                self.stats.fixed_candidates += 1;
                continue;
            }
            if scored == self.limits.candidates {
                self.cutoff("scoring-cutoff", progress);
                return Ok(None);
            }
            scored += 1;
            self.stats.candidates_scored += 1;
            let mut sizes = [0; 2];
            for (i, branch) in [yes, no].into_iter().enumerate() {
                let before = *retained;
                scoped.condition = branch;
                let branch_cone = crate::guarded_bounds::executable(
                    self.program,
                    self.component,
                    &scoped,
                    &self.literal.term.atom,
                    self.summaries,
                    self.producers,
                    ctx,
                    retained,
                    budget,
                    &mut Preparation::default(),
                )?;
                sizes[i] = cyclic_size(&branch_cone, retained, budget)?;
                drop(branch_cone);
                *retained = before;
            }
            let next = (sizes[0].max(sizes[1]), sizes[0].saturating_add(sizes[1]));
            if next < score {
                score = next;
                *retained = crate::symbolic::retain(
                    *retained,
                    best.as_ref().map_or(0, |c| 1 + c.condition.node_count()),
                    1 + condition.node_count(),
                    budget,
                )?;
                best = Some(Choice {
                    atom,
                    condition,
                    cyclic: sizes,
                });
                if score == (0, 0) {
                    break;
                }
            }
        }
        Ok(best)
    }
}

/// Iterative SCC traversal, like the executable graph builder. Scores count
/// cyclic atoms, including positive cycles and self-loops; polarity proves nothing.
pub(crate) fn cyclic_size(
    cone: &BorrowedCone<'_>,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<usize> {
    let baseline = *retained;
    let n = cone.atoms.len();
    *retained = crate::symbolic::retain(*retained, 0, n.saturating_mul(8), budget)?;
    let index: BTreeMap<_, _> = cone.atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    budget.charge(n, "case split graph")?;
    let mut edges = vec![Vec::new(); n];
    let mut reverse = vec![Vec::new(); n];
    for producer in cone.producers.iter().filter(|p| p.live) {
        let head = index[&producer.rule.head.atom];
        for premise in &producer.rule.body {
            budget.tick("case split edge")?;
            if let Some(&to) = index.get(&premise.term.atom) {
                *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
                edges[head].push(to);
                reverse[to].push(head);
            }
        }
    }
    let mut seen = vec![false; n];
    let mut finish = Vec::new();
    for root in 0..n {
        budget.tick("case split SCC")?;
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((node, next)) = stack.last_mut() {
            budget.tick("case split SCC")?;
            if let Some(&to) = edges[*node].get(*next) {
                *next += 1;
                if !seen[to] {
                    seen[to] = true;
                    stack.push((to, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }
    seen.fill(false);
    let mut count = 0;
    for root in finish.into_iter().rev() {
        budget.tick("case split SCC")?;
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut size = 0;
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            budget.tick("case split SCC")?;
            size += 1;
            for &to in &reverse[node] {
                budget.tick("case split SCC")?;
                if !seen[to] {
                    seen[to] = true;
                    stack.push(to);
                }
            }
        }
        if size > 1 || edges[root].contains(&root) {
            count += size;
        }
    }
    *retained = baseline;
    Ok(count)
}

#[cfg(test)]
mod tests;
