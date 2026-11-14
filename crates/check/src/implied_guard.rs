//! One-hop necessary conditions, built lazily from an immutable settled snapshot.
use crate::{
    guarded_settlement::{Expr, bounded, constant, join, signed},
    limits::{Budget, Result},
    *,
};
use biodivine_lib_bdd::op_function::{and, or};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

const DISCOVERY_WORK: usize = 8192;

#[derive(Debug, Clone)]
pub struct ImpliedGuardPremise {
    pub literal: GroundLiteral,
    /// Complete immutable producer snapshots, including support outside the cone.
    pub producers: Vec<Arc<ProducerSummary>>,
}
#[derive(Debug, Clone)]
pub struct ImpliedGuardProof {
    pub expression: Expr,
    pub premises: Vec<ImpliedGuardPremise>,
}
impl ImpliedGuardProof {
    pub(crate) fn summaries(&self) -> impl Iterator<Item = &ProducerSummary> {
        self.premises
            .iter()
            .flat_map(|p| p.producers.iter().map(AsRef::as_ref))
    }
    pub(crate) fn nodes(&self) -> usize {
        self.expression.nodes()
            + self.premises.len()
            + self.summaries().map(source_nodes).sum::<usize>()
    }
}
fn source_nodes(p: &ProducerSummary) -> usize {
    1 + p.nodes() + p.rule.body.len() + p.rule.replacements.len() + p.settled.len()
}
pub(crate) struct Inferred {
    pub condition: Condition,
    pub proof: ImpliedGuardProof,
}
impl Inferred {
    pub fn nodes(&self) -> usize {
        self.condition.node_count() + self.proof.nodes()
    }
}
/// One most-recent complete union. It borrows summaries, never a whole round.
pub(crate) struct Union<'a> {
    key: (GroundAtom, bool),
    condition: Condition,
    expression: Expr,
    producers: Vec<&'a ProducerSummary>,
}
impl Union<'_> {
    pub fn nodes(&self) -> usize {
        1 + self.condition.node_count() + self.expression.nodes() + self.producers.len()
    }
}
pub(crate) struct Discovery<'a> {
    pub inferred: Option<Inferred>,
    pub union: Option<Arc<Union<'a>>>,
    pub cutoff: bool,
}
impl Discovery<'_> {
    pub fn nodes(&self) -> usize {
        self.inferred.as_ref().map_or(0, Inferred::nodes)
            + self.union.as_ref().map_or(0, |u| u.nodes())
    }
}

// Built once from summaries. Sorting never constructs a new BDD or walks cones.
#[derive(Default)]
pub(crate) struct Hint {
    lower: Option<usize>,
    upper: usize,
    unrestricted: bool,
}
impl Hint {
    pub fn add(&mut self, p: &ProducerSummary) {
        if p.exact && !p.condition.is_false() {
            self.lower = Some(self.lower.map_or(p.condition.node_count(), |n| {
                n.min(p.condition.node_count())
            }));
        }
        self.upper = self.upper.saturating_add(p.condition.node_count());
        self.unrestricted |= p.condition.is_true();
    }
}
pub(crate) fn hint(
    candidate: &ProducerSummary,
    hints: &BTreeMap<GroundAtom, Hint>,
    budget: &mut Budget<'_>,
) -> Result<Option<usize>> {
    // Hints only promote an otherwise unrestricted reader. This preserves the
    // ordering of existing informative guards when no inference is needed.
    if !candidate.condition.is_true() {
        return Ok(None);
    }
    let mut estimate = None;
    for literal in &candidate.rule.body {
        budget.tick("implied guard hint")?;
        let Some(h) = hints.get(&literal.term.atom) else {
            continue;
        };
        let n = if literal.polarity == Polarity::Negative {
            h.lower
        } else {
            (!h.unrestricted).then_some(h.upper)
        };
        if let Some(n) = n {
            estimate = Some(estimate.map_or(n, |old: usize| old.min(n)));
        }
    }
    Ok(estimate)
}

struct Walk {
    work: usize,
}
impl Walk {
    fn charge(&mut self, n: usize, budget: &mut Budget<'_>) -> std::result::Result<(), Stop> {
        budget.charge(n, "implied guard discovery")?;
        self.work = self.work.saturating_add(n);
        if self.work > DISCOVERY_WORK {
            Err(Stop::Cutoff)
        } else {
            Ok(())
        }
    }
}
enum Stop {
    Cutoff,
    Error(CheckError),
}
impl From<CheckError> for Stop {
    fn from(e: CheckError) -> Self {
        Self::Error(e)
    }
}
type Build<T> = std::result::Result<T, Stop>;

fn expression(
    p: &ProducerSummary,
    walk: &mut Walk,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Build<Expr> {
    walk.charge(
        1 + p.rule.body.len() + p.rule.replacements.len() + p.settled.len(),
        budget,
    )?;
    let mut terms = p
        .rule
        .replacements
        .iter()
        .map(|r| Arc::clone(&r.expression))
        .collect::<Vec<_>>();
    for s in &p.settled {
        // Preserve static truth directly. In particular !q for an impossible
        // q is true; complementing a producer containing it must not introduce
        // a positive dependency on an atom absent from the sparse ground graph.
        terms.push(if s.condition.is_true() {
            constant(true)
        } else if s.condition.is_false() {
            constant(false)
        } else {
            signed(
                Arc::new(SettledExpression::Atom(s.literal.term.atom.clone())),
                s.literal.polarity == Polarity::Negative,
            )
        });
    }
    let e = join(terms, true);
    if !bounded(&e, budget)? {
        return Err(Stop::Cutoff);
    }
    walk.charge(e.nodes(), budget)?;
    *retained = crate::symbolic::retain(*retained, 0, e.nodes() + 1, budget)?;
    Ok(e)
}

pub(crate) fn discover<'a>(
    candidate: &ProducerSummary,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
    previous: Option<&Arc<Union<'a>>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Result<Discovery<'a>> {
    let baseline = *retained;
    let result = build(
        candidate, summaries, producers, previous, ctx, retained, budget,
    );
    let result = match result {
        Ok(result) => result,
        Err(Stop::Cutoff) => Discovery {
            inferred: None,
            union: None,
            cutoff: true,
        },
        Err(Stop::Error(e)) => return Err(e),
    };
    // No partial inference or union escapes. Successful values keep explicit
    // charges; the caller replaces/releases the optional one-entry union cache.
    *retained = crate::symbolic::retain(baseline, 0, result.nodes(), budget)?;
    Ok(result)
}
fn build<'a>(
    candidate: &ProducerSummary,
    summaries: &'a BTreeMap<GroundRuleId, ProducerSummary>,
    producers: &BTreeMap<&GroundAtom, Vec<GroundRuleId>>,
    previous: Option<&Arc<Union<'a>>>,
    ctx: &ConditionContext,
    retained: &mut usize,
    budget: &mut Budget<'_>,
) -> Build<Discovery<'a>> {
    let mut walk = Walk { work: 0 };
    walk.charge(candidate.settled.len(), budget)?;
    let settled = candidate
        .settled
        .iter()
        .map(|s| s.literal.term.occurrence)
        .collect::<BTreeSet<_>>();
    let mut condition = candidate.condition.clone();
    *retained =
        crate::symbolic::retain(*retained, 0, settled.len() + condition.node_count(), budget)?;
    let mut terms = vec![expression(candidate, &mut walk, retained, budget)?];
    let mut premises = Vec::new();
    let mut latest: Option<Arc<Union<'a>>> = None;
    for literal in &candidate.rule.body {
        walk.charge(1, budget)?;
        if settled.contains(&literal.term.occurrence) {
            continue;
        }
        let negative = literal.polarity == Polarity::Negative;
        let key = (literal.term.atom.clone(), negative);
        let cached = latest
            .as_ref()
            .filter(|u| u.key == key)
            .or_else(|| previous.filter(|u| u.key == key));
        let union = if let Some(cached) = cached {
            Arc::clone(cached)
        } else {
            let mut condition = ctx.false_condition();
            *retained = crate::symbolic::retain(*retained, 0, condition.node_count(), budget)?;
            let mut alternatives = Vec::new();
            let mut sources = Vec::new();
            for id in producers.get(&literal.term.atom).into_iter().flatten() {
                walk.charge(1, budget)?;
                let p = &summaries[id];
                if negative && (!p.exact || *id == candidate.rule.id) {
                    continue;
                }
                // Even the reading producer supplies only its original settled
                // guard; no loop premise or newly inferred guard justifies itself.
                alternatives.push(expression(p, &mut walk, retained, budget)?);
                let next = ctx.apply(&condition, &p.condition, or, budget)?;
                *retained = crate::symbolic::retain(
                    *retained,
                    condition.node_count(),
                    next.node_count(),
                    budget,
                )?;
                condition = next;
                *retained = crate::symbolic::retain(*retained, 0, 2, budget)?;
                sources.push(p);
            }
            let e = join(alternatives, false);
            if !bounded(&e, budget)? {
                return Err(Stop::Cutoff);
            }
            walk.charge(e.nodes(), budget)?;
            let union = Arc::new(Union {
                key,
                condition,
                expression: e,
                producers: sources,
            });
            *retained = crate::symbolic::retain(*retained, 0, union.nodes(), budget)?;
            union
        };
        let necessary = if negative {
            ctx.complement(&union.condition, budget)?
        } else {
            union.condition.clone()
        };
        *retained = crate::symbolic::retain(*retained, 0, necessary.node_count(), budget)?;
        condition = ctx.apply(&condition, &necessary, and, budget)?;
        *retained = crate::symbolic::retain(*retained, 0, condition.node_count(), budget)?;
        *retained = crate::symbolic::retain(*retained, 0, 4 + union.expression.nodes(), budget)?;
        terms.push(signed(Arc::clone(&union.expression), negative));
        // Defer expensive snapshot ownership until the guard is known useful.
        premises.push((literal.clone(), Arc::clone(&union)));
        latest = Some(union);
    }
    let complement = ctx.complement(&condition, budget)?;
    *retained = crate::symbolic::retain(*retained, 0, complement.node_count(), budget)?;
    let difference = ctx.apply(&candidate.condition, &complement, and, budget)?;
    *retained = crate::symbolic::retain(*retained, 0, difference.node_count(), budget)?;
    let improved = ctx.restrict(&difference, budget)?;
    *retained = crate::symbolic::retain(*retained, 0, improved.node_count(), budget)?;
    if improved.is_false() || ctx.restrict(&condition, budget)?.is_false() {
        return Ok(Discovery {
            inferred: None,
            union: latest,
            cutoff: false,
        });
    }
    let expression = join(terms, true);
    if !bounded(&expression, budget)? {
        return Err(Stop::Cutoff);
    }
    let mut owned = Vec::new();
    for (literal, union) in premises {
        let mut sources = Vec::new();
        for p in &union.producers {
            walk.charge(
                1 + p.rule.body.len() + p.rule.replacements.len() + p.settled.len(),
                budget,
            )?;
            *retained = crate::symbolic::retain(*retained, 0, source_nodes(p), budget)?;
            sources.push(Arc::new((*p).clone()));
        }
        owned.push(ImpliedGuardPremise {
            literal,
            producers: sources,
        });
    }
    Ok(Discovery {
        inferred: Some(Inferred {
            condition,
            proof: ImpliedGuardProof {
                expression,
                premises: owned,
            },
        }),
        union: latest,
        cutoff: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule, summaries};
    use denotate_ir::Corpus;

    #[test]
    fn self_producer_uses_only_original_guard_and_negative_cover_uses_only_exact_sources() {
        let mut c = Corpus::new();
        let gate = rel(&mut c, "gate", true);
        let flag = rel(&mut c, "flag", true);
        let q = rel(&mut c, "q", false);
        let r = rel(&mut c, "r", false);
        let reader = rule(&mut c, q, &[(gate, false), (q, false), (r, true)]);
        let exact = rule(&mut c, r, &[(flag, false)]);
        rule(&mut c, r, &[(q, true)]);
        let l = Limits::default();
        let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        let m = p.symbolic(&l).unwrap();
        let s = summaries(&p, &m, &l);
        let ctx = m.context();
        let mut index = BTreeMap::<_, Vec<_>>::new();
        for p in s.values() {
            index.entry(&p.rule.head.atom).or_default().push(p.rule.id);
        }
        let candidate = s.values().find(|p| p.rule.source == reader).unwrap();
        let mut retained = 0;
        let d = discover(
            candidate,
            &s,
            &index,
            None,
            ctx,
            &mut retained,
            &mut Budget::new(&l),
        )
        .unwrap();
        let inferred = d.inferred.as_ref().unwrap();
        let expected = ctx
            .and(
                &ctx.input(&atom(gate), &l).unwrap(),
                &ctx.not(&ctx.input(&atom(flag), &l).unwrap(), &l).unwrap(),
                &l,
            )
            .unwrap();
        assert!(ctx.equivalent(&inferred.condition, &expected, &l).unwrap());
        assert_eq!(
            inferred
                .proof
                .expression
                .atoms()
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([atom(gate), atom(flag)])
        );
        assert_eq!(
            inferred
                .proof
                .premises
                .iter()
                .find(|p| p.literal.polarity == Polarity::Negative)
                .unwrap()
                .producers
                .iter()
                .map(|p| p.rule.source)
                .collect::<Vec<_>>(),
            vec![exact]
        );
        assert!(inferred.proof.summaries().any(|p| p.rule.source == reader));
        assert_eq!(retained, d.nodes());
        // Optional storage exhaustion is reported, but the original guard is
        // still available and the failure is not a final admission limit.
        let constrained = Limits {
            max_condition_nodes: 1,
            ..l.clone()
        };
        let events = std::cell::RefCell::new(Vec::new());
        let observe = |e: &crate::AdmissionProgress| events.borrow_mut().push(e.clone());
        let progress = crate::admission_progress::AdmissionReporter::new(Some(&observe));
        let mut attempts = crate::admission_skips::Attempts::default();
        let mut held = 0;
        let result = attempts
            .run(
                crate::admission_skips::Attempt::ImpliedGuard(candidate.rule.id),
                &candidate.rule.head.atom,
                &p,
                &mut held,
                &mut Budget::new(&constrained),
                &progress,
                |held, budget| discover(candidate, &s, &index, None, ctx, held, budget),
            )
            .unwrap();
        assert!(result.is_none());
        assert_eq!(held, 0);
        assert!(attempts.records().is_empty());
        assert!(events.borrow().iter().any(|e| {
            e.skipped
                .as_ref()
                .is_some_and(|s| s.kind == AdmissionAttemptKind::ImpliedGuard)
        }));
        // A repeated signed producer union is reusable only within this snapshot.
        let second = discover(
            candidate,
            &s,
            &index,
            d.union.as_ref(),
            ctx,
            &mut retained,
            &mut Budget::new(&l),
        )
        .unwrap();
        assert!(
            ctx.equivalent(&second.inferred.unwrap().condition, &expected, &l)
                .unwrap()
        );
    }

    #[test]
    fn equal_guard_and_bounded_discovery_leave_no_partial_inference() {
        let mut c = Corpus::new();
        let flag = rel(&mut c, "flag", true);
        let q = rel(&mut c, "q", false);
        let r = rel(&mut c, "r", false);
        rule(&mut c, q, &[(flag, true), (r, true)]);
        rule(&mut c, r, &[(flag, false)]);
        rule(&mut c, r, &[(q, true)]);
        let l = Limits::default();
        let p = GroundProgram::prepare_cartesian(&c, &Domains::new(), &l).unwrap();
        let m = p.symbolic(&l).unwrap();
        let s = summaries(&p, &m, &l);
        let mut index = BTreeMap::<_, Vec<_>>::new();
        for p in s.values() {
            index.entry(&p.rule.head.atom).or_default().push(p.rule.id);
        }
        let candidate = s.values().find(|p| p.rule.head.atom == atom(q)).unwrap();
        let mut retained = 11;
        let d = discover(
            candidate,
            &s,
            &index,
            None,
            m.context(),
            &mut retained,
            &mut Budget::new(&l),
        )
        .unwrap();
        assert!(d.inferred.is_none());
        assert!(!d.cutoff);
        assert_eq!(retained, 11 + d.nodes());
        let mut wide = candidate.clone();
        wide.rule.body = wide
            .rule
            .body
            .into_iter()
            .cycle()
            .take(DISCOVERY_WORK + 1)
            .collect();
        let mut retained = 11;
        let d = discover(
            &wide,
            &s,
            &index,
            None,
            m.context(),
            &mut retained,
            &mut Budget::new(&l),
        )
        .unwrap();
        assert!(d.cutoff);
        assert!(d.inferred.is_none());
        assert!(d.union.is_none());
        assert_eq!(retained, 11);
        let constrained = Limits { max_work: 1, ..l };
        assert!(matches!(
            discover(
                candidate,
                &s,
                &index,
                None,
                m.context(),
                &mut retained,
                &mut Budget::new(&constrained)
            ),
            Err(CheckError::LimitExceeded {
                resource: "work",
                ..
            })
        ));
    }
}
