//! Optional, snapshot-local pruning operands. Only the most recent domain is
//! retained. Reachability, relaxation and propagated deadness are never cached.
use super::*;

#[derive(Default)]
pub(crate) struct PruningCache {
    allowance: usize,
    used: usize,
    domain: Option<(u64, Condition)>,
    live: BTreeMap<GroundRuleId, bool>,
    guarantees: BTreeMap<GroundAtom, (Vec<GroundRuleId>, bool)>,
    disabled: bool,
}
impl PruningCache {
    pub(crate) fn reserve(&mut self, retained: &mut usize, budget: &mut Budget<'_>) -> Result<()> {
        if self.allowance != 0 || self.disabled {
            return Ok(());
        }
        // A small fixed reservation makes partial preparation/fallback accounting
        // independent of how many completed entries it adds. Yield it on pressure.
        let allowance = (budget.limits.max_condition_nodes / 64).min(65_536);
        if allowance == 0 || retained.saturating_add(allowance) > budget.limits.max_condition_nodes
        {
            return Ok(());
        }
        *retained = crate::symbolic::retain(*retained, 0, allowance, budget)?;
        self.allowance = allowance;
        Ok(())
    }
    pub(crate) fn reserved(&self) -> usize {
        self.allowance
    }
    pub(crate) fn release(&mut self) -> usize {
        let held = self.allowance;
        *self = Self {
            disabled: true,
            ..Self::default()
        };
        held
    }
    pub(super) fn select(
        &mut self,
        snapshot: u64,
        domain: &Condition,
        budget: &mut Budget<'_>,
    ) -> Result<()> {
        if self.allowance == 0 {
            return Ok(());
        }
        if domain.node_count().saturating_add(4) > self.allowance {
            // No representation lookup or retention is possible. In particular,
            // do not charge a scan of a large D merely to bypass this cache.
            self.domain = None;
            self.live.clear();
            self.guarantees.clear();
            self.used = 0;
            return Ok(());
        }
        budget.charge(domain.node_count(), "pruning cache domain")?;
        if self
            .domain
            .as_ref()
            .is_some_and(|(s, d)| *s == snapshot && d.same_representation(domain))
        {
            return Ok(());
        }
        self.domain = None;
        self.live.clear();
        self.guarantees.clear();
        self.used = domain.node_count() + 4;
        self.domain = Some((snapshot, domain.clone()));
        Ok(())
    }
    fn room(&self, nodes: usize) -> bool {
        self.domain.is_some() && self.used.saturating_add(nodes) <= self.allowance
    }
    pub(super) fn live(
        &mut self,
        id: GroundRuleId,
        compute: impl FnOnce(&mut Budget<'_>) -> Result<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        if self.domain.is_some() {
            budget.tick("pruning liveness cache lookup")?;
            if let Some(value) = self.live.get(&id) {
                budget.tick("pruning liveness cache hit")?;
                return Ok(*value);
            }
        }
        let result = compute(budget)?;
        if self.room(4) {
            budget.charge(4, "pruning cache retention")?;
            self.live.insert(id, result);
            self.used += 4;
        }
        Ok(result)
    }
    pub(super) fn guaranteed(
        &mut self,
        atom: &GroundAtom,
        exact: &[GroundRuleId],
        compute: impl FnOnce(&mut Budget<'_>) -> Result<bool>,
        budget: &mut Budget<'_>,
    ) -> Result<bool> {
        if self.domain.is_some() {
            budget.charge(1 + exact.len(), "pruning guarantee cache lookup")?;
            if let Some((sources, result)) = self.guarantees.get(atom) {
                // Usually identical. An exact relaxed producer is excluded, so
                // never reuse a guarantee built with a different producer set.
                if sources == exact {
                    budget.tick("pruning guarantee cache hit")?;
                    return Ok(*result);
                }
            }
        }
        let result = compute(budget)?;
        let nodes = 5 + atom.arguments.len() + exact.len();
        if self.room(nodes) {
            budget.charge(nodes, "pruning cache retention")?;
            if let Some((old, _)) = self
                .guarantees
                .insert(atom.clone(), (exact.to_vec(), result))
            {
                self.used -= 5 + atom.arguments.len() + old.len();
            }
            self.used += nodes;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule};

    #[test]
    fn candidates_with_shared_guards_reuse_tests_without_sharing_their_cones() {
        let mut c = denotate_ir::Corpus::new();
        let gate = rel(&mut c, "gate", true);
        let seed = rel(&mut c, "seed", true);
        let q = rel(&mut c, "q", false);
        rule(&mut c, q, &[(seed, false)]);
        let pairs: Vec<_> = (0..8)
            .map(|i| {
                (
                    rel(&mut c, &format!("a{i}"), false),
                    rel(&mut c, &format!("b{i}"), false),
                )
            })
            .collect();
        let mut candidates = Vec::new();
        for (i, (a, b)) in pairs.iter().copied().enumerate() {
            candidates.push((rule(&mut c, a, &[(gate, false), (b, true), (q, true)]), b));
            candidates.push((rule(&mut c, b, &[(gate, false), (a, true)]), a));
            rule(&mut c, a, &[(pairs[(i + 1) % pairs.len()].0, false)]);
            rule(&mut c, b, &[(pairs[(i + 1) % pairs.len()].1, false)]);
            rule(&mut c, q, &[(a, false)]);
        }
        let l = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &l).unwrap();
        let m = p.symbolic(&l).unwrap();
        let summaries = crate::test_support::rewrites::summaries(&p, &m, &l);
        let index = summaries
            .values()
            .fold(BTreeMap::<_, Vec<_>>::new(), |mut map, s| {
                map.entry(&s.rule.head.atom).or_default().push(s.rule.id);
                map
            });
        let mut fresh_budget = Budget::new(&l);
        let mut cached_budget = Budget::new(&l);
        fresh_budget.enable_profile();
        cached_budget.enable_profile();
        let mut cache = PruningCache::default();
        let mut held = 0;
        cache.reserve(&mut held, &mut cached_budget).unwrap();
        for (source, root) in candidates {
            let candidate = summaries
                .values()
                .find(|s| s.rule.source == source)
                .unwrap();
            let root = atom(root);
            let component = p.component_for(&root).unwrap();
            let fresh = super::super::prepare(
                &p,
                component,
                candidate,
                &root,
                &summaries,
                &index,
                m.context(),
                &mut 0,
                &mut fresh_budget,
                &mut Preparation::default(),
            )
            .unwrap();
            let cached = super::super::prepare_cached(
                &p,
                component,
                candidate,
                &root,
                &summaries,
                &index,
                m.context(),
                &mut held,
                &mut cached_budget,
                &mut Preparation::default(),
                &mut cache,
            )
            .unwrap();
            assert!(
                fresh
                    .same_computation(&cached, &mut Budget::new(&l))
                    .unwrap()
            );
            held -= cached.temporary_nodes();
            assert_eq!(held, cache.reserved());
        }
        let fresh = &fresh_budget.profile.as_ref().unwrap().calls;
        let cached = &cached_budget.profile.as_ref().unwrap().calls;
        assert!(cached["pruning liveness cache hit"] > 0);
        assert!(cached["pruning guarantee cache hit"] > 0);
        assert!(cached["BDD operation"] < fresh["BDD operation"]);
        println!(
            "pruning comparison: BDD calls {} -> {}; liveness hits {}; guarantee hits {}",
            fresh["BDD operation"],
            cached["BDD operation"],
            cached["pruning liveness cache hit"],
            cached["pruning guarantee cache hit"]
        );
        held -= cache.release();
        assert_eq!(held, 0);
    }

    #[test]
    fn reuse_requires_the_same_domain_snapshot_and_exact_producers() {
        let mut c = denotate_ir::Corpus::new();
        let i = rel(&mut c, "i", true);
        let q = rel(&mut c, "q", false);
        rule(&mut c, q, &[(i, false)]);
        let limits = Limits::default();
        let p = GroundProgram::prepare(&c, &Domains::new(), &limits).unwrap();
        let ctx = p.condition_context(&limits).unwrap();
        let id = p.rules().next().unwrap().id;
        let domain = ctx.input(&atom(i), &limits).unwrap();
        let other = ctx.complement(&domain, &mut Budget::new(&limits)).unwrap();
        let mut budget = Budget::new(&limits);
        let mut cache = PruningCache::default();
        let mut held = 0;
        cache.reserve(&mut held, &mut budget).unwrap();
        cache.select(0, &domain, &mut budget).unwrap();
        assert!(cache.live(id, |_| Ok(true), &mut budget).unwrap());
        assert!(
            cache
                .live(id, |_| panic!("recomputed liveness"), &mut budget)
                .unwrap()
        );
        assert!(
            cache
                .guaranteed(&atom(q), &[id], |_| Ok(true), &mut budget)
                .unwrap()
        );
        assert!(
            cache
                .guaranteed(
                    &atom(q),
                    &[id],
                    |_| panic!("recomputed guarantee"),
                    &mut budget
                )
                .unwrap()
        );
        // Relaxing that exact producer must not reuse the unrelaxed guarantee.
        assert!(
            !cache
                .guaranteed(&atom(q), &[], |_| Ok(false), &mut budget)
                .unwrap()
        );
        cache.select(0, &other, &mut budget).unwrap();
        assert!(!cache.live(id, |_| Ok(false), &mut budget).unwrap());
        cache.select(1, &other, &mut budget).unwrap();
        assert!(cache.live(id, |_| Ok(true), &mut budget).unwrap());
        let failure =
            cache.guaranteed(&atom(q), &[id], |_| Err(CheckError::Cancelled), &mut budget);
        assert!(matches!(failure, Err(CheckError::Cancelled)));
        assert!(
            cache
                .guaranteed(&atom(q), &[id], |_| Ok(true), &mut budget)
                .unwrap()
        );
        assert!(cache.used <= cache.reserved());
        held -= cache.release();
        assert_eq!(held, 0);
        cache.reserve(&mut held, &mut budget).unwrap();
        assert_eq!(
            held, 0,
            "pressure eviction disables reuse until the next snapshot"
        );
        // A domain which cannot fit is a bypass, including with no work left for
        // a representation scan; it must not manufacture a budget exhaustion.
        let mut tiny = PruningCache {
            allowance: 1,
            ..PruningCache::default()
        };
        let no_work = Limits {
            max_work: 0,
            ..limits
        };
        tiny.select(0, &domain, &mut Budget::new(&no_work)).unwrap();
        assert!(tiny.domain.is_none());
        assert_eq!(tiny.used, 0);
    }
}
