//! Cumulative SAT allowances. A ledger is one scope's allowance of solves,
//! solver polls, conflicts and propagations: its caps, what its solves used, and
//! the enclosing scope. Every solve debits its ledger and each ancestor exactly
//! once, so replacing, resuming or nesting a solver never refreshes an
//! allowance. `used > cap` exhausts a resource; a solve is refused before it
//! starts when no solve remains or an earlier call already overshot.
use super::*;

pub(super) struct SatLedger {
    caps: QueryLimits,
    used: std::sync::Mutex<QueryLimits>,
    parent: Option<Arc<SatLedger>>,
}

pub(super) fn unbounded() -> QueryLimits {
    QueryLimits {
        max_solves: usize::MAX,
        max_solver_polls: usize::MAX,
        max_conflicts: u64::MAX,
        max_propagations: u64::MAX,
    }
}

fn zero() -> QueryLimits {
    QueryLimits {
        max_solves: 0,
        max_solver_polls: 0,
        max_conflicts: 0,
        max_propagations: 0,
    }
}

/// What a call may still use: the smallest remaining balance over the chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Remaining {
    pub polls: usize,
    pub conflicts: u64,
    pub propagations: u64,
}

impl SatLedger {
    pub(super) fn root(caps: QueryLimits) -> Arc<Self> {
        Arc::new(Self {
            caps,
            used: std::sync::Mutex::new(zero()),
            parent: None,
        })
    }
    pub(super) fn child(self: &Arc<Self>, caps: QueryLimits) -> Arc<Self> {
        Arc::new(Self {
            caps,
            used: std::sync::Mutex::new(zero()),
            parent: Some(self.clone()),
        })
    }
    fn chain(&self) -> impl Iterator<Item = &SatLedger> {
        std::iter::successors(Some(self), |l| l.parent.as_deref())
    }
    pub(super) fn used(&self) -> QueryLimits {
        self.used.lock().unwrap().clone()
    }
    /// Tests: the same scope, but no further solve allowed.
    #[cfg(test)]
    pub(super) fn no_more_solves(&self) -> Arc<Self> {
        let used = self.used();
        Arc::new(Self {
            caps: QueryLimits {
                max_solves: used.max_solves,
                ..self.caps.clone()
            },
            used: std::sync::Mutex::new(used),
            parent: self.parent.clone(),
        })
    }
    /// Restart this scope's own counts (obligation parts); ancestors keep theirs.
    pub(super) fn reset(&self) {
        *self.used.lock().unwrap() = zero();
    }
    /// Refuse a call before it starts: a solve must remain in every scope, and no
    /// scope may already be past a cap (an earlier checkpoint overshoot).
    pub(super) fn admit(&self, b: &mut Budget<'_>) -> Result<()> {
        for l in self.chain() {
            let used = l.used();
            b.room(
                used.max_solves,
                l.caps.max_solves,
                "completion solve",
                "solves",
            )?;
        }
        match self.exhausted() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
    pub(super) fn remaining(&self) -> Remaining {
        let mut r = Remaining {
            polls: usize::MAX,
            conflicts: u64::MAX,
            propagations: u64::MAX,
        };
        for l in self.chain() {
            let used = l.used();
            r.polls = r.polls.min(
                l.caps
                    .max_solver_polls
                    .saturating_sub(used.max_solver_polls),
            );
            r.conflicts = r
                .conflicts
                .min(l.caps.max_conflicts.saturating_sub(used.max_conflicts));
            r.propagations = r.propagations.min(
                l.caps
                    .max_propagations
                    .saturating_sub(used.max_propagations),
            );
        }
        r
    }
    pub(super) fn debit(&self, d: &QueryLimits) {
        for l in self.chain() {
            let mut used = l.used.lock().unwrap();
            used.max_solves = used.max_solves.saturating_add(d.max_solves);
            used.max_solver_polls = used.max_solver_polls.saturating_add(d.max_solver_polls);
            used.max_conflicts = used.max_conflicts.saturating_add(d.max_conflicts);
            used.max_propagations = used.max_propagations.saturating_add(d.max_propagations);
        }
    }
    /// The first resource past its cap, innermost scope first, in the order
    /// conflicts, propagations, solver polls.
    pub(super) fn exhausted(&self) -> Option<CheckError> {
        let over = |resource, used: u64, cap: u64| {
            (used > cap).then(|| {
                CheckError::limit(
                    "completion solve",
                    resource,
                    cap.try_into().unwrap_or(usize::MAX),
                    Some(used.try_into().unwrap_or(usize::MAX)),
                )
            })
        };
        for (resource, pick) in [
            ("conflicts", 0usize),
            ("propagations", 1),
            ("solver polls", 2),
        ] {
            for l in self.chain() {
                let used = l.used();
                let (u, c) = match pick {
                    0 => (used.max_conflicts, l.caps.max_conflicts),
                    1 => (used.max_propagations, l.caps.max_propagations),
                    _ => (used.max_solver_polls as u64, l.caps.max_solver_polls as u64),
                };
                if let Some(error) = over(resource, u, c) {
                    return Some(error);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn caps(solves: usize, polls: usize, conflicts: u64, propagations: u64) -> QueryLimits {
        QueryLimits {
            max_solves: solves,
            max_solver_polls: polls,
            max_conflicts: conflicts,
            max_propagations: propagations,
        }
    }
    #[test]
    fn a_debit_reaches_every_ancestor_once_and_the_smallest_balance_binds() {
        let root = SatLedger::root(caps(10, 100, 50, 500));
        let child = root.child(caps(3, 1000, 1000, 20));
        child.debit(&caps(1, 10, 5, 7));
        assert_eq!(root.used().max_conflicts, 5);
        assert_eq!(child.used().max_conflicts, 5);
        assert_eq!(
            child.remaining(),
            Remaining {
                polls: 90,
                conflicts: 45,
                propagations: 13
            }
        );
        // A sibling scope starts fresh locally but sees the shared root.
        let sibling = root.child(unbounded());
        assert_eq!(sibling.remaining().conflicts, 45);
    }
    #[test]
    fn solves_are_refused_at_the_cap_and_other_resources_only_past_it() {
        let limits = Limits::default();
        let mut b = Budget::new(&limits);
        let root = SatLedger::root(caps(1, 0, 0, 0));
        // Zero conflicts allowed still admits a conflict-free solve.
        assert!(root.admit(&mut b).is_ok());
        root.debit(&caps(1, 0, 0, 0));
        assert!(matches!(
            root.admit(&mut b),
            Err(CheckError::LimitExceeded {
                resource: "solves",
                ..
            })
        ));
        let other = SatLedger::root(caps(5, 0, 0, 0));
        other.debit(&caps(1, 0, 1, 0));
        assert!(matches!(
            other.admit(&mut b),
            Err(CheckError::LimitExceeded {
                resource: "conflicts",
                ..
            })
        ));
        other.reset();
        assert!(other.admit(&mut b).is_ok());
    }
}

impl Engine {
    /// A new run's ledger: capped by this engine's `config`, debiting the scope.
    pub(super) fn run_ledger(&self) -> Arc<SatLedger> {
        match &self.ledger {
            Some(scope) => scope.child(self.config.clone()),
            None => SatLedger::root(self.config.clone()),
        }
    }
    /// This engine inside a scope: itself if it already has one, otherwise a
    /// copy owning a fresh scope capped by `config`. Questions and standalone
    /// passes call this at entry so all their runs share one allowance.
    pub(super) fn scoped(&self) -> std::borrow::Cow<'_, Engine> {
        if self.ledger.is_some() {
            std::borrow::Cow::Borrowed(self)
        } else {
            std::borrow::Cow::Owned(self.with_scope())
        }
    }
    /// A copy owning a fresh scope, whatever scope this engine is in (a pass
    /// that must not debit, or be limited by, the caller's question).
    pub(super) fn with_scope(&self) -> Engine {
        let mut e = self.clone();
        e.ledger = Some(SatLedger::root(self.config.clone()));
        e
    }
    /// A copy whose runs debit a child scope of this engine's scope, capped by
    /// `caps` (and by every enclosing scope).
    pub(super) fn sub_scope(&self, caps: QueryLimits) -> Engine {
        let mut e = self.clone();
        e.ledger = Some(match &self.ledger {
            Some(scope) => scope.child(caps.clone()),
            None => SatLedger::root(caps.clone()),
        });
        e.config = caps;
        e
    }
}
