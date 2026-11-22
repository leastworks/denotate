//! CLI-only SAT exploration policy. Library, BDD and editor defaults stay unchanged.
use denotate_check::{Limits, stable_query::QueryLimits};
use std::{collections::BTreeSet, time::Duration};

pub fn apply(l: &mut Limits, q: &mut QueryLimits, explicit: &BTreeSet<String>) {
    let base = Limits::default();
    macro_rules! set {
        ($field:ident, $flag:literal, $value:expr) => {
            if !explicit.contains($flag) && l.$field == base.$field {
                l.$field = $value;
            }
        };
    }
    set!(timeout, "--timeout-ms", Duration::from_secs(120));
    set!(max_atoms, "--max-atoms", 5_000_000);
    set!(max_rules, "--max-rules", 7_000_000);
    set!(max_dependencies, "--max-dependencies", 50_000_000);
    set!(max_work, "--max-work", 2_000_000_000);
    macro_rules! query {
        ($field:ident, $flag:literal, $value:expr) => {
            if !explicit.contains($flag) {
                q.$field = $value;
            }
        };
    }
    query!(max_solves, "--sat-max-solves", 100_000);
    query!(max_refinements, "--sat-max-refinements", 100_000);
    query!(max_solver_polls, "--sat-max-polls", 100_000_000);
    query!(max_conflicts, "--sat-max-conflicts", 1_000_000_000);
    query!(max_propagations, "--sat-max-propagations", 10_000_000_000);
}

pub fn checks(c: &mut denotate_check::stable_query::CheckOptions, explicit: &BTreeSet<String>) {
    if !explicit.contains("--sat-max-worlds") {
        c.max_worlds = 100_000;
    }
    if !explicit.contains("--sat-max-tuples") {
        c.max_tuples = 5_000_000;
    }
}

pub fn start(l: &mut Limits) {
    // One deadline across preparation, all queries and all selected verifications.
    if l.run_deadline.is_none() {
        l.run_deadline = std::time::Instant::now().checked_add(l.timeout);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn profile_is_cli_local_and_explicit_flags_win() {
        let default = Limits::default();
        let mut l = default.clone();
        let mut q = QueryLimits::default();
        apply(&mut l, &mut q, &BTreeSet::new());
        assert!(l.max_atoms > default.max_atoms && l.timeout > default.timeout);
        assert!(l.run_deadline.is_none());
        let mut explicit = BTreeSet::new();
        for flag in ["--max-atoms", "--timeout-ms", "--sat-max-polls"] {
            explicit.insert(flag.into());
        }
        let mut l = Limits::default();
        let mut q = QueryLimits::default();
        apply(&mut l, &mut q, &explicit);
        assert_eq!(l.max_atoms, default.max_atoms);
        assert_eq!(l.timeout, default.timeout);
        assert_eq!(q.max_solver_polls, QueryLimits::default().max_solver_polls);
        start(&mut l);
        let first = l.run_deadline;
        start(&mut l);
        assert_eq!(
            l.run_deadline, first,
            "later phases never restart the deadline"
        );
        assert!(Limits::default().run_deadline.is_none());
    }
}
