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
    // Search guards are deliberately generous; time, not an accidentally small
    // child work allowance, binds automatic CLI exploration. Keep explicit caps.
    let seconds = l
        .timeout
        .as_secs()
        .saturating_add(u64::from(l.timeout.subsec_nanos() != 0))
        .max(1);
    let scale = |rate: u64| rate.saturating_mul(seconds);
    let work = usize::try_from(scale(1_000_000_000)).unwrap_or(usize::MAX);
    set!(max_work, "--max-work", work);
    macro_rules! query {
        ($field:ident, $flag:literal, $value:expr) => {
            if !explicit.contains($flag) {
                q.$field = $value;
            }
        };
    }
    query!(max_solves, "--sat-max-solves", scale(100_000) as usize);
    query!(
        max_refinements,
        "--sat-max-refinements",
        scale(100_000) as usize
    );
    query!(
        max_solver_polls,
        "--sat-max-polls",
        scale(100_000_000) as usize
    );
    query!(max_conflicts, "--sat-max-conflicts", scale(1_000_000_000));
    query!(
        max_propagations,
        "--sat-max-propagations",
        scale(10_000_000_000)
    );
    l.search_guards = Some(denotate_check::SearchGuards {
        work: (!explicit.contains("--max-work")).then_some(l.max_work),
        solves: (!explicit.contains("--sat-max-solves")).then_some(q.max_solves),
        polls: (!explicit.contains("--sat-max-polls")).then_some(q.max_solver_polls),
        conflicts: (!explicit.contains("--sat-max-conflicts")).then_some(q.max_conflicts),
        propagations: (!explicit.contains("--sat-max-propagations")).then_some(q.max_propagations),
        worlds: (!explicit.contains("--sat-max-worlds")).then_some(100_000),
    });
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
    fn time_scaled_guards_leave_structural_caps_and_explicit_limits_alone() {
        let mut short = Limits::default();
        let mut sq = QueryLimits::default();
        apply(&mut short, &mut sq, &BTreeSet::new());
        let mut long = Limits {
            timeout: Duration::from_secs(360),
            ..Default::default()
        };
        let mut lq = QueryLimits::default();
        apply(&mut long, &mut lq, &BTreeSet::from(["--timeout-ms".into()]));
        assert!(long.max_work > short.max_work && lq.max_solver_polls > sq.max_solver_polls);
        assert_eq!(
            (short.max_atoms, short.max_rules, short.max_dependencies),
            (long.max_atoms, long.max_rules, long.max_dependencies)
        );
        let mut limited = Limits {
            max_work: 17,
            ..Default::default()
        };
        let mut q = QueryLimits {
            max_solver_polls: 19,
            ..Default::default()
        };
        apply(
            &mut limited,
            &mut q,
            &BTreeSet::from([
                "--max-work".into(),
                "--sat-max-polls".into(),
                "--sat-max-worlds".into(),
            ]),
        );
        assert_eq!(limited.max_work, 17);
        assert_eq!(q.max_solver_polls, 19);
        let policy = limited.search_guards.unwrap();
        assert!(policy.work.is_none() && policy.polls.is_none() && policy.worlds.is_none());
    }
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
