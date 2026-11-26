//! Cumulative SAT allowances on real solves (024.46a acceptance).
use super::*;
use crate::sat_probe::completion_query::ledger::{SatLedger, unbounded};
use crate::sat_probe::completion_query::queries::Run;

fn engine(config: QueryLimits) -> Engine {
    let mut c = Corpus::new();
    rel(&mut c, "input", true);
    let v = verification(&mut c, None, &[]);
    let mut e = prepare(&c, v, &Default::default());
    e.config = config;
    e
}
fn caps(f: impl FnOnce(&mut QueryLimits)) -> QueryLimits {
    let mut q = unbounded();
    f(&mut q);
    q
}
/// Seven pigeons in six holes behind `gate`: hard UNSAT under `gate`, trivially
/// satisfiable under `!gate`.
fn pigeonhole(run: &mut Run<'_, '_, '_>) -> Lit {
    let gate = run.cnf.var(run.budget).unwrap();
    let (pigeons, holes) = (7, 6);
    let mut x = vec![];
    for _ in 0..pigeons * holes {
        x.push(run.cnf.var(run.budget).unwrap());
    }
    for p in 0..pigeons {
        let mut c: Vec<_> = (0..holes).map(|h| x[p * holes + h]).collect();
        c.push(!gate);
        run.cnf.clause(c, run.budget).unwrap();
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                run.cnf
                    .clause(
                        vec![!x[p * holes + h], !x[q * holes + h], !gate],
                        run.budget,
                    )
                    .unwrap();
            }
        }
    }
    gate
}
fn resource(error: CheckError) -> &'static str {
    inconclusive(error).unwrap().resource
}

/// What the pigeonhole search uses when nothing stops it.
fn unlimited() -> QueryLimits {
    let e = engine(unbounded());
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert!(!run.raw_solve(&[gate]).unwrap());
    run.usage()
}

#[test]
fn a_solve_stops_inside_the_call_at_each_allowance() {
    let full = unlimited();
    assert!(full.max_conflicts > 200 && full.max_solver_polls > 200);
    for (name, config) in [
        ("conflicts", caps(|q| q.max_conflicts = 10)),
        ("propagations", caps(|q| q.max_propagations = 10)),
        ("solver polls", caps(|q| q.max_solver_polls = 10)),
    ] {
        let e = engine(config);
        let mut b = Budget::new(&e.limits);
        let mut run = Run::universe(&e, &mut b).unwrap();
        let gate = pigeonhole(&mut run);
        let error = run.raw_solve(&[gate]).unwrap_err();
        assert_eq!(resource(error), name);
        let used = run.usage();
        assert_eq!(used.max_solves, 1);
        let (used, all) = match name {
            "conflicts" => (used.max_conflicts, full.max_conflicts),
            "propagations" => (used.max_propagations, full.max_propagations),
            _ => (used.max_solver_polls as u64, full.max_solver_polls as u64),
        };
        // Stopped at the first checkpoint past the cap (cooperative: batsat
        // checks between decisions), long before the search would end.
        assert!(used > 10 && used < all / 4, "{name}: {used} of {all}");
    }
}

#[test]
fn a_call_with_no_solve_left_is_refused_before_it_starts() {
    let e = engine(caps(|q| q.max_solves = 0));
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert_eq!(resource(run.raw_solve(&[!gate]).unwrap_err()), "solves");
    assert_eq!(run.solves(), 0, "no solve issued");
    // Zero conflicts allowed still admits a conflict-free solve.
    let e = engine(caps(|q| q.max_conflicts = 0));
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert!(run.raw_solve(&[!gate]).unwrap());
}

#[test]
fn runs_in_one_scope_share_its_allowance_and_a_new_solver_is_not_a_refresh() {
    let e = engine(caps(|q| q.max_conflicts = 30));
    let scoped = e.with_scope();
    let mut b = Budget::new(&e.limits);
    {
        let mut first = Run::universe(&scoped, &mut b).unwrap();
        let gate = pigeonhole(&mut first);
        assert_eq!(resource(first.raw_solve(&[gate]).unwrap_err()), "conflicts");
    }
    // A fresh solver in the same scope: refused before it starts, no solve issued.
    {
        let mut second = Run::universe(&scoped, &mut b).unwrap();
        let gate = pigeonhole(&mut second);
        assert_eq!(
            resource(second.raw_solve(&[!gate]).unwrap_err()),
            "conflicts"
        );
        assert_eq!(second.solves(), 0);
    }
    let total = scoped.ledger.as_ref().unwrap().used();
    assert_eq!(total.max_solves, 1);
    assert!(total.max_conflicts > 30);
    // A scope below it starts with what the question has left, not a new cap.
    let unit = scoped.sub_scope(caps(|q| q.max_conflicts = 1000));
    let mut third = Run::universe(&unit, &mut b).unwrap();
    let gate = pigeonhole(&mut third);
    assert_eq!(
        resource(third.raw_solve(&[!gate]).unwrap_err()),
        "conflicts"
    );
}

#[test]
fn local_uniqueness_solvers_debit_the_enclosing_run() {
    let e = engine(unbounded());
    let scoped = e.with_scope();
    let mut b = Budget::new(&e.limits);
    let mut run = Run::local(&scoped, &mut b).unwrap();
    let cone = (*e.cone).clone();
    let (answer, _, _, _) = run.local_unique(&cone, |_, _| {});
    answer.unwrap();
    assert_eq!(
        run.solves(),
        1,
        "the replacement solver's solve stays charged"
    );
    assert_eq!(scoped.ledger.as_ref().unwrap().used().max_solves, 1);
}

#[test]
fn an_obligation_part_restarts_only_the_run_allowance() {
    let e = engine(caps(|q| q.max_solves = 1));
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert!(run.raw_solve(&[!gate]).unwrap());
    assert_eq!(resource(run.raw_solve(&[!gate]).unwrap_err()), "solves");
    run.next_property_part().unwrap();
    assert!(run.raw_solve(&[!gate]).unwrap());
}

#[test]
fn an_interrupted_incremental_solver_answers_a_later_authorized_query() {
    let e = engine(caps(|q| q.max_conflicts = 10));
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert_eq!(resource(run.raw_solve(&[gate]).unwrap_err()), "conflicts");
    // Authorize more: the stale budget must not stop the solver.
    run.ledger = SatLedger::root(unbounded());
    assert!(run.raw_solve(&[!gate]).unwrap());
    assert!(!run.raw_solve(&[gate]).unwrap(), "pigeonhole stays UNSAT");
}

#[test]
fn cancellation_wins_over_an_allowance_inside_a_call() {
    let e = engine(caps(|q| q.max_conflicts = 0));
    let mut b = Budget::new(&e.limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    let token = e.limits.cancellation.clone();
    run.cnf.solver.cb_mut().hook = Some(Box::new(move || token.cancel()));
    assert!(matches!(run.raw_solve(&[gate]), Err(CheckError::Cancelled)));
}

#[test]
fn certification_runs_share_and_debit_the_parent_run_allowance() {
    let e = engine(caps(|q| q.max_conflicts = 20));
    let mut b = Budget::new(&e.limits);
    let parent = Run::universe(&e, &mut b).unwrap().ledger.clone();
    let mut nested = Run::universe_under(&e, &mut b, &parent).unwrap();
    let gate = pigeonhole(&mut nested);
    assert_eq!(
        resource(nested.raw_solve(&[gate]).unwrap_err()),
        "conflicts"
    );
    let own = nested.usage();
    drop(nested);
    // Charged once to the parent, interruption included.
    let charged = parent.used();
    assert_eq!(charged.max_solves, 1);
    assert!(charged.max_conflicts > 20);
    assert_eq!(
        (
            charged.max_conflicts,
            charged.max_propagations,
            charged.max_solver_polls
        ),
        (
            own.max_conflicts,
            own.max_propagations,
            own.max_solver_polls
        )
    );
}

#[test]
fn a_probe_work_stop_is_reported_as_work() {
    let mut e = engine(unbounded());
    e.probe = true;
    // Measure the setup's work, then leave five units for the solve.
    let setup = {
        let mut b = Budget::new(&e.limits);
        let mut run = Run::universe(&e, &mut b).unwrap();
        pigeonhole(&mut run);
        drop(run);
        b.used()
    };
    let mut limits = e.limits.clone();
    limits.max_work = setup + 6;
    let mut b = Budget::new(&limits);
    let mut run = Run::universe(&e, &mut b).unwrap();
    let gate = pigeonhole(&mut run);
    assert_eq!(resource(run.raw_solve(&[gate]).unwrap_err()), "work");
}
