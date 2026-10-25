//! Clark completion is an overapproximation. Only UNSAT proves an obligation;
//! a SAT observation must pass the existing concrete least-fixed-point replay.
use super::*;
use batsat::{Callbacks, Lit, Solver, SolverInterface, lbool};

struct Stop {
    operations: OperationalLimits,
    started: Instant,
    #[cfg(test)]
    polls: std::sync::atomic::AtomicUsize,
    #[cfg(test)]
    poll_action: Option<Box<dyn Fn(usize) + Send + Sync>>,
}
impl Stop {
    fn check(&self) -> Result<()> {
        self.operations.cancellation.check()?;
        if self.started.elapsed() >= self.operations.timeout {
            return Err(CheckError::Deadline { phase: "SAT query" });
        }
        Ok(())
    }
}
impl Callbacks for Stop {
    fn stop(&self) -> bool {
        #[cfg(test)]
        if let Some(action) = &self.poll_action {
            action(
                self.polls
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    + 1,
            );
        }
        self.check().is_err()
    }
}

struct Encoding {
    solver: Solver<Stop>,
}
impl Encoding {
    fn new(operations: &OperationalLimits) -> Self {
        Self {
            solver: Solver::new(
                Default::default(),
                Stop {
                    operations: operations.clone(),
                    started: Instant::now(),
                    #[cfg(test)]
                    polls: Default::default(),
                    #[cfg(test)]
                    poll_action: None,
                },
            ),
        }
    }
    fn var(&mut self) -> Result<Lit> {
        self.solver.cb().check()?;
        if self.solver.num_vars() >= (u32::MAX / 2) - 2 {
            return Err(CheckError::LimitExceeded {
                phase: "SAT encoding",
                resource: "variables",
            });
        }
        Ok(Lit::new(self.solver.new_var_default(), true))
    }
    fn clause(&mut self, mut lits: Vec<Lit>) -> Result<()> {
        self.solver.cb().check()?;
        self.solver.add_clause_reuse(&mut lits);
        self.solver.cb().check()
    }
    fn and(&mut self, lits: &[Lit]) -> Result<Lit> {
        let v = self.var()?;
        for &lit in lits {
            self.clause(vec![!v, lit])?;
        }
        let mut reverse = vec![v];
        reverse.extend(lits.iter().map(|l| !*l));
        self.clause(reverse)?;
        Ok(v)
    }
    fn or(&mut self, lits: &[Lit]) -> Result<Lit> {
        let negated = lits.iter().map(|l| !*l).collect::<Vec<_>>();
        Ok(!self.and(&negated)?)
    }
    fn solve(&mut self, assumptions: &[Lit]) -> Result<bool> {
        self.solver.cb().check()?;
        let result = self.solver.solve_limited(assumptions);
        self.solver.cb().check()?;
        if result == lbool::TRUE {
            Ok(true)
        } else if result == lbool::FALSE {
            Ok(false)
        } else {
            Err(CheckError::Internal(
                "SAT stopped without an operational error",
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sat_interrupts_inside_search_for_cancellation_and_deadline() {
        for deadline in [false, true] {
            let ops = OperationalLimits::from(&Limits {
                timeout: Duration::from_secs(60),
                ..Limits::default()
            });
            let mut enc = Encoding::new(&ops);
            // Nine pigeons in eight holes: an actual unsatisfiable search, not
            // a pre-cancelled query or a timeout checked only after solve().
            let mut pigeons = Vec::new();
            for _ in 0..9 {
                let row = (0..8).map(|_| enc.var().unwrap()).collect::<Vec<_>>();
                enc.clause(row.clone()).unwrap();
                pigeons.push(row);
            }
            for i in 0..9 {
                for j in 0..i {
                    for h in 0..8 {
                        enc.clause(vec![!pigeons[i][h], !pigeons[j][h]]).unwrap();
                    }
                }
            }
            let token = ops.cancellation.clone();
            enc.solver.cb_mut().poll_action = Some(Box::new(move |n| {
                if n == 2 {
                    if deadline {
                        std::thread::sleep(Duration::from_millis(30));
                    } else {
                        token.cancel();
                    }
                }
            }));
            enc.solver.cb_mut().started = Instant::now();
            if deadline {
                enc.solver.cb_mut().operations.timeout = Duration::from_millis(20);
            }
            let result = enc.solve(&[]);
            assert!(
                enc.solver
                    .cb()
                    .polls
                    .load(std::sync::atomic::Ordering::Relaxed)
                    >= 2
            );
            if deadline {
                assert!(matches!(result, Err(CheckError::Deadline { .. })));
            } else {
                assert!(matches!(result, Err(CheckError::Cancelled)));
            }
        }
    }

    #[test]
    fn sat_assumptions_agree_with_exhaustive_boolean_oracle() {
        let ops = OperationalLimits::from(&Limits::default());
        for seed in 0..128_u32 {
            let mut enc = Encoding::new(&ops);
            let vars = (0..3).map(|_| enc.var().unwrap()).collect::<Vec<_>>();
            let mut rng = seed + 1;
            let mut formula = Vec::new();
            for _ in 0..5 {
                let mut clause = Vec::new();
                for _ in 0..3 {
                    rng = rng.wrapping_mul(1664525).wrapping_add(1013904223);
                    clause.push(((rng as usize >> 4) % 3, rng & 1 != 0));
                }
                enc.clause(
                    clause
                        .iter()
                        .map(|(v, positive)| if *positive { vars[*v] } else { !vars[*v] })
                        .collect(),
                )
                .unwrap();
                formula.push(clause);
            }
            for mask in 0..8 {
                let assumptions = (0..3)
                    .map(|v| {
                        if mask & (1 << v) != 0 {
                            vars[v]
                        } else {
                            !vars[v]
                        }
                    })
                    .collect::<Vec<_>>();
                let expected = formula.iter().all(|c| {
                    c.iter()
                        .any(|(v, positive)| (mask & (1 << v) != 0) == *positive)
                });
                assert_eq!(enc.solve(&assumptions).unwrap(), expected);
            }
            let any = (0..8).any(|mask| {
                formula.iter().all(|c| {
                    c.iter()
                        .any(|(v, positive)| (mask & (1 << v) != 0) == *positive)
                })
            });
            assert_eq!(
                enc.solve(&[]).unwrap(),
                any,
                "assumption UNSAT must not poison a later solve"
            );
        }
    }
}

pub(super) fn answer(
    input: &LocalInput,
    operations: &OperationalLimits,
    metrics: &mut LocalMetrics,
) -> Result<OwnedAnswer> {
    let limits = input.limits.with_operations(operations);
    let mut budget = Budget::tracked(&limits);
    let start = Instant::now();
    let computed = (|| {
        operations.cancellation.check()?;
        budget.check("SAT query")?;
        let blocked = input
            .components
            .values()
            .flat_map(|c| c.blocked_by.iter().cloned())
            .collect::<BTreeSet<_>>();
        if !blocked.is_empty() {
            if let Some(c) = input.admission_limit {
                return Err(CheckError::LimitExceeded {
                    phase: c.phase,
                    resource: c.resource,
                });
            }
            return Ok(LocalVerdict::Unsupported(
                UnsupportedReason::DependsOnUnsettled(blocked),
            ));
        }
        validate_local_constraints(&input.constraints)?;
        let mut enc = Encoding::new(operations);
        let mut all = input.facts.clone();
        all.extend(input.inputs.iter().cloned());
        all.extend(input.roots.iter().cloned());
        for rule in input.rules.values() {
            enc.solver.cb().check()?;
            all.insert(rule.head.atom.clone());
            all.extend(rule.body.iter().map(|(_, p)| p.atom.clone()));
        }
        let atoms = all
            .iter()
            .map(|a| Ok((a.clone(), enc.var()?)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        let mut producers: BTreeMap<&AtomKey, Vec<Lit>> = BTreeMap::new();
        for rule in input.rules.values() {
            if input.inputs.contains(&rule.head.atom) {
                return Err(CheckError::Internal("SAT producer for input atom"));
            }
            let body = rule
                .body
                .iter()
                .map(|(negative, p)| {
                    let lit = atoms[&p.atom];
                    if *negative { !lit } else { lit }
                })
                .collect::<Vec<_>>();
            let body = enc.and(&body)?;
            let head = atoms[&rule.head.atom];
            enc.clause(vec![!body, head])?;
            producers.entry(&rule.head.atom).or_default().push(body);
        }
        for atom in &all {
            if input.inputs.contains(atom) {
                continue;
            }
            // No producer means false. Inputs alone remain free variables.
            let mut support = vec![!atoms[atom]];
            if let Some(bodies) = producers.get(atom) {
                support.extend(bodies);
            }
            enc.clause(support)?;
        }
        // Linear sequential at-most-one constraints, preserving absent extension.
        for group in &input.input_groups {
            let mut seen: Option<Lit> = None;
            for atom in group {
                if !input.inputs.contains(atom) {
                    return Err(CheckError::Internal("SAT non-input constraint"));
                }
                let lit = atoms[atom];
                seen = Some(if let Some(previous) = seen {
                    enc.clause(vec![!previous, !lit])?;
                    enc.or(&[previous, lit])?
                } else {
                    lit
                });
            }
        }
        // A violation is at least two distinct roots, also in linear space.
        let mut seen = enc.or(&[])?;
        let mut overlap = enc.or(&[])?;
        for root in &input.roots {
            let both = enc.and(&[seen, atoms[root]])?;
            overlap = enc.or(&[overlap, both])?;
            seen = enc.or(&[seen, atoms[root]])?;
        }
        enc.clause(vec![overlap])?;
        if !enc.solve(&[])? {
            return Ok(LocalVerdict::Proved);
        }
        let mut assumptions = Vec::new();
        let mut candidate = Candidate {
            present: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for atom in &input.inputs {
            let lit = atoms[atom];
            assumptions.push(!lit);
            if enc.solve(&assumptions)? {
                candidate.absent.insert(atom.clone());
            } else {
                *assumptions.last_mut().unwrap() = lit;
                candidate.present.insert(atom.clone());
            }
        }
        // The SAT assignment of derived variables is deliberately discarded.
        // Validation uses the same concrete kernel as BDD witness replay.
        let rt = owned::Runtime::new(input, &mut budget, true)?;
        let replay = rt.program.evaluate_selected(
            candidate.present.iter().map(|a| rt.atoms[a].clone()),
            Some(&rt.cone.components),
            &mut budget,
        )?;
        let mut count = 0;
        for root in &input.roots {
            budget.tick("SAT candidate validation")?;
            match replay.fact(&rt.atoms[root])? {
                FactState::Settled(true) => count += 1,
                FactState::Settled(false) => {}
                FactState::Blocked(_) => {
                    return Err(CheckError::Internal("SAT admitted cone replay blocked"));
                }
            }
        }
        enc.solver.cb().check()?;
        Ok(if count >= 2 {
            LocalVerdict::Candidate(candidate)
        } else {
            LocalVerdict::Unsupported(UnsupportedReason::UnfoundedSupport(candidate))
        })
    })();
    metrics.property += start.elapsed();
    let (value, failure) = match computed {
        Ok(v) => (Some(LocalAnswer::Group(v)), None),
        Err(e) => {
            budget.failure(&e);
            (None, Some(Inconclusive::from_error(e)?))
        }
    };
    Ok(OwnedAnswer {
        value,
        failure,
        receipt: owned::receipt(input, &budget, true),
    })
}
