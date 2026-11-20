//! Uniqueness queries and fixed (input-independent) cardinality checks.
use super::*;
use crate::coverage::COVERAGE_EXAMPLE_LIMIT;
use denotate_ir::ObligationId;

impl Engine {
    pub(super) fn fixed_relation(&self, relation: RelationId) -> bool {
        !self.residual_relations.contains(&relation)
    }
    pub(super) fn check_cardinality(
        &mut self,
        id: ObligationId,
        kind: Cardinality,
        relation: RelationId,
        fixed: bool,
        world: &Model,
        keys: &SemanticKeys,
        report: &mut Report,
        retained: &mut Vec<(usize, Model)>,
    ) -> Result<()> {
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        let result: Result<()> = (|| {
            let cols = &self.columns[&id];
            let mut groups = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
            for a in self.program.atoms().filter(|a| a.relation == relation) {
                b.charge(a.arguments.len() + 1, "SAT obligation groups")?;
                groups
                    .entry(cols.iter().map(|i| a.arguments[*i]).collect())
                    .or_default()
                    .push(a.clone());
            }
            let mut ordered = groups
                .into_iter()
                .map(|(g, ts)| {
                    Ok((
                        g.iter()
                            .map(|c| keys.constant(*c).cloned().map_err(CheckError::Keys))
                            .collect::<Result<Vec<_>>>()?,
                        g,
                        ts,
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            ordered.sort_by(|a, b| a.0.cmp(&b.0));
            if kind.has_coverage() {
                // This branch is only reachable for fixed relations. Enumerate
                // resolved domain groups, including groups with no producer.
                let mut coverage = CoverageReport::default();
                let coverage_result: Result<()> = (|| {
                    let signature = &self.program.signatures[&relation];
                    let mut domains = Vec::new();
                    for col in cols {
                        let mut d = self.program.domains[&signature[*col]].clone();
                        b.charge(d.len(), "SAT fixed coverage domains")?;
                        d.sort_by_key(|c| keys.constant(*c).unwrap());
                        domains.push(d);
                    }
                    if domains.iter().any(Vec::is_empty) {
                        coverage.no_groups = true;
                        return Ok(());
                    }
                    let present = ordered
                        .iter()
                        .filter(|(_, _, ts)| ts.iter().any(|a| world.value(a) == Some(true)))
                        .map(|(_, g, _)| g.clone())
                        .collect::<BTreeSet<_>>();
                    let mut pos = vec![0; domains.len()];
                    loop {
                        b.room(
                            coverage.examined,
                            limits.max_atoms,
                            "SAT fixed coverage",
                            "groups",
                        )?;
                        let group = domains
                            .iter()
                            .zip(&pos)
                            .map(|(d, p)| d[*p])
                            .collect::<Vec<_>>();
                        coverage.examined += 1;
                        if !present.contains(&group) {
                            coverage.missing += 1;
                            if coverage.examples.len() < COVERAGE_EXAMPLE_LIMIT {
                                coverage.examples.push(CoverageExample {
                                    group,
                                    observation: world.observation_precharged(),
                                    replay_scope: ReplayScope::ConeOnly,
                                    dependency_inputs: Some(Attribution::Complete(BTreeSet::new())),
                                });
                            }
                        }
                        let mut advanced = false;
                        for i in (0..pos.len()).rev() {
                            pos[i] += 1;
                            if pos[i] < domains[i].len() {
                                advanced = true;
                                break;
                            }
                            pos[i] = 0;
                        }
                        if !advanced {
                            return Ok(());
                        }
                    }
                })();
                if let Err(e) = coverage_result {
                    self.limits.progress.failure(&e);
                    coverage.inconclusive = Some(query_inconclusive(e)?);
                }
                report.coverage.insert(id, coverage);
            }
            if !kind.has_uniqueness() {
                return Ok(());
            }
            for (_, key, tuples) in ordered {
                b.tick("SAT uniqueness groups")?;
                if tuples.len() < 2 {
                    continue;
                }
                let group = AtMostOneGroup {
                    obligation: id,
                    key,
                    tuples,
                };
                // Reserve materialising the answer before asking for a violation.
                b.charge(
                    group.tuples.len() + self.program.inputs.len(),
                    "SAT uniqueness answer",
                )?;
                let answer = if fixed {
                    if group
                        .tuples
                        .iter()
                        .filter(|a| world.value(a) == Some(true))
                        .count()
                        > 1
                    {
                        Answer::Model(world.clone())
                    } else {
                        Answer::NoModel
                    }
                } else {
                    self.overlap(&group.tuples, &mut b)?
                };
                let outcome = match answer {
                    Answer::NoModel => VerifiedOutcome::Proved,
                    Answer::Inconclusive(c) => VerifiedOutcome::Inconclusive(c),
                    Answer::Model(m) => {
                        let tuples = group
                            .tuples
                            .iter()
                            .filter(|a| m.value(a) == Some(true))
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        if tuples.len() < 2 {
                            return Err(CheckError::Internal("SAT overlap did not replay"));
                        }
                        retained.push((report.groups.len(), m.clone()));
                        VerifiedOutcome::Counterexample(Counterexample {
                            observation: m.observation_precharged(),
                            replay_scope: if fixed || self.scope_atoms.is_some() {
                                ReplayScope::ConeOnly
                            } else {
                                ReplayScope::WholeProgram
                            },
                            dependency_inputs: None,
                            tuples,
                            evidence: BTreeMap::new(),
                            incomplete_attribution: BTreeMap::new(),
                            certification: None,
                            confined_to_no_meaning: vec![],
                        })
                    }
                };
                report.groups.push(VerifiedGroup {
                    cone: DependencyCone {
                        roots: group.tuples.iter().cloned().collect(),
                        facts: BTreeSet::new(),
                        rules: BTreeSet::new(),
                        components: BTreeSet::new(),
                        blocked_by: BTreeSet::new(),
                    },
                    group,
                    outcome,
                });
            }
            Ok(())
        })();
        if let Err(e) = result {
            self.limits.progress.failure(&e);
            report
                .incomplete
                .insert(id, query_inconclusive(e.in_phase("SAT cardinality", None))?);
        }
        Ok(())
    }
    fn overlap(&mut self, tuples: &[GroundAtom], b: &mut Budget<'_>) -> Result<Answer> {
        if let Some(e) = &self.append_failed {
            return Ok(Answer::Inconclusive(query_inconclusive(e.clone())?));
        }
        self.stats = Stats::default();
        let conflicts = self.cnf.solver.num_conflicts();
        let propagations = self.cnf.solver.num_propagations();
        let stop = self.cnf.solver.cb_mut();
        stop.start = Instant::now();
        stop.timeout = b.remaining_time();
        stop.polls = Some(PollLimit {
            used: std::cell::Cell::new(0),
            max: self.config.max_solver_polls,
        });
        let result: Result<Answer> = (|| {
            let built: Result<Lit> = (|| {
                let gate = self.cnf.var(b)?;
                self.cnf.gate = Some(gate);
                let mut seen = !self.truth;
                let mut many = !self.truth;
                for a in tuples {
                    b.tick("SAT overlap encoding")?;
                    let l = match resolve(&self.program, a)? {
                        Resolved::Fixed(v) => {
                            if v {
                                self.truth
                            } else {
                                !self.truth
                            }
                        }
                        Resolved::Atom(i) => self.program_encoding.vars[i],
                    };
                    let both = self.cnf.and(&[seen, l], b)?;
                    many = self.cnf.or(&[many, both], b)?;
                    seen = self.cnf.or(&[seen, l], b)?;
                }
                self.cnf.clause(vec![many], b)?;
                Ok(gate)
            })();
            let gate = match built {
                Ok(g) => g,
                Err(e) => {
                    self.append_failed = Some(e.clone());
                    return Err(e);
                }
            };
            self.search(
                Mode::Program,
                &[self.active, gate],
                conflicts,
                propagations,
                b,
            )
        })();
        self.cnf.solver.cb_mut().timeout = self.limits.timeout;
        match result {
            Ok(a) => Ok(a),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok(Answer::Inconclusive(query_inconclusive(
                    e.in_phase("SAT uniqueness obligation", None),
                )?))
            }
        }
    }
}
