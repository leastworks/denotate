//! Whole-verification results. Property truth never substitutes for meaning.
use super::*;
use denotate_ir::{NoticeId, ObligationId};
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Context {
    Permitted,
    EmptyUniverse,
    InconsistentAssumptions,
    Inconclusive(Inconclusive),
}
#[derive(Debug, Clone)]
pub struct CheckOptions {
    pub max_worlds: usize,
    pub max_tuples: usize,
    pub examples: EmptinessExamples,
    /// Independent per-example allowance; cannot change semantic completeness.
    /// Uses the engine's cancellation token, regardless of this value's token.
    pub attribution: Limits,
}
impl Default for CheckOptions {
    fn default() -> Self {
        Self {
            max_worlds: 1024,
            max_tuples: 10000,
            examples: Default::default(),
            attribution: Limits::default(),
        }
    }
}
#[derive(Debug)]
pub struct Report {
    pub verification: VerificationId,
    pub context: Context,
    pub meaning: Option<Meaning>,
    /// Counts distinct tuples possible in stable models, not worlds. A complete
    /// zero count alone does NOT establish existence or uniqueness of meaning.
    pub emptiness: BTreeMap<ObligationId, EmptinessReport>,
    pub not_analysed: BTreeSet<ObligationId>,
    pub notices_not_analysed: BTreeSet<NoticeId>,
    program: Arc<GroundProgram>,
}
impl Report {
    pub fn has_failures(&self) -> bool {
        self.emptiness.values().any(|e| e.present > 0)
    }
    pub fn proved(&self) -> bool {
        self.context == Context::Permitted
            && self
                .meaning
                .as_ref()
                .is_some_and(Meaning::unique_everywhere)
            && self.not_analysed.is_empty()
            && self.emptiness.values().all(EmptinessReport::proved)
    }
    pub fn program(&self) -> &GroundProgram {
        &self.program
    }
}
impl Engine {
    /// Check this engine's selected obligations. This increment analyses empty
    /// only; other kinds and notices are explicitly listed as not analysed.
    pub fn check(&mut self, keys: &SemanticKeys, options: &CheckOptions) -> Result<Report> {
        self.limits.cancellation.check()?;
        let mut report = Report {
            verification: self.verification,
            context: Context::Permitted,
            meaning: None,
            emptiness: BTreeMap::new(),
            not_analysed: self.selection.iter().map(|s| s.0).collect(),
            notices_not_analysed: self.notices.clone(),
            program: self.program.clone(),
        };
        if self.program.input_universe_is_empty() {
            report.context = Context::EmptyUniverse;
            return Ok(report);
        }
        report.context = match self.worlds(&Query::default())? {
            Answer::NoModel => Context::InconsistentAssumptions,
            Answer::Inconclusive(c) => Context::Inconclusive(c),
            Answer::Model(_) => Context::Permitted,
        };
        if report.context != Context::Permitted {
            return Ok(report);
        }
        // Preserve property failures even if the later meaning search exhausts.
        let mut retained = BTreeMap::new();
        for (id, kind, relation) in self.selection.clone() {
            if kind != Cardinality::Empty {
                continue;
            }
            let (empty, models) = self.empty(relation, keys, options)?;
            report.emptiness.insert(id, empty);
            retained.insert(id, models);
            report.not_analysed.remove(&id);
        }
        report.meaning = Some(self.meaning(options)?);
        // Diagnostic work is last and has no dependency on the remaining SAT budget.
        let mut attribution = options.attribution.clone();
        attribution.cancellation = self.limits.cancellation.clone();
        for (id, empty) in &mut report.emptiness {
            for example in &mut empty.examples {
                let model = &retained[id][&example.tuple];
                model.attribute(example, &attribution)?;
            }
        }
        Ok(report)
    }
    pub(super) fn phase_query(
        &mut self,
        mode: Mode,
        q: &Query,
        b: &mut Budget<'_>,
    ) -> Result<Answer> {
        b.check("SAT checking")?;
        let timeout = self.cnf.solver.cb().timeout;
        self.cnf.solver.cb_mut().timeout = timeout.min(b.remaining_time());
        let result = self.query_using(mode, q, b);
        self.cnf.solver.cb_mut().timeout = timeout;
        result
    }
    fn empty(
        &mut self,
        relation: RelationId,
        keys: &SemanticKeys,
        options: &CheckOptions,
    ) -> Result<(EmptinessReport, BTreeMap<GroundAtom, Model>)> {
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        let mut report = EmptinessReport::default();
        let mut models = BTreeMap::new();
        let result: Result<()> = (|| {
            let mut remaining = BTreeSet::new();
            for atom in self.program.atoms() {
                b.tick("SAT emptiness candidates")?;
                if atom.relation == relation {
                    remaining.insert(atom.clone());
                }
            }
            loop {
                b.check("SAT emptiness")?;
                if remaining.is_empty() {
                    return Ok(());
                }
                if options.max_tuples == 0 {
                    return Err(CheckError::limit("SAT emptiness", "tuples", 0, None));
                }
                // The negation of the all-absent cube is an aggregate violation
                // query. Counting a tuple removes it, never its input world.
                b.charge(remaining.len(), "SAT emptiness query")?;
                let query = Query {
                    pins: vec![],
                    exclude: vec![remaining.iter().map(|a| (a.clone(), false)).collect()],
                };
                // Reserve answer inspection before solving. Once a violation is
                // reduct-confirmed, running out of work while materialising its
                // world/tuple must not erase the failure we already established.
                b.charge(
                    remaining.len().saturating_add(self.program.inputs.len()),
                    "SAT emptiness answer",
                )?;
                let model = match self.phase_query(Mode::Program, &query, &mut b)? {
                    Answer::NoModel => return Ok(()),
                    Answer::Inconclusive(c) => return Err(c.into()),
                    Answer::Model(m) => m,
                };
                let observation = model.observation_precharged();
                let mut found = Vec::new();
                for atom in &remaining {
                    limits.cancellation.check()?;
                    if model.value(atom) == Some(true) {
                        if report.present >= options.max_tuples {
                            return Err(CheckError::limit(
                                "SAT emptiness",
                                "tuples",
                                options.max_tuples,
                                report.present.checked_add(1),
                            ));
                        }
                        report.present += 1;
                        crate::emptiness::retain_example(
                            &mut report,
                            atom,
                            &observation,
                            ReplayScope::WholeProgram,
                            Some(keys),
                            options.examples.limit(),
                        )?;
                        // Only retained examples hold a model. All tuples are counted.
                        if options.examples.limit() != usize::MAX {
                            models.retain(|a, _| report.examples.iter().any(|e| e.tuple == *a));
                        }
                        if options.examples.limit() == usize::MAX
                            || report.examples.iter().any(|e| e.tuple == *atom)
                        {
                            models.insert(atom.clone(), model.clone());
                        }
                        found.push(atom.clone());
                    }
                }
                if found.is_empty() {
                    return Err(CheckError::Internal(
                        "aggregate SAT violation has no present tuple",
                    ));
                }
                for atom in found {
                    remaining.remove(&atom);
                }
            }
        })();
        if let Err(e) = result {
            report.inconclusive = Some(query_inconclusive(e.in_phase("SAT emptiness", None))?);
        }
        // The All policy appends during checking, as on the BDD path.
        if options.examples.limit() == usize::MAX {
            let mut keyed = report
                .examples
                .drain(..)
                .map(|e| {
                    Ok((
                        AtomKey::from_atom(keys, &e.tuple).map_err(CheckError::Keys)?,
                        e,
                    ))
                })
                .collect::<Result<Vec<_>>>()?;
            keyed.sort_by(|a, b| a.0.cmp(&b.0));
            report.examples = keyed.into_iter().map(|(_, e)| e).collect();
        }
        Ok((report, models))
    }
}
impl Model {
    pub(super) fn observation(&self, b: &mut Budget<'_>) -> Result<Observation> {
        b.charge(self.program.inputs.len(), "SAT observation")?;
        Ok(self.observation_precharged())
    }
    fn observation_precharged(&self) -> Observation {
        let mut out = Observation {
            present: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for a in &self.program.inputs {
            // These atoms are already validated; avoid rechecking each domain.
            let i = self.program.core.atom_index[a];
            if self.values[i / 64] & (1u64 << (i % 64)) != 0 {
                out.present.insert(a.clone());
            } else {
                out.absent.insert(a.clone());
            }
        }
        out
    }
}
