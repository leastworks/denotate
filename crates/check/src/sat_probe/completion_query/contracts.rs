//! Definitions of input restrictions are queried independently over U.
use super::*;
use denotate_ir::{AssumptionId, Restriction};
use queries::{Run, checked_assignment};

#[derive(Debug, Clone)]
pub struct AssumptionAmbiguity {
    pub models: Pair,
    /// One group true in the first interpretation and false in the second.
    pub group: Vec<ConstantId>,
}
#[derive(Debug, Clone)]
pub struct AssumptionAnalysis {
    pub assumption: AssumptionId,
    pub ambiguous: Search<AssumptionAmbiguity>,
    pub no_meaning: Search<Observation>,
}
impl AssumptionAnalysis {
    pub fn failed(&self) -> bool {
        self.ambiguous.exists() || self.no_meaning.exists()
    }
    pub fn certified(&self) -> bool {
        matches!(self.ambiguous, Search::None) && matches!(self.no_meaning, Search::None)
    }
}
pub(super) struct Assumption {
    pub id: AssumptionId,
    pub kind: Cardinality,
    pub cone: Cone,
    pub members: Arc<BTreeSet<GroundAtom>>,
    pub groups: Vec<(Vec<ConstantId>, Vec<usize>)>,
    pub recursive: bool,
    pub negative: bool,
}
impl Assumption {
    pub fn formula(
        &self,
        e: &Encoding,
        cnf: &mut Cnf,
        truth: Lit,
        b: &mut Budget<'_>,
    ) -> Result<Lit> {
        let mut all = Vec::new();
        for (_, atoms) in &self.groups {
            let mut seen = !truth;
            let mut many = !truth;
            for i in atoms {
                b.tick("completion assumption formula")?;
                let l = e.vars[*i];
                let both = cnf.and(&[seen, l], b)?;
                many = cnf.or(&[many, both], b)?;
                seen = cnf.or(&[seen, l], b)?;
            }
            all.push(match self.kind {
                Cardinality::Empty => !seen,
                Cardinality::AtMostOne => !many,
                Cardinality::AtLeastOne => seen,
                Cardinality::ExactlyOne => cnf.and(&[seen, !many], b)?,
            });
        }
        cnf.and(&all, b)
    }
    fn group_value(&self, atoms: &[usize], values: &[bool]) -> bool {
        let n = atoms.iter().filter(|i| values[**i]).count();
        match self.kind {
            Cardinality::Empty => n == 0,
            Cardinality::AtMostOne => n <= 1,
            Cardinality::AtLeastOne => n >= 1,
            Cardinality::ExactlyOne => n == 1,
        }
    }
    pub fn value(&self, values: &[bool]) -> bool {
        self.groups
            .iter()
            .all(|(_, atoms)| self.group_value(atoms, values))
    }
}

pub(super) fn build(
    engine: &Engine,
    corpus: &Corpus,
    b: &mut Budget<'_>,
) -> Result<Vec<Assumption>> {
    let mut out = Vec::new();
    for id in &corpus
        .verification(engine.verification)
        .unwrap()
        .assumptions
    {
        let restriction = &corpus.assumption(*id).unwrap().restriction;
        let roots = engine
            .program
            .atoms()
            .filter(|a| a.relation == restriction.relation())
            .cloned();
        let live = engine.program.dependency_cone_with_budget(roots, b)?;
        let mut recursive = false;
        let mut negative = false;
        for c in engine.program.components() {
            b.tick("completion assumption components")?;
            if live.components.contains(&c.id) {
                recursive |= c.recursive;
                negative |= c.cycle.is_some();
            }
        }
        let members = Arc::new(live.facts);
        let mut cone = engine.cone.clone();
        cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
        let groups = groups(&engine.program, restriction, b)?;
        out.push(Assumption {
            id: *id,
            kind: restriction.kind(),
            cone,
            members,
            groups,
            recursive,
            negative,
        });
    }
    Ok(out)
}
fn groups(
    p: &GroundProgram,
    r: &Restriction,
    b: &mut Budget<'_>,
) -> Result<Vec<(Vec<ConstantId>, Vec<usize>)>> {
    let mut groups = BTreeMap::<Vec<ConstantId>, Vec<usize>>::new();
    if r.kind().has_coverage() {
        let signature = &p.signatures[&r.relation()];
        let columns: Vec<_> = r
            .group_by()
            .iter()
            .map(|i| &p.domains[&signature[*i]])
            .collect();
        if !columns.iter().any(|c| c.is_empty()) {
            let mut positions = vec![0; columns.len()];
            loop {
                b.tick("completion assumption groups")?;
                b.room(
                    groups.len(),
                    b.limits.max_atoms,
                    "completion assumption groups",
                    "groups",
                )?;
                groups.insert(
                    columns.iter().zip(&positions).map(|(c, i)| c[*i]).collect(),
                    vec![],
                );
                let mut advanced = false;
                for i in (0..positions.len()).rev() {
                    positions[i] += 1;
                    if positions[i] < columns[i].len() {
                        advanced = true;
                        break;
                    }
                    positions[i] = 0;
                }
                if !advanced {
                    break;
                }
            }
        }
    }
    for (i, a) in p.core.atoms.iter().enumerate() {
        b.tick("completion assumption tuples")?;
        if a.relation == r.relation() {
            let key: Vec<_> = r.group_by().iter().map(|i| a.arguments[*i]).collect();
            if !groups.contains_key(&key) {
                b.room(
                    groups.len(),
                    b.limits.max_atoms,
                    "completion assumption groups",
                    "groups",
                )?;
            }
            groups.entry(key).or_default().push(i);
        }
    }
    Ok(groups.into_iter().collect())
}

impl Engine {
    pub fn assumption_analysis(&self, options: &CheckOptions) -> Result<Vec<AssumptionAnalysis>> {
        self.assumptions
            .iter()
            .map(|a| {
                let ambiguous = if a.recursive {
                    self.contract_search("completion assumption determinacy", |run| {
                        let first = encode(
                            &a.cone,
                            &mut run.cnf,
                            run.truth,
                            Some(&run.world.vars),
                            run.budget,
                        )?;
                        let second = encode(
                            &a.cone,
                            &mut run.cnf,
                            run.truth,
                            Some(&run.world.vars),
                            run.budget,
                        )?;
                        let yes = a.formula(&first, &mut run.cnf, run.truth, run.budget)?;
                        let no = a.formula(&second, &mut run.cnf, run.truth, run.budget)?;
                        if !run.solve(&[yes, !no])? {
                            return Ok(None);
                        }
                        let av = checked_assignment(&a.cone, &first, &run.cnf, run.budget)?;
                        let bv = checked_assignment(&a.cone, &second, &run.cnf, run.budget)?;
                        let group = a
                            .groups
                            .iter()
                            .find(|(_, atoms)| {
                                a.group_value(atoms, &av) != a.group_value(atoms, &bv)
                            })
                            .unwrap()
                            .0
                            .clone();
                        Ok(Some(AssumptionAmbiguity {
                            models: Pair {
                                first: self.contract_model(av, a),
                                second: self.contract_model(bv, a),
                            },
                            group,
                        }))
                    })?
                } else {
                    Search::None
                };
                let no_meaning = if a.negative {
                    self.contract_search("completion assumption existence", |run| {
                        let gate = run.cnf.var(run.budget)?;
                        run.cnf.gate = Some(gate);
                        let e = encode(
                            &a.cone,
                            &mut run.cnf,
                            run.truth,
                            Some(&run.world.vars),
                            run.budget,
                        )?;
                        run.cnf.gate = None;
                        let selection = run.cnf.var(run.budget)?;
                        let mut examined = 0;
                        while run.solve(&[!gate, selection])? {
                            run.budget.room(
                                examined,
                                options.max_worlds,
                                "completion assumption existence",
                                "worlds",
                            )?;
                            examined += 1;
                            let world =
                                checked_assignment(&self.world, &run.world, &run.cnf, run.budget)?;
                            let pins = run.input_pins(&world);
                            let mut target = vec![gate, !selection];
                            target.extend(pins);
                            if !run.solve(&target)? {
                                return Ok(Some(
                                    self.model(world, ModelScope::WholeProgram).observation(),
                                ));
                            }
                            let values = checked_assignment(&a.cone, &e, &run.cnf, run.budget)?;
                            let cube = super::symbolic::cover(&a.cone, &values, None, run.budget)?;
                            run.cnf.gate = Some(selection);
                            run.exclude(&cube)?;
                            run.cnf.gate = None;
                        }
                        Ok(None)
                    })?
                } else {
                    Search::None
                };
                Ok(AssumptionAnalysis {
                    assumption: a.id,
                    ambiguous,
                    no_meaning,
                })
            })
            .collect()
    }
    fn contract_model(&self, values: Vec<bool>, a: &Assumption) -> Model {
        let mut m = self.model(values, ModelScope::Assumption);
        m.members = Some(a.members.clone());
        m
    }
    fn contract_search<T>(
        &self,
        phase: &'static str,
        f: impl FnOnce(&mut Run<'_, '_, '_>) -> Result<Option<T>>,
    ) -> Result<Search<T>> {
        let _progress = self.limits.progress.scope(phase, None, true);
        let mut budget = Budget::new(&self.limits);
        let result = (|| f(&mut Run::universe(self, &mut budget)?))();
        match result {
            Ok(Some(v)) => Ok(Search::Exists(v)),
            Ok(None) => Ok(Search::None),
            Err(e) => Ok(Search::Inconclusive(inconclusive(e.in_phase(phase, None))?)),
        }
    }
}

pub(super) fn uncertified() -> Inconclusive {
    Inconclusive {
        phase: "completion input contract",
        resource: "undetermined assumptions",
        details: Default::default(),
    }
}

impl Engine {
    pub(super) fn assumptions_at(
        &self,
        present: &BTreeSet<GroundAtom>,
        b: &mut Budget<'_>,
        solves: &mut usize,
    ) -> Result<Vec<AssumptionAnalysis>> {
        let mut out = Vec::new();
        for a in self.assumptions.iter().filter(|a| a.recursive) {
            let mut run = Run::universe(self, b)?;
            run.solve_limit = self.config.max_solves.saturating_sub(*solves);
            let result: Result<Option<AssumptionAnalysis>> = (|| {
                let mut pins = Vec::new();
                for atom in &self.program.inputs {
                    let l = run.input(atom)?;
                    pins.push(if present.contains(atom) { l } else { !l });
                }
                if !run.solve(&pins)? {
                    return Ok(None);
                }
                let e = encode(
                    &a.cone,
                    &mut run.cnf,
                    run.truth,
                    Some(&run.world.vars),
                    run.budget,
                )?;
                let formula = a.formula(&e, &mut run.cnf, run.truth, run.budget)?;
                if !run.solve(&pins)? {
                    return Ok(Some(AssumptionAnalysis {
                        assumption: a.id,
                        ambiguous: Search::None,
                        no_meaning: Search::Exists(Observation {
                            present: present.clone(),
                            absent: self.program.inputs.difference(present).cloned().collect(),
                        }),
                    }));
                }
                let first = checked_assignment(&a.cone, &e, &run.cnf, run.budget)?;
                let value = a.value(&first);
                pins.push(if value { !formula } else { formula });
                if run.solve(&pins)? {
                    let second = checked_assignment(&a.cone, &e, &run.cnf, run.budget)?;
                    let (first, second) = if value {
                        (first, second)
                    } else {
                        (second, first)
                    };
                    let group = a
                        .groups
                        .iter()
                        .find(|(_, atoms)| {
                            a.group_value(atoms, &first) != a.group_value(atoms, &second)
                        })
                        .unwrap()
                        .0
                        .clone();
                    return Ok(Some(AssumptionAnalysis {
                        assumption: a.id,
                        no_meaning: Search::None,
                        ambiguous: Search::Exists(AssumptionAmbiguity {
                            group,
                            models: Pair {
                                first: self.contract_model(first, a),
                                second: self.contract_model(second, a),
                            },
                        }),
                    }));
                }
                Ok(None)
            })();
            *solves += run.solves;
            if let Some(issue) = result? {
                out.push(issue);
            }
        }
        Ok(out)
    }
}
