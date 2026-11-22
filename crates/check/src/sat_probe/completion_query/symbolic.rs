//! Symbolic searches share inputs between equation copies. Only candidate searches
//! see excluded cubes; neither classification nor model-existence queries do.
use super::*;
use queries::{Run, checked_assignment};

pub mod planning;

type Cube = BTreeMap<usize, bool>;
#[cfg(test)]
mod cube_tests {
    use super::*;

    #[test]
    fn every_model_cube_preserves_equations_for_all_unpinned_inputs() {
        let mut corpus = denotate_ir::Corpus::new();
        let atoms: Vec<_> = (0..4)
            .map(|i| {
                let r = corpus
                    .declare_relation(
                        format!("a{i}"),
                        if i < 2 {
                            denotate_ir::RelationRole::Input
                        } else {
                            denotate_ir::RelationRole::Derived
                        },
                        [],
                    )
                    .unwrap();
                GroundAtom::new(r, [])
            })
            .collect();
        let limits = Limits::default();
        for left in 0..8 {
            for right in 0..8 {
                let cone = Cone {
                    atoms: atoms.clone(),
                    rules: vec![
                        super::super::super::Rule {
                            head: 2,
                            body: vec![(left / 2, left % 2 == 0)],
                        },
                        super::super::super::Rule {
                            head: 3,
                            body: vec![(right / 2, right % 2 == 0)],
                        },
                        super::super::super::Rule {
                            head: 2,
                            body: vec![(0, true), (1, false)],
                        },
                    ],
                    target: vec![true; 4],
                    duplicated: vec![false; 4],
                    fixed: vec![None; 4],
                    input: vec![true, true, false, false],
                    groups: vec![],
                    source_rules: 3,
                };
                let valid = |values: &[bool]| {
                    (2..4).all(|head| {
                        values[head]
                            == cone
                                .rules
                                .iter()
                                .filter(|r| r.head == head)
                                .any(|r| r.body.iter().all(|(i, pos)| values[*i] == *pos))
                    })
                };
                for bits in 0..16 {
                    let values: Vec<_> = (0..4).map(|i| bits & (1 << i) != 0).collect();
                    if !valid(&values) {
                        continue;
                    }
                    for h in [None, Some(0), Some(2)] {
                        if h.is_some_and(|i| !values[i]) {
                            continue;
                        }
                        let cube = cover(&cone, &values, h, &mut Budget::new(&limits)).unwrap();
                        for world in 0..4 {
                            let mut other = values.clone();
                            other[0] = world & 1 != 0;
                            other[1] = world & 2 != 0;
                            if cube.iter().all(|(i, v)| other[*i] == *v) {
                                assert!(valid(&other));
                                assert!(h.is_none_or(|i| other[i]));
                            }
                        }
                    }
                }
            }
        }
    }
}
struct Encoded {
    gate: Lit,
    encoding: Encoding,
}
struct Solver<'a, 'b, 'l> {
    run: Run<'a, 'b, 'l>,
    gates: Vec<Lit>,
    eligibility: Option<(Encoded, Encoded, Lit)>,
}
impl<'a, 'b, 'l> Solver<'a, 'b, 'l> {
    fn new(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        Ok(Self {
            run: Run::new(engine, budget)?,
            gates: vec![],
            eligibility: None,
        })
    }
    fn gate(&mut self) -> Result<Lit> {
        let gate = self.run.cnf.var(self.run.budget)?;
        self.gates.push(gate);
        Ok(gate)
    }
    fn encode(&mut self, cone: &Cone, h: bool) -> Result<Encoded> {
        let gate = self.gate()?;
        self.run.cnf.gate = Some(gate);
        let encoding = encoding::encode_named(
            cone,
            &mut self.run.cnf,
            self.run.truth,
            Some(&self.run.world.vars),
            self.run.budget,
            if h && self.run.engine.classification.is_some() {
                "model-under-hypothesis"
            } else {
                "model"
            },
        )?;
        if h {
            if let Some((_, _, i)) = &self.run.engine.classification {
                self.run
                    .cnf
                    .clause(vec![encoding.vars[*i]], self.run.budget)?;
            }
        }
        self.run.cnf.gate = None;
        Ok(Encoded { gate, encoding })
    }
    fn difference(
        &mut self,
        cone: &Cone,
        a: &Encoded,
        b: &Encoded,
        members: Option<&BTreeSet<GroundAtom>>,
    ) -> Result<Lit> {
        self.difference_selected(cone, a, b, members, true)
    }
    fn difference_selected(
        &mut self,
        cone: &Cone,
        a: &Encoded,
        b: &Encoded,
        members: Option<&BTreeSet<GroundAtom>>,
        declared_only: bool,
    ) -> Result<Lit> {
        let gate = self.gate()?;
        self.run.cnf.gate = Some(gate);
        let mut differences = Vec::new();
        for (i, atom) in cone.atoms.iter().enumerate() {
            self.run.budget.tick("completion pair")?;
            if cone.input[i]
                || (declared_only && !self.run.engine.decision(atom))
                || members.is_some_and(|m| !m.contains(atom))
            {
                continue;
            }
            let yes = self
                .run
                .cnf
                .and(&[a.encoding.vars[i], !b.encoding.vars[i]], self.run.budget)?;
            let no = self
                .run
                .cnf
                .and(&[!a.encoding.vars[i], b.encoding.vars[i]], self.run.budget)?;
            differences.extend([yes, no]);
        }
        self.run.cnf.clause(differences, self.run.budget)?;
        self.run.cnf.gate = None;
        Ok(gate)
    }
    fn solve(&mut self, active: &[Lit], pins: &[Lit]) -> Result<bool> {
        self.run
            .budget
            .charge(self.gates.len() + pins.len(), "completion query pins")?;
        let mut assumptions = pins.to_vec();
        assumptions.extend(
            self.gates
                .iter()
                .map(|g| if active.contains(g) { *g } else { !*g }),
        );
        self.run.solve(&assumptions)
    }
    fn values(&mut self, cone: &Cone, encoded: &Encoded) -> Result<Vec<bool>> {
        checked_assignment(cone, &encoded.encoding, &self.run.cnf, self.run.budget)
    }
    fn world(&mut self) -> Result<Observation> {
        let values = checked_assignment(
            &self.run.engine.world,
            &self.run.world,
            &self.run.cnf,
            self.run.budget,
        )?;
        Ok(self
            .run
            .engine
            .model(values, ModelScope::WholeProgram)
            .observation())
    }
    fn pins(&mut self, w: &Observation) -> Result<Vec<Lit>> {
        self.run
            .budget
            .charge(w.present.len() + w.absent.len(), "completion world pins")?;
        w.present
            .iter()
            .map(|a| (a, true))
            .chain(w.absent.iter().map(|a| (a, false)))
            .map(|(a, value)| self.run.input(a).map(|l| if value { l } else { !l }))
            .collect()
    }
    fn exclude(&mut self, selector: Lit, cube: &Cube) -> Result<()> {
        self.run
            .budget
            .charge(cube.len(), "completion cube exclusion")?;
        self.run.cnf.gate = Some(selector);
        let clause = cube
            .iter()
            .map(|(i, value)| {
                if *value {
                    !self.run.world.vars[*i]
                } else {
                    self.run.world.vars[*i]
                }
            })
            .collect();
        self.run.cnf.clause(clause, self.run.budget)?;
        self.run.cnf.gate = None;
        Ok(())
    }
    /// A pair witnesses ambiguity on every W-world in the intersection of its
    /// model cubes. Neither downstream equations nor candidate exclusions apply.
    fn eligible(&mut self, w: &Observation, globally_unique: bool) -> Result<Option<Cube>> {
        if self.run.engine.classification.is_none() || globally_unique {
            return Ok(None);
        }
        if self.eligibility.is_none() {
            let (cone, members, _) = self.run.engine.classification.as_ref().unwrap();
            let a = self.encode(cone, true)?;
            let b = self.encode(cone, true)?;
            let diff = self.difference(cone, &a, &b, Some(members))?;
            self.eligibility = Some((a, b, diff));
        }
        let pins = self.pins(w)?;
        let (a, b, diff) = self.eligibility.as_ref().unwrap();
        let active = [a.gate, b.gate, *diff];
        if !self.solve(&active, &pins)? {
            return Ok(None);
        }
        let (a, b, _) = self.eligibility.as_ref().unwrap();
        let (cone, _, h) = self.run.engine.classification.as_ref().unwrap();
        let av = checked_assignment(cone, &a.encoding, &self.run.cnf, self.run.budget)?;
        let bv = checked_assignment(cone, &b.encoding, &self.run.cnf, self.run.budget)?;
        let mut cube = cover(cone, &av, Some(*h), self.run.budget)?;
        cube.extend(cover(cone, &bv, Some(*h), self.run.budget)?);
        Ok(Some(cube))
    }
}

/// Keep the truth of derived atoms under every variation of unpinned inputs.
/// A true head needs one true producer; a false head needs one blocker for each
/// producer. Derived literals keep their model values, including circular support:
/// completion requires equations, not a finite derivation. W is enforced separately.
pub(super) fn cover(
    c: &Cone,
    values: &[bool],
    h: Option<usize>,
    b: &mut Budget<'_>,
) -> Result<Cube> {
    b.charge(c.fixed.len(), "completion model cube")?;
    let mut supported = vec![false; c.fixed.len()];
    let mut cube = Cube::new();
    let free = |i: usize| c.input[i] && c.fixed[i].is_none();
    if let Some(i) = h.filter(|i| free(*i)) {
        cube.insert(i, values[i]);
    }
    for r in &c.rules {
        b.charge(r.body.len() + 1, "completion model cube")?;
        if c.input[r.head] || c.fixed[r.head].is_some() {
            continue;
        }
        if values[r.head] {
            if !supported[r.head] && r.body.iter().all(|(i, pos)| values[*i] == *pos) {
                supported[r.head] = true;
                for (i, _) in &r.body {
                    if free(*i) {
                        cube.insert(*i, values[*i]);
                    }
                }
            }
        } else {
            let (i, _) = r
                .body
                .iter()
                .filter(|(i, pos)| values[*i] != *pos)
                .min_by_key(|(i, _)| (free(*i) && !cube.contains_key(i), *i))
                .ok_or(CheckError::Internal("invalid completion cube blocker"))?;
            if free(*i) {
                cube.insert(*i, values[*i]);
            }
        }
    }
    for i in 0..c.fixed.len() {
        b.tick("completion model cube")?;
        if !c.input[i] && c.fixed[i].is_none() && values[i] && !supported[i] {
            return Err(CheckError::Internal("invalid completion cube support"));
        }
    }
    Ok(cube)
}

impl Engine {
    fn symbolic_search_in<T>(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        phase: &'static str,
        f: impl FnOnce(&mut Solver<'_, '_, '_>) -> Result<Option<T>>,
    ) -> Result<Search<T>> {
        let _progress = self.limits.progress.scope(phase, None, true);
        let mut budget = Budget::new(&self.limits);
        let answer = (|| {
            let mut solver = Solver::new(self, &mut budget)?;
            solver.run.label(phase);
            for (atom, value) in context {
                let literal = solver.run.input(atom)?;
                solver.run.cnf.clause(
                    vec![if *value { literal } else { !literal }],
                    solver.run.budget,
                )?;
            }
            f(&mut solver)
        })();
        match answer {
            Ok(Some(value)) => Ok(Search::Exists(value)),
            Ok(None) => Ok(Search::None),
            Err(error) => Ok(Search::Inconclusive(inconclusive(
                error.in_phase(phase, None),
            )?)),
        }
    }
    fn symbolic_pair(
        &self,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
    ) -> Result<Search<Pair>> {
        self.symbolic_pair_in(&BTreeMap::new(), classification, unique, options)
    }
    fn symbolic_pair_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
    ) -> Result<Search<Pair>> {
        let (cone, members, scope) = if classification {
            let (c, m, _) = self.classification.as_ref().unwrap();
            (c, Some(m.as_ref()), ModelScope::Classification)
        } else {
            (
                &self.cone,
                None,
                if self.hypothesis.is_some() {
                    ModelScope::Processing
                } else {
                    ModelScope::WholeProgram
                },
            )
        };
        self.symbolic_search_in(
            context,
            if classification {
                "completion classification ambiguity"
            } else {
                "completion processing ambiguity"
            },
            |s| {
                let a = s.encode(cone, true)?;
                let b = s.encode(cone, true)?;
                let diff = s.difference(cone, &a, &b, members)?;
                let selector = s.gate()?;
                let mut examined = 0;
                loop {
                    if !s.solve(&[a.gate, b.gate, diff, selector], &[])? {
                        return Ok(None);
                    }
                    s.run
                        .budget
                        .room(examined, options.max_worlds, "completion pair", "worlds")?;
                    examined += 1;
                    let world = s.world()?;
                    // Retain both original assignments before the eligibility query
                    // changes the solver's current model.
                    let first = self.model(s.values(cone, &a)?, scope);
                    let second = self.model(s.values(cone, &b)?, scope);
                    if !classification {
                        if let Some(cube) = s.eligible(&world, unique)? {
                            s.exclude(selector, &cube)?;
                            continue;
                        }
                    }
                    return Ok(Some(Pair { first, second }));
                }
            },
        )
    }
    fn symbolic_accepted(&self, unique: bool, options: &CheckOptions) -> Result<Search<Model>> {
        self.symbolic_accepted_in(&BTreeMap::new(), unique, options)
    }
    fn symbolic_accepted_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        unique: bool,
        options: &CheckOptions,
    ) -> Result<Search<Model>> {
        let (cone, _, _) = self.classification.as_ref().unwrap();
        self.symbolic_search_in(context, "completion accepted observations", |s| {
            let encoded = s.encode(cone, true)?;
            let selector = s.gate()?;
            let mut examined = 0;
            loop {
                if !s.solve(&[encoded.gate, selector], &[])? {
                    return Ok(None);
                }
                s.run.budget.room(
                    examined,
                    options.max_worlds,
                    "completion accepted observations",
                    "worlds",
                )?;
                examined += 1;
                let world = s.world()?;
                let model = self.model(s.values(cone, &encoded)?, ModelScope::Classification);
                if let Some(cube) = s.eligible(&world, unique)? {
                    s.exclude(selector, &cube)?;
                    continue;
                }
                return Ok(Some(model));
            }
        })
    }
    fn symbolic_rejected(&self, options: &CheckOptions) -> Result<Search<Model>> {
        self.symbolic_rejected_in(&BTreeMap::new(), options)
    }
    fn symbolic_rejected_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        options: &CheckOptions,
    ) -> Result<Search<Model>> {
        let (cone, _, h) = self.classification.as_ref().unwrap();
        self.symbolic_search_in(context, "completion rejection", |s| {
            let base = s.encode(cone, false)?;
            let selector = s.gate()?;
            let mut examined = 0;
            loop {
                if !s.solve(&[base.gate, selector], &[!base.encoding.vars[*h]])? {
                    return Ok(None);
                }
                s.run.budget.room(
                    examined,
                    options.max_worlds,
                    "completion rejection",
                    "worlds",
                )?;
                examined += 1;
                let world = s.world()?;
                let model = self.model(
                    s.values(cone, &base)?,
                    ModelScope::ClassificationWithoutHypothesis,
                );
                let mut pins = s.pins(&world)?;
                pins.push(base.encoding.vars[*h]);
                if !s.solve(&[base.gate], &pins)? {
                    return Ok(Some(model));
                }
                let values = s.values(cone, &base)?;
                let cube = cover(cone, &values, Some(*h), s.run.budget)?;
                s.exclude(selector, &cube)?;
            }
        })
    }
    fn symbolic_no_meaning(
        &self,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
    ) -> Result<Search<Observation>> {
        self.symbolic_no_meaning_in(&BTreeMap::new(), classification, unique, options)
    }
    fn symbolic_no_meaning_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
    ) -> Result<Search<Observation>> {
        let cone = if classification {
            &self.classification.as_ref().unwrap().0
        } else {
            &self.cone
        };
        self.symbolic_no_meaning_cone(context, classification, unique, options, cone)
    }
    fn symbolic_no_meaning_cone(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
        cone: &Cone,
    ) -> Result<Search<Observation>> {
        let phase = if classification {
            "completion classification existence"
        } else {
            "completion processing existence"
        };
        self.symbolic_search_in(context, phase, |s| {
            // Every positive SCC has a least fixpoint for each assignment of its
            // providers. Classification is upstream-closed, so this also proves
            // an extension for each accepted classification when no negative SCC
            // exists in the complete program. This does not prove determinacy.
            let mut negative = false;
            for c in self.program.components() {
                s.run.budget.tick(phase)?;
                if c.cycle.is_some()
                    && (!classification
                        || c.atoms
                            .iter()
                            .any(|a| self.classification.as_ref().unwrap().1.contains(a)))
                {
                    negative = true;
                    break;
                }
            }
            if !negative {
                return Ok(None);
            }
            let candidate = if !classification {
                self.classification
                    .as_ref()
                    .map(|(c, _, _)| s.encode(c, true))
                    .transpose()?
            } else {
                None
            };
            let target = s.encode(cone, !classification)?;
            let selector = s.gate()?;
            let mut active = vec![selector];
            if let Some(candidate) = &candidate {
                active.push(candidate.gate);
            }
            let mut examined = 0;
            loop {
                if !s.solve(&active, &[])? {
                    return Ok(None);
                }
                s.run
                    .budget
                    .room(examined, options.max_worlds, phase, "worlds")?;
                examined += 1;
                let world = s.world()?;
                if !classification {
                    if let Some(cube) = s.eligible(&world, unique)? {
                        s.exclude(selector, &cube)?;
                        continue;
                    }
                }
                let pins = s.pins(&world)?;
                if !s.solve(&[target.gate], &pins)? {
                    return Ok(Some(world));
                }
                let values = s.values(cone, &target)?;
                let h = (!classification)
                    .then(|| self.classification.as_ref().map(|(_, _, h)| *h))
                    .flatten();
                let cube = cover(cone, &values, h, s.run.budget)?;
                s.exclude(selector, &cube)?;
            }
        })
    }
    fn symbolic_advisory(
        &self,
        unique: bool,
        options: &CheckOptions,
        keys: &SemanticKeys,
    ) -> Result<Advisory> {
        let mut limits = options.advisory_limits.clone();
        limits.cancellation = self.limits.cancellation.clone();
        let mut budget = Budget::new(&limits);
        let mut models = Vec::new();
        let sampled: Result<()> = (|| {
            let Some((cone, _, _)) = &self.classification else {
                return Ok(());
            };
            let mut s = Solver::new(self, &mut budget)?;
            let encoded = s.encode(cone, true)?;
            let selector = s.gate()?;
            let mut examined = 0;
            while s.solve(&[encoded.gate, selector], &[])? {
                s.run.budget.room(
                    examined,
                    options.max_worlds,
                    "completion advisory sampling",
                    "worlds",
                )?;
                examined += 1;
                let world = s.world()?;
                let values = s.values(cone, &encoded)?;
                if let Some(cube) = s.eligible(&world, unique)? {
                    s.exclude(selector, &cube)?;
                    continue;
                }
                s.run.budget.room(
                    models.len(),
                    options.max_examples,
                    "completion advisory sampling",
                    "examples",
                )?;
                // Optional sampling keeps one representative per observation, as
                // before. It never consumes required checking's allowance.
                let cube = cone
                    .input
                    .iter()
                    .enumerate()
                    .filter_map(|(i, input)| input.then_some((i, values[i])))
                    .collect();
                models.push(self.model(values, ModelScope::Classification));
                s.exclude(selector, &cube)?;
            }
            Ok(())
        })();
        let cause = match sampled {
            Ok(()) => None,
            Err(e) => Some(inconclusive(
                e.in_phase("completion advisory sampling", None),
            )?),
        };
        let mut result =
            self.circular_advisory_using(&models, false, options, keys, &mut budget)?;
        if let Advisory::Checked { incomplete, .. } = &mut result {
            if incomplete.is_none() {
                *incomplete = cause;
            }
        }
        Ok(result)
    }

    fn symbolic_property(
        &self,
        cone: &Cone,
        members: Arc<BTreeSet<GroundAtom>>,
        part: &PropertyPart,
        unique: bool,
        options: &CheckOptions,
        budget: &mut Budget<'_>,
    ) -> Result<Option<Model>> {
        let mut s = Solver::new(self, budget)?;
        s.run.label("completion property");
        let encoded = s.encode(cone, true)?;
        s.run.cnf.gate = Some(encoded.gate);
        let lits: Vec<_> = part
            .tuples
            .iter()
            .map(|a| encoded.encoding.vars[self.program.atom_index[a]])
            .collect();
        s.run
            .budget
            .charge(lits.len(), "completion property tuples")?;
        let pins = match part.component {
            Cardinality::Empty => lits,
            Cardinality::AtLeastOne => lits.into_iter().map(|l| !l).collect(),
            Cardinality::AtMostOne => {
                let mut seen = !s.run.truth;
                let mut many = !s.run.truth;
                for l in lits {
                    let both = s.run.cnf.and(&[seen, l], s.run.budget)?;
                    many = s.run.cnf.or(&[many, both], s.run.budget)?;
                    seen = s.run.cnf.or(&[seen, l], s.run.budget)?;
                }
                vec![many]
            }
            Cardinality::ExactlyOne => unreachable!(),
        };
        s.run.cnf.gate = None;
        let selector = s.gate()?;
        let mut examined = 0;
        loop {
            if !s.solve(&[encoded.gate, selector], &pins)? {
                return Ok(None);
            }
            s.run.budget.room(
                examined,
                options.max_worlds,
                "completion property",
                "worlds",
            )?;
            examined += 1;
            let world = s.world()?;
            let mut model = self.model(s.values(cone, &encoded)?, ModelScope::Property);
            model.members = Some(members.clone());
            if let Some(cube) = s.eligible(&world, unique)? {
                s.exclude(selector, &cube)?;
                continue;
            }
            return Ok(Some(model));
        }
    }
}

impl Engine {
    /// Verification-wide questions are independent symbolic searches. In
    /// particular, a processing contradiction never filters the input universe
    /// or the original classification query.
    pub fn check(&self, keys: &SemanticKeys, options: &CheckOptions) -> Result<Report> {
        if options.meaning != MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "completion supports full meaning analysis only",
            ));
        }
        let mut report = Report {
            verification: self.verification,
            hypothesis: self.hypothesis,
            decisions: self.decisions.clone(),
            context: Context::Permitted,
            classification: self.hypothesis.map(|_| Classification {
                accepted: Search::NotAnalysed,
                rejected: Search::NotAnalysed,
                no_meaning: Search::NotAnalysed,
                ambiguous: Search::NotAnalysed,
            }),
            meaning: Meaning {
                no_meaning: Search::NotAnalysed,
                ambiguous: Search::NotAnalysed,
                applicable: self.hypothesis.is_none(),
            },
            obligations: self.properties(keys, options)?,
            notices_not_analysed: self.notices.clone(),
            incomplete: vec![],
            advisory: Advisory::NotRequested,
            dead_producers: DeadProducerAdvisory::NotRequested,
            assumptions: self.assumption_analysis(options)?,
            ignored_input_domains: self.ignored_input_domains.clone(),
            program: self.program.clone(),
        };
        let contract_incomplete = report.assumptions.iter().any(|a| !a.certified());
        for a in &report.assumptions {
            if let Search::Inconclusive(c) = a.ambiguous {
                report.incomplete.push(c);
            }
            if let Search::Inconclusive(c) = a.no_meaning {
                report.incomplete.push(c);
            }
        }
        match self.worlds_using(&WorldQuery::default(), &mut Budget::new(&self.limits))? {
            WorldAnswer::NoWorld if !contract_incomplete => {
                report.context = Context::InconsistentAssumptions
            }
            WorldAnswer::NoWorld => (),
            WorldAnswer::Inconclusive(c) => {
                report.context = Context::Inconclusive(c);
                report.incomplete.push(c);
            }
            WorldAnswer::World(_) => (),
        }
        if report.context != Context::Permitted {
            for (id, req) in &self.selection {
                if matches!(req, denotate_ir::Requirement::NoRejections { .. }) {
                    report.obligations.insert(
                        *id,
                        ObligationResult::rejection(req.clone(), &Search::NotAnalysed, None),
                    );
                }
            }
            if options.circular_support {
                report.advisory = self.symbolic_advisory(false, options, keys)?;
            }
            report.dead_producers = self.dead_producer_advisory(options)?;
            return Ok(report);
        }
        let mut globally_unique = true;
        if let Some(c) = &mut report.classification {
            c.ambiguous = self.symbolic_pair(true, true, options)?;
            globally_unique = matches!(c.ambiguous, Search::None);
            c.accepted = self.symbolic_accepted(globally_unique, options)?;
            c.rejected = self.symbolic_rejected(options)?;
            c.no_meaning = self.symbolic_no_meaning(true, true, options)?;
            for state in [
                &c.accepted as &dyn Unknown,
                &c.rejected,
                &c.no_meaning,
                &c.ambiguous,
            ] {
                if let Some(cause) = state.unknown() {
                    report.incomplete.push(cause);
                }
            }
        }
        let vacuous = !contract_incomplete
            && report
                .classification
                .as_ref()
                .is_some_and(|c| matches!(c.accepted, Search::None));
        let eligibility_unknown = report
            .classification
            .as_ref()
            .and_then(|c| Unknown::unknown(&c.accepted));
        report.meaning.applicable = !vacuous;
        if vacuous {
            report.meaning.no_meaning = Search::None;
            report.meaning.ambiguous = Search::None;
        } else {
            report.meaning.no_meaning =
                self.symbolic_no_meaning(false, globally_unique, options)?;
            report.meaning.ambiguous = self.symbolic_pair(false, globally_unique, options)?;
            for state in [
                &report.meaning.no_meaning as &dyn Unknown,
                &report.meaning.ambiguous,
            ] {
                if let Some(cause) = state.unknown() {
                    report.incomplete.push(cause);
                }
            }
        }
        for property in report.obligations.values_mut() {
            let mut budget = Budget::new(&self.limits);
            if !vacuous {
                if let Some(members) = property.members.clone() {
                    let mut cone = self.cone.clone();
                    cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
                    let mut retained = 0;
                    for part in &mut property.parts {
                        match self.symbolic_property(
                            &cone,
                            members.clone(),
                            part,
                            globally_unique,
                            options,
                            &mut budget,
                        ) {
                            Ok(Some(model)) => {
                                part.failed = true;
                                if retained < options.max_examples {
                                    part.example = Some(model);
                                    retained += 1;
                                }
                            }
                            Ok(None) => (),
                            Err(e) => {
                                property.inconclusive =
                                    Some(inconclusive(e.in_phase("completion property", None))?);
                                break;
                            }
                        }
                    }
                }
            }
            property.finish(true, eligibility_unknown, vacuous);
        }
        for (id, req) in &self.selection {
            if matches!(req, denotate_ir::Requirement::NoRejections { .. }) {
                let rejected = &report.classification.as_ref().unwrap().rejected;
                report.obligations.insert(
                    *id,
                    ObligationResult::rejection(req.clone(), rejected, None),
                );
            }
        }
        if options.circular_support {
            report.advisory = self.symbolic_advisory(globally_unique, options, keys)?;
        }
        if contract_incomplete {
            report.mark_partial_contract();
        }
        report.incomplete.sort_by_key(|c| (c.phase, c.resource));
        report.incomplete.dedup();
        report.dead_producers = self.dead_producer_advisory(options)?;
        Ok(report)
    }
}
trait Unknown {
    fn unknown(&self) -> Option<Inconclusive>;
}
impl<T> Unknown for Search<T> {
    fn unknown(&self) -> Option<Inconclusive> {
        if let Self::Inconclusive(c) = self {
            Some(*c)
        } else {
            None
        }
    }
}
