//! Symbolic searches share inputs between equation copies. Only candidate searches
//! see excluded cubes; neither classification nor model-existence queries do.
use super::*;
use queries::{Run, checked_assignment};

pub(super) mod branches;
mod consistency;
mod determinacy;
mod existence;
mod existence_slice;
mod odd;
pub mod planning;
pub(super) mod targets;
mod validation;

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
                    atoms: atoms.clone().into(),
                    rules: vec![
                        super::super::super::Rule {
                            ground: None,
                            source: None,
                            head: 2,
                            body: vec![(left / 2, left % 2 == 0)],
                        },
                        super::super::super::Rule {
                            ground: None,
                            source: None,
                            head: 3,
                            body: vec![(right / 2, right % 2 == 0)],
                        },
                        super::super::super::Rule {
                            ground: None,
                            source: None,
                            head: 2,
                            body: vec![(0, true), (1, false)],
                        },
                    ]
                    .into(),
                    target: vec![true; 4].into(),
                    duplicated: vec![false; 4].into(),
                    fixed: vec![None; 4],
                    input: vec![true, true, false, false].into(),
                    groups: vec![].into(),
                    source_rules: 3,
                    retained: vec![].into(),
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
    eligibility_index: Option<validation::Index>,
    eligibility_states: [validation::State; 2],
    property_index: Option<validation::Index>,
    property_state: validation::State,
    stats: crate::CompletionExistenceStats,
}
impl<'a, 'b, 'l> Solver<'a, 'b, 'l> {
    fn new(engine: &'a Engine, budget: &'b mut Budget<'l>) -> Result<Self> {
        Ok(Self {
            run: Run::new(engine, budget)?,
            gates: vec![],
            eligibility: None,
            eligibility_index: None,
            eligibility_states: Default::default(),
            property_index: None,
            property_state: Default::default(),
            stats: Default::default(),
        })
    }
    fn metrics(&mut self) {
        if let Some((_, stats)) = &mut self.run.cnf.measurement {
            stats.existence = self.stats.clone();
        }
        self.run
            .engine
            .limits
            .progress
            .completion_existence(&self.stats);
    }
    fn cube_metrics(&mut self, cube: &Cube) {
        self.stats.cubes += 1;
        self.stats.pins += cube.len();
        self.stats.max_pins = self.stats.max_pins.max(cube.len());
        self.metrics();
    }
    fn gate(&mut self) -> Result<Lit> {
        let gate = self.run.cnf.var(self.run.budget)?;
        self.gates.push(gate);
        Ok(gate)
    }
    fn simplified(&mut self, cone: &Cone, h: bool) -> Result<pruning::View> {
        pruning::view_using(
            self.run.engine,
            cone,
            h,
            self.run.budget.remaining_time(),
            self.run.budget,
        )
    }
    fn encode(&mut self, original: &Cone, h: bool) -> Result<Encoded> {
        let view = self.simplified(original, h)?;
        self.encode_view(&view, original, h)
    }
    fn encode_view(&mut self, cone: &Cone, original: &Cone, h: bool) -> Result<Encoded> {
        let gate = self.gate()?;
        self.run.cnf.gate = Some(gate);
        let mut encoding = encoding::encode_named(
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
        original_validation(original, &mut encoding, self.run.budget)?;
        Ok(Encoded { gate, encoding })
    }
    fn encode_shared(
        &mut self,
        cone: &Cone,
        h: bool,
        first: &Encoded,
        shared: &[bool],
    ) -> Result<Encoded> {
        let gate = self.gate()?;
        self.run.cnf.gate = Some(gate);
        let mut encoding = encoding::encode_shared(
            cone,
            &mut self.run.cnf,
            self.run.truth,
            Some(&self.run.world.vars),
            self.run.budget,
            "shared-pair",
            Some((&first.encoding.vars, shared)),
        )?;
        if h {
            if let Some((_, _, i)) = &self.run.engine.classification {
                self.run
                    .cnf
                    .clause(vec![encoding.vars[*i]], self.run.budget)?;
            }
        }
        self.run.cnf.gate = None;
        if let (Some(to), Some(from)) = (&mut encoding.validation, &first.encoding.validation) {
            self.run
                .budget
                .charge(from.heads.len(), "completion original validation index")?;
            to.heads.clone_from(&from.heads);
        }
        Ok(Encoded { gate, encoding })
    }
    /// Both questions are active together: selected outputs differ, and this
    /// component differs. Define each atom comparison once under their common
    /// gate, even when the atom belongs to both sets.
    fn component_difference(
        &mut self,
        cone: &Cone,
        a: &Encoded,
        b: &Encoded,
        members: Option<&BTreeSet<GroundAtom>>,
        heads: &[usize],
    ) -> Result<Lit> {
        let gate = self.gate()?;
        self.run.cnf.gate = Some(gate);
        self.run
            .budget
            .charge(cone.fixed.len(), "completion pair")?;
        let mut root = vec![false; cone.fixed.len()];
        for i in heads {
            root[*i] = true;
        }
        let mut selected = Vec::new();
        let mut component = Vec::new();
        for (i, is_root) in root.into_iter().enumerate() {
            self.run.budget.tick("completion pair")?;
            if cone.input[i] || a.encoding.vars[i] == b.encoding.vars[i] {
                continue;
            }
            let decision = cone
                .atoms
                .get(i)
                .is_some_and(|atom| self.run.engine.compared(atom, members));
            if !decision && !is_root {
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
            if decision {
                selected.extend([yes, no]);
            }
            if is_root {
                component.extend([yes, no]);
            }
        }
        self.run.cnf.clause(selected, self.run.budget)?;
        self.run.cnf.clause(component, self.run.budget)?;
        self.run.cnf.gate = None;
        Ok(gate)
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
                || a.encoding.vars[i] == b.encoding.vars[i]
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
        let started = self.run.budget.used();
        let result = checked_assignment(cone, &encoded.encoding, &self.run.cnf, self.run.budget);
        self.stats.validation_work += self.run.budget.used() - started;
        self.metrics();
        result
    }
    fn existence_values(
        &mut self,
        slice: &existence_slice::Slice,
        original: &Cone,
        encoded: &Encoded,
    ) -> Result<Vec<bool>> {
        self.slice_values(slice, original, encoded)
            .map(|(core, _)| core)
    }
    /// Pair witnesses report full interpretations: the reconstructed remainder,
    /// replayed against the original equations like every other model.
    fn full_values(
        &mut self,
        slice: &existence_slice::Slice,
        original: &Cone,
        encoded: &Encoded,
    ) -> Result<Vec<bool>> {
        self.slice_values(slice, original, encoded)
            .map(|(_, full)| full)
    }
    fn slice_values(
        &mut self,
        slice: &existence_slice::Slice,
        original: &Cone,
        encoded: &Encoded,
    ) -> Result<(Vec<bool>, Vec<bool>)> {
        let started = self.run.budget.used();
        let result = (|| {
            let core = checked_assignment(
                &slice.core,
                &encoded.encoding,
                &self.run.cnf,
                self.run.budget,
            )?;
            self.run
                .budget
                .charge(core.len(), "completion existence extension")?;
            let mut full = core.clone();
            slice.extend(&mut full, self.run.budget)?;
            queries::validate_assignment(
                original,
                &full,
                encoded.encoding.validation.as_ref(),
                self.run.budget,
            )?;
            Ok((core, full))
        })();
        self.stats.validation_work += self.run.budget.used() - started;
        self.metrics();
        result
    }
    fn property_values(&mut self, cone: &Cone, encoded: &Encoded) -> Result<Vec<bool>> {
        if self.property_index.is_none() {
            self.property_index = Some(validation::Index::new(
                cone,
                encoded,
                self.run.truth,
                self.run.budget,
            )?);
        }
        let started = self.run.budget.used();
        let result = self
            .property_state
            .update(
                cone,
                encoded,
                self.property_index.as_ref().unwrap(),
                &self.run.cnf,
                self.run.budget,
            )
            .map(|v| v.to_vec());
        self.stats.validation_work += self.run.budget.used() - started;
        self.metrics();
        result
    }
    fn world(&mut self) -> Result<Observation> {
        let started = self.run.budget.used();
        let checked = checked_assignment(
            &self.run.engine.world,
            &self.run.world,
            &self.run.cnf,
            self.run.budget,
        );
        self.stats.validation_work += self.run.budget.used() - started;
        self.metrics();
        let values = checked?;
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
        self.cube_metrics(cube);
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
        let (a, b, diff) = self.eligibility.take().unwrap();
        let (cone, _, h) = self.run.engine.classification.as_ref().unwrap();
        if self.eligibility_index.is_none() {
            self.eligibility_index = Some(validation::Index::new(
                cone,
                &a,
                self.run.truth,
                self.run.budget,
            )?);
        }
        let started = self.run.budget.used();
        let av = self.eligibility_states[0]
            .update(
                cone,
                &a,
                self.eligibility_index.as_ref().unwrap(),
                &self.run.cnf,
                self.run.budget,
            )?
            .to_vec();
        let bv = self.eligibility_states[1]
            .update(
                cone,
                &b,
                self.eligibility_index.as_ref().unwrap(),
                &self.run.cnf,
                self.run.budget,
            )?
            .to_vec();
        self.stats.validation_work += self.run.budget.used() - started;
        let mut left = cover(cone, &av, Some(*h), self.run.budget)?;
        existence::lift(cone, &av, &a, &mut left, self)?;
        let mut right = cover(cone, &bv, Some(*h), self.run.budget)?;
        existence::lift(cone, &bv, &b, &mut right, self)?;
        // H can itself be an input. Lifting equations alone cannot remove it.
        if cone.input[*h] && cone.fixed[*h].is_none() {
            left.insert(*h, true);
        }
        left.extend(right);
        let cube = left;
        self.eligibility = Some((a, b, diff));
        Ok(Some(cube))
    }
}

fn original_validation(original: &Cone, encoding: &mut Encoding, b: &mut Budget<'_>) -> Result<()> {
    b.charge(
        original.rules.len() + original.fixed.len(),
        "completion original validation index",
    )?;
    if let Some(index) = &mut encoding.validation {
        let mut heads: BTreeSet<_> = original.rules.iter().map(|r| r.head).collect();
        heads.extend(
            original
                .fixed
                .iter()
                .enumerate()
                .filter_map(|(i, v)| v.is_some().then_some(i)),
        );
        index.heads = heads.into_iter().collect();
    }
    Ok(())
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
    for eq in &c.retained {
        b.charge(
            eq.bodies.iter().map(|body| body.len() + 1).sum(),
            "completion retained cube",
        )?;
        if values[eq.head] {
            let body = eq
                .bodies
                .iter()
                .find(|body| body.iter().all(|(i, p)| values[*i] == *p))
                .ok_or(CheckError::Internal("invalid forced true cube"))?;
            for (i, _) in body {
                if free(*i) {
                    cube.insert(*i, values[*i]);
                }
            }
        } else {
            for body in &eq.bodies {
                let (i, _) = body
                    .iter()
                    .filter(|(i, p)| values[*i] != *p)
                    .min_by_key(|(i, _)| (free(*i) && !cube.contains_key(i), *i))
                    .ok_or(CheckError::Internal("invalid forced false cube"))?;
                if free(*i) {
                    cube.insert(*i, values[*i]);
                }
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
    pub(super) fn shared_limits(&self, shares: usize) -> Limits {
        let mut limits = self.limits.clone();
        if let Some(deadline) = limits.run_deadline {
            limits.timeout = limits.timeout.min(
                deadline.saturating_duration_since(Instant::now())
                    / self.limits.completion_share(shares).min(u32::MAX as usize) as u32,
            );
        }
        limits
    }
    fn symbolic_search_in<T>(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        phase: &'static str,
        shares: usize,
        f: impl FnOnce(&mut Solver<'_, '_, '_>) -> Result<Option<T>>,
    ) -> Result<Search<T>> {
        let _progress = self.limits.progress.scope(phase, None, true);
        let limits = self.shared_limits(shares);
        let mut budget = Budget::new(&limits);
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
        if let Some(work) = &self.exploration_work {
            let _ = work.fetch_update(
                std::sync::atomic::Ordering::Relaxed,
                std::sync::atomic::Ordering::Relaxed,
                |n| Some(n.saturating_add(budget.used())),
            );
        }
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
        shares: usize,
    ) -> Result<Search<Pair>> {
        if options.split_depth == 0 {
            return self.symbolic_pair_in(
                &BTreeMap::new(),
                classification,
                unique,
                options,
                shares,
            );
        }
        branches::run(self, classification, false, options, shares, |e, opts| {
            e.symbolic_pair_in(&BTreeMap::new(), classification, unique, opts, 1)
        })
    }
    fn symbolic_pair_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
        shares: usize,
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
            shares,
            |s| {
                let view = s.simplified(cone, true)?;
                determinacy::search(
                    self,
                    &view,
                    view.label(),
                    cone,
                    members,
                    scope,
                    classification,
                    unique,
                    options,
                    s,
                )
            },
        )
    }
    fn symbolic_accepted(
        &self,
        unique: bool,
        options: &CheckOptions,
        shares: usize,
    ) -> Result<Search<Model>> {
        if !self.limits.completion_exploration || options.split_depth == 0 {
            return self.symbolic_accepted_in(&BTreeMap::new(), unique, options, shares);
        }
        let mut question = self.clone();
        question.branch_phase = Some("completion accepted observations");
        branches::run(&question, true, false, options, shares, |e, opts| {
            e.symbolic_accepted_in(&BTreeMap::new(), unique, opts, 1)
        })
    }
    fn symbolic_accepted_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        unique: bool,
        options: &CheckOptions,
        shares: usize,
    ) -> Result<Search<Model>> {
        let (cone, _, _) = self.classification.as_ref().unwrap();
        self.symbolic_search_in(context, "completion accepted observations", shares, |s| {
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
                s.stats.rounds += 1;
                s.metrics();
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
    fn symbolic_rejected(&self, options: &CheckOptions, shares: usize) -> Result<Search<Model>> {
        if !self.limits.completion_exploration || options.split_depth == 0 {
            return self.symbolic_rejected_in(&BTreeMap::new(), options, shares);
        }
        let mut question = self.clone();
        question.branch_phase = Some("completion rejection");
        // Like classification existence, rejection searches no-H models and
        // therefore permits only W-certified formula partitions.
        branches::run(&question, true, true, options, shares, |e, opts| {
            e.symbolic_rejected_in(&BTreeMap::new(), opts, 1)
        })
    }
    fn symbolic_rejected_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        options: &CheckOptions,
        shares: usize,
    ) -> Result<Search<Model>> {
        let (cone, _, h) = self.classification.as_ref().unwrap();
        self.symbolic_search_in(context, "completion rejection", shares, |s| {
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
                s.stats.rounds += 1;
                s.metrics();
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
        shares: usize,
    ) -> Result<Search<Observation>> {
        if options.split_depth == 0 {
            return self.symbolic_no_meaning_in(
                &BTreeMap::new(),
                classification,
                unique,
                options,
                shares,
            );
        }
        branches::run(self, classification, true, options, shares, |e, opts| {
            e.symbolic_no_meaning_in(&BTreeMap::new(), classification, unique, opts, 1)
        })
    }
    fn symbolic_no_meaning_in(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
        shares: usize,
    ) -> Result<Search<Observation>> {
        let cone = if classification {
            &self.classification.as_ref().unwrap().0
        } else {
            &self.cone
        };
        if classification && self.pruning.is_some() {
            return self.symbolic_classification_existence(context, options, shares, cone);
        }
        self.symbolic_no_meaning_cone(context, classification, unique, options, shares, cone)
    }
    /// An H-model already proves classification existence at that observation.
    /// Only an UNSAT H query permits falling back to equations without H.
    fn symbolic_classification_existence(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        options: &CheckOptions,
        shares: usize,
        original: &Cone,
    ) -> Result<Search<Observation>> {
        self.symbolic_search_in(
            context,
            "completion classification existence",
            shares,
            |s| {
                // An unconditional structural existence certificate needs no
                // model query, with or without H.
                let world_view = s.simplified(original, false)?;
                if world_view.retained.is_empty()
                    && consistency::analyse(&world_view, None, s.run.budget)?.odd_components == 0
                {
                    return Ok(None);
                }
                existence::classification_shape(self, &world_view, world_view.label(), s)?;
                let h = self.classification.as_ref().unwrap().2;
                let view = s.simplified(original, true)?;
                let slice = existence_slice::Slice::new(&view, Some(h), s.run.budget)?;
                let accepted = s.encode_view(&slice.core, original, true)?;
                let selector = s.gate()?;
                let mut base = None;
                loop {
                    if let Some(d) = &mut s.stats.current_component {
                        d.state = "covering-hypothesis-models";
                    }
                    s.metrics();
                    if !s.solve(&[selector], &[])? {
                        return Ok(None);
                    }
                    s.run.budget.room(
                        s.stats.rounds,
                        options.max_worlds,
                        "completion classification existence",
                        "worlds",
                    )?;
                    s.stats.rounds += 1;
                    s.metrics();
                    let world = s.world()?;
                    let pins = s.pins(&world)?;
                    if s.solve(&[accepted.gate], &pins)? {
                        let values = s.existence_values(&slice, original, &accepted)?;
                        let mut cube = cover(&slice.core, &values, Some(h), s.run.budget)?;
                        existence::lift(&slice.core, &values, &accepted, &mut cube, s)?;
                        // A lifted model must still assert H if H is an input.
                        if view.input[h] && view.fixed[h].is_none() {
                            cube.insert(h, true);
                        }
                        s.exclude(selector, &cube)?;
                        continue;
                    }
                    if let Some(d) = &mut s.stats.current_component {
                        d.state = "searching-without-hypothesis";
                    }
                    s.metrics();
                    if base.is_none() {
                        let slice =
                            existence_slice::Slice::new(&world_view, Some(h), s.run.budget)?;
                        let encoded = s.encode_view(&slice.core, original, false)?;
                        base = Some((slice, encoded));
                    }
                    let (base_slice, base) = base.as_ref().unwrap();
                    if !s.solve(&[base.gate], &pins)? {
                        return Ok(Some(world));
                    }
                    let values = s.existence_values(base_slice, original, base)?;
                    let cube = cover(&base_slice.core, &values, None, s.run.budget)?;
                    s.exclude(selector, &cube)?;
                }
            },
        )
    }
    fn symbolic_no_meaning_cone(
        &self,
        context: &BTreeMap<GroundAtom, bool>,
        classification: bool,
        unique: bool,
        options: &CheckOptions,
        shares: usize,
        cone: &Cone,
    ) -> Result<Search<Observation>> {
        let phase = if classification {
            "completion classification existence"
        } else {
            "completion processing existence"
        };
        self.symbolic_search_in(context, phase, shares, |s| {
            let view = s.simplified(cone, !classification)?;
            let Some(cone) =
                existence::residual(self, &view, view.label(), classification, s, options)?
            else {
                return Ok(None);
            };
            let cone = &cone;
            let candidate = if !classification {
                self.classification
                    .as_ref()
                    .map(|(c, _, h)| {
                        let view = s.simplified(c, true)?;
                        let slice = existence_slice::Slice::new(&view, Some(*h), s.run.budget)?;
                        s.encode_view(&slice.core, c, true)
                    })
                    .transpose()?
            } else {
                None
            };
            let h = self.classification.as_ref().map(|(_, _, h)| *h);
            let slice = existence_slice::Slice::new(cone, h, s.run.budget)?;
            let target = s.encode_view(&slice.core, cone, !classification)?;
            let selector = s.gate()?;
            let mut active = vec![selector];
            if let Some(candidate) = &candidate {
                active.push(candidate.gate);
            }
            loop {
                if !s.solve(&active, &[])? {
                    return Ok(None);
                }
                s.run
                    .budget
                    .room(s.stats.rounds, options.max_worlds, phase, "worlds")?;
                s.stats.rounds += 1;
                s.metrics();
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
                let values = s.existence_values(&slice, cone, &target)?;
                let h = (!classification)
                    .then(|| self.classification.as_ref().map(|(_, _, h)| *h))
                    .flatten();
                let cube = cover(&slice.core, &values, h, s.run.budget)?;
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
                s.stats.rounds += 1;
                s.metrics();
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
        s: &mut Solver<'_, '_, '_>,
        encoded: &Encoded,
        selector: Lit,
    ) -> Result<Option<Model>> {
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
            s.stats.rounds += 1;
            s.metrics();
            let world = s.world()?;
            if !unique && self.classification.is_some() {
                if let Some(cube) = s.eligible(&world, unique)? {
                    s.exclude(selector, &cube)?;
                    continue;
                }
                let mut restored = s.pins(&world)?;
                restored.extend_from_slice(&pins);
                if !s.solve(&[encoded.gate, selector], &restored)? {
                    return Err(CheckError::Internal(
                        "eligible completion property disappeared",
                    ));
                }
            }
            let mut model = self.model(s.property_values(cone, encoded)?, ModelScope::Property);
            model.members = Some(members.clone());
            return Ok(Some(model));
        }
    }
}

impl Engine {
    /// Verification-wide questions are independent symbolic searches. In
    /// particular, a processing contradiction never filters the input universe
    /// or the original classification query.
    pub fn check(&self, keys: &SemanticKeys, options: &CheckOptions) -> Result<Report> {
        if !self.limits.completion_exploration {
            return self.check_scheduled(keys, options);
        }
        let mut invocation = self.clone();
        // API callers get one deadline across this verification, not a fresh
        // timeout per mechanism. CLI preparation already set the run deadline.
        if invocation.limits.run_deadline.is_none() {
            invocation.limits.run_deadline = Instant::now().checked_add(invocation.limits.timeout);
        }
        for (stage, enabled) in [
            ("completion exploration pruning", options.prune),
            ("completion exploration forcing", options.force),
            ("completion exploration splits", options.split_depth > 0),
        ] {
            invocation.exploration(
                stage,
                if enabled {
                    "not-started"
                } else {
                    "not-started-disabled"
                },
                0,
                Duration::ZERO,
            );
        }
        let started = Instant::now();
        let result = invocation.check_scheduled(keys, options);
        if let Ok(report) = &result {
            fn state<T>(s: &Search<T>) -> &'static str {
                match s {
                    Search::NotAnalysed => "not-started",
                    Search::Inconclusive(_) => "cut-off",
                    _ => "completed",
                }
            }
            if let Some(c) = &report.classification {
                for (phase, status) in [
                    ("completion accepted observations", state(&c.accepted)),
                    ("completion rejection", state(&c.rejected)),
                    ("completion classification existence", state(&c.no_meaning)),
                    ("completion classification ambiguity", state(&c.ambiguous)),
                ] {
                    invocation.limits.progress.exploration(
                        phase,
                        status,
                        "status",
                        0,
                        Duration::ZERO,
                    );
                }
            }
            invocation.exploration(
                "completion processing existence",
                state(&report.meaning.no_meaning),
                0,
                started.elapsed(),
            );
            invocation.exploration(
                "completion processing ambiguity",
                state(&report.meaning.ambiguous),
                0,
                started.elapsed(),
            );
        }
        invocation.exploration(
            "completion exploration",
            if result.is_ok() {
                "finished"
            } else {
                "cut-off"
            },
            0,
            started.elapsed(),
        );
        result
    }
    pub(super) fn exploration(
        &self,
        phase: &'static str,
        state: &'static str,
        work: usize,
        elapsed: Duration,
    ) {
        if self.limits.completion_exploration {
            self.limits
                .progress
                .exploration(phase, state, "work", work, elapsed);
        }
    }
    fn check_scheduled(&self, keys: &SemanticKeys, options: &CheckOptions) -> Result<Report> {
        if !options.prune && !options.force && options.split_depth == 0 {
            return self.check_unpruned(keys, options);
        }
        let mut invocation = self.clone();
        invocation.forcing = options.force && options.split_depth > 0;
        let cache = Arc::new(std::sync::Mutex::new(pruning::Cache::for_engine(self)));
        if options.prune && options.split_depth > 0 {
            cache.lock().unwrap().enable_trials(self);
            // Exploration proves reductions in the unit, after its cheap probe.
            // Raw questions may reuse views but never initiate root proof search.
            if self.limits.completion_exploration {
                cache.lock().unwrap().readonly = true;
            }
        }
        if options.prune {
            invocation.pruning = Some(cache.clone());
        }
        let branches = Arc::new(std::sync::Mutex::new(BranchReport::default()));
        if options.split_depth > 0 || options.force {
            invocation.branches = Some(branches.clone());
        }
        if options.prune && !(self.limits.completion_exploration && options.split_depth > 0) {
            if invocation.classification.is_some() {
                pruning::prepare(&invocation, true)?;
            }
            pruning::prepare(&invocation, false)?;
        }
        let mut report = invocation.check_unpruned(keys, options)?;
        report.pruning = cache.lock().unwrap().report.clone();
        if let Some(pool) = &cache.lock().unwrap().trials {
            pool.lock().unwrap().summarize(&mut report.pruning);
        }
        report.pruning.enabled = options.prune;
        report.branches = branches.lock().unwrap().clone();
        report.branches.enabled = options.split_depth > 0 || options.force;
        Ok(report)
    }
    pub(super) fn check_unpruned(
        &self,
        keys: &SemanticKeys,
        options: &CheckOptions,
    ) -> Result<Report> {
        if options.meaning != MeaningMode::Full {
            return Err(CheckError::InvalidRequest(
                "completion supports full meaning analysis only",
            ));
        }
        let mut report = Report {
            pruning: Default::default(),
            branches: Default::default(),
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
        let mut remaining = report.obligations.len()
            + 2
            + if report.classification.is_some() {
                4
            } else {
                0
            };
        if let Some(c) = &mut report.classification {
            // Ordinary searches receive a bounded part of the remaining
            // shared deadline. Exploration moves the potentially expensive
            // classification cover behind the gating questions below.
            c.rejected = self.symbolic_rejected(options, remaining)?;
            remaining -= 1;
            if !self.limits.completion_exploration {
                c.no_meaning = self.symbolic_no_meaning(true, true, options, remaining)?;
                remaining -= 1;
            }
            c.ambiguous = self.symbolic_pair(true, true, options, remaining)?;
            remaining -= 1;
            globally_unique = matches!(c.ambiguous, Search::None);
            c.accepted = self.symbolic_accepted(globally_unique, options, remaining)?;
            remaining -= 1;
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
            remaining = remaining.saturating_sub(2);
            report.meaning.no_meaning = Search::None;
            report.meaning.ambiguous = Search::None;
        } else {
            report.meaning.no_meaning =
                self.symbolic_no_meaning(false, globally_unique, options, remaining)?;
            remaining -= 1;
            report.meaning.ambiguous =
                self.symbolic_pair(false, globally_unique, options, remaining)?;
            remaining -= 1;
            for state in [
                &report.meaning.no_meaning as &dyn Unknown,
                &report.meaning.ambiguous,
            ] {
                if let Some(cause) = state.unknown() {
                    report.incomplete.push(cause);
                }
            }
        }
        for (id, property) in &mut report.obligations {
            let _progress = self.limits.progress.scope(
                "completion property",
                Some(crate::CheckingTarget::Obligation(*id)),
                true,
            );
            let limits = self.shared_limits(remaining);
            remaining = remaining.saturating_sub(1);
            let mut budget = Budget::new(&limits);
            if !vacuous {
                if let Some(members) = property.members.clone() {
                    let mut cone = self.cone.as_ref().clone();
                    cone.rules.retain(|r| members.contains(&cone.atoms[r.head]));
                    let result: Result<()> = (|| {
                        let mut solver = Solver::new(self, &mut budget)?;
                        solver.run.label("completion property");
                        let encoded = solver.encode(&cone, true)?;
                        let selector = solver.gate()?;
                        let mut retained = 0;
                        let mut previous: Option<Model> = None;
                        let mut queried = false;
                        let part_count = property.parts.len();
                        let mut failures = 0;
                        for (part_index, part) in property.parts.iter_mut().enumerate() {
                            solver.run.budget.tick("completion property tuples")?;
                            // A validated interpretation may witness several
                            // empty failures. Reusing it asserts presence only;
                            // absence still requires its own universal search.
                            let reuse = part.component == Cardinality::Empty
                                && previous.as_ref().is_some_and(|m| {
                                    part.tuples
                                        .iter()
                                        .all(|a| m.values[self.program.atom_index[a]])
                                });
                            let model = if reuse {
                                previous.clone()
                            } else {
                                if queried {
                                    solver.run.next_property_part()?;
                                }
                                queried = true;
                                self.symbolic_property(
                                    &cone,
                                    members.clone(),
                                    part,
                                    globally_unique,
                                    options,
                                    &mut solver,
                                    &encoded,
                                    selector,
                                )?
                            };
                            if let Some(model) = model {
                                previous = Some(model.clone());
                                part.failed = true;
                                if retained < options.max_examples {
                                    part.example = Some(model);
                                    retained += 1;
                                }
                                failures += 1;
                                if failures >= options.max_failures.max(1)
                                    && part_index + 1 < part_count
                                {
                                    property.failures_truncated = true;
                                    break;
                                }
                            }
                        }
                        Ok(())
                    })();
                    if let Err(e) = result {
                        property.inconclusive =
                            Some(inconclusive(e.in_phase("completion property", None))?);
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
        // Classification existence is independent of the gating questions.
        // Its universal cover can be the hardest search, so exploration spends
        // only the invocation's remaining time here. Its verdict is unchanged.
        if self.limits.completion_exploration {
            if let Some(c) = &mut report.classification {
                c.no_meaning = self.symbolic_no_meaning(true, true, options, remaining)?;
                if let Some(cause) = c.no_meaning.unknown() {
                    report.incomplete.push(cause);
                }
            }
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

#[cfg(test)]
pub(super) fn has_cycle_for_test(c: &Cone) -> bool {
    consistency::analyse(c, None, &mut Budget::new(&Limits::default()))
        .unwrap()
        .cyclic
        .iter()
        .any(|v| *v)
}

#[cfg(test)]
mod lifting_scope_tests;
