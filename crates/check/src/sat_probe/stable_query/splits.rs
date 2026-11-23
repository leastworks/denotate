//! One-level partition of W by a declared exactly-one input group.
use super::*;

#[derive(Debug, Clone)]
pub struct SplitOptions {
    /// Zero disables automatic and hinted split search.
    pub max_candidates: usize,
    pub max_members: usize,
    /// Optional ranking cap; default inherits checker max_work.
    pub max_work: usize,
    /// Restrict candidate groups to this input relation; never an assumed fact.
    pub relation: Option<RelationId>,
}
impl Default for SplitOptions {
    fn default() -> Self {
        Self {
            max_candidates: 8,
            max_members: 32,
            max_work: usize::MAX,
            relation: None,
        }
    }
}
#[derive(Debug)]
pub struct SplitBranch {
    pub member: GroundAtom,
    pub existence: &'static str,
    pub uniqueness: &'static str,
    pub stratified: bool,
}
#[derive(Debug)]
pub struct SplitStats {
    pub group: Vec<GroundAtom>,
    pub candidates: usize,
    pub ranking_incomplete: bool,
    pub branches: Vec<SplitBranch>,
}
impl Engine {
    fn compatible_pins(&self, pins: &BTreeMap<GroundAtom, bool>) -> bool {
        pins.iter()
            .all(|(a, v)| self.input_pins.get(a).is_none_or(|known| known == v))
    }
    fn member_pins(group: &[GroundAtom], member: &GroundAtom) -> BTreeMap<GroundAtom, bool> {
        group.iter().map(|a| (a.clone(), a == member)).collect()
    }
    fn rank_split(&self, options: &SplitOptions, outer: &Budget<'_>) -> Result<Option<SplitStats>> {
        if options.max_candidates == 0 {
            return Ok(None);
        }
        let mut limits = self.limits.clone();
        limits.max_work = limits.max_work.min(options.max_work);
        limits.timeout = limits.timeout.min(outer.remaining_time());
        let mut b = Budget::new(&limits);
        let mut best: Option<(Vec<usize>, Vec<GroundAtom>)> = None;
        let mut considered = 0;
        let mut incomplete = false;
        let ranked: Result<()> = (|| {
            let inputs = self.negative_input_support(&mut b)?;
            // Only rules upstream of a negative component matter to this score.
            let mut reached = BTreeSet::new();
            let mut todo: Vec<_> = self
                .program
                .core
                .components
                .iter()
                .filter(|c| c.cycle.is_some())
                .map(|c| c.id.index)
                .collect();
            while let Some(i) = todo.pop() {
                b.tick("SAT split ranking cone")?;
                if reached.insert(i) {
                    todo.extend(
                        self.program.core.components[i]
                            .dependencies
                            .iter()
                            .map(|d| d.index),
                    );
                }
            }
            let mut base = (*self.program).clone();
            let mut rules = Vec::new();
            for r in &self.program.core.rules {
                b.tick("SAT split ranking rules")?;
                let head = self.program.core.atom_index[&r.head.atom];
                if reached.contains(&self.program.core.atom_components[head].index) {
                    let mut r = r.clone();
                    r.id.index = rules.len();
                    rules.push(r);
                }
            }
            base.rules = rules;
            let mut eligible = 0;
            for group in &self.split_groups {
                b.tick("SAT split candidates")?;
                if group.len() > options.max_members
                    || !group.iter().any(|a| inputs.contains(a))
                    || options
                        .relation
                        .is_some_and(|r| group.iter().any(|a| a.relation != r))
                {
                    continue;
                }
                eligible += 1;
                if considered == options.max_candidates {
                    incomplete = true;
                    break;
                }
                let mut score = Vec::new();
                for member in group {
                    let pins = Self::member_pins(group, member);
                    if !self.compatible_pins(&pins) {
                        score.push(0);
                        continue;
                    }
                    let (p, _, _, _) = base.settle_atoms_with_inputs(None, &pins, &mut b)?;
                    score.push(
                        p.core
                            .components
                            .iter()
                            .filter(|c| c.cycle.is_some())
                            .map(|c| c.atoms.len())
                            .sum(),
                    );
                }
                score.sort_unstable_by(|a, b| b.cmp(a)); // minimize the worst branch first
                considered += 1;
                if best.as_ref().is_none_or(|(old, _)| score < *old) {
                    best = Some((score, group.clone()));
                }
            }
            if options.relation.is_some() && eligible == 0 {
                return Err(CheckError::InvalidRequest(
                    "split hint has no eligible exactly-one input group in a negative cone",
                ));
            }
            Ok(())
        })();
        if let Err(e) = ranked {
            query_inconclusive(e)?;
            incomplete = true;
        }
        outer.check("SAT split ranking")?;
        Ok(best.map(|(_, group)| SplitStats {
            group,
            candidates: considered,
            ranking_incomplete: incomplete,
            branches: vec![],
        }))
    }

    fn branch_engine(&self, pins: BTreeMap<GroundAtom, bool>, b: &mut Budget<'_>) -> Result<Self> {
        let mut limits = self.limits.clone();
        limits.timeout = limits.timeout.min(b.remaining_time());
        let mut input_pins = self.input_pins.clone();
        input_pins.extend(pins.clone());
        let cnf = Cnf {
            measurement: None,
            solver: Solver::new(
                Default::default(),
                Stop {
                    deadline: None,
                    polls: None,
                    cancellation: limits.cancellation.clone(),
                    start: Instant::now(),
                    timeout: limits.timeout,
                    #[cfg(test)]
                    hook: None,
                },
            ),
            clauses: 0,
            literals: 0,
            gate: None,
        };
        let mut e = Self {
            program: self.program.clone(),
            original: self.original.clone(),
            settled: self.settled.clone(),
            preparation_receipts: self.preparation_receipts.clone(),
            scope: self.scope.clone(),
            scope_atoms: self.scope_atoms.clone(),
            origins: self.origins.clone(),
            input_pins,
            pinned_values: self.pinned_values.clone(),
            pin_stats: self.pin_stats.clone(),
            split_groups: vec![],
            ordered_inputs: vec![],
            input_relations: self.input_relations.clone(),
            cone: self.cone.clone(),
            world_cone: self.world_cone.clone(),
            cnf,
            program_encoding: Encoding {
                vars: vec![],
                bodies: vec![],
            },
            world_encoding: Encoding {
                vars: vec![],
                bodies: vec![],
            },
            // Replaced before any query. No parent selectors are reused.
            active: self.active,
            truth: self.truth,
            pair_encoding: None,
            verification: self.verification,
            selection: self.selection.clone(),
            notices: self.notices.clone(),
            columns: self.columns.clone(),
            residual_relations: self.residual_relations.clone(),
            limits,
            config: self.config.clone(),
            cache: VecDeque::new(),
            cache_bytes: 0,
            stats: Stats::default(),
            append_failed: None,
        };
        e.fold_pins(pins, b)?;
        e.reset_world(b)?;
        e.encode_program(b)?;
        Ok(e)
    }
    pub(super) fn split_meaning(
        &mut self,
        options: &CheckOptions,
        outer: &mut Budget<'_>,
    ) -> Result<Option<Meaning>> {
        let Some(mut stats) = self.rank_split(&options.splits, outer)? else {
            return Ok(None);
        };
        let _progress = self.limits.progress.scope("SAT meaning split", None, true);
        let existence_requested = matches!(options.meaning, MeaningMode::Full | MeaningMode::Cone);
        let uniqueness_requested = options.meaning != MeaningMode::Cone;
        let mut result = Meaning {
            mode: options.meaning,
            split: None,
            existence_stats: None,
            uniqueness_stats: None,
            existence: if existence_requested {
                Existence::EveryWorld
            } else {
                Existence::NotAnalysed
            },
            uniqueness: if uniqueness_requested {
                Uniqueness::AtMostOne
            } else {
                Uniqueness::NotAnalysed
            },
        };
        let mut branch_options = options.clone();
        branch_options.splits.max_candidates = 0;
        for member in stats.group.clone() {
            let pins = Self::member_pins(&stats.group, &member);
            if !self.compatible_pins(&pins) {
                stats.branches.push(SplitBranch {
                    member,
                    existence: "empty-context",
                    uniqueness: "empty-context",
                    stratified: false,
                });
                continue;
            }
            let checked: Result<Option<(Meaning, bool)>> = (|| {
                outer.check("SAT meaning split")?;
                match self.phase_query(
                    Mode::World,
                    &Query {
                        pins: pins.iter().map(|(a, v)| (a.clone(), *v)).collect(),
                        exclude: vec![],
                    },
                    outer,
                )? {
                    Answer::NoModel => return Ok(None),
                    Answer::Inconclusive(c) => {
                        return Ok(Some((unknown(options.meaning, c), false)));
                    }
                    Answer::Model(_) => (),
                }
                // Deterministic per-branch phase allowances; one shared deadline.
                let mut branch_limits = self.limits.clone();
                branch_limits.timeout = branch_limits.timeout.min(outer.remaining_time());
                let mut preparation = Budget::new(&branch_limits);
                let mut branch = self.branch_engine(pins, &mut preparation)?;
                branch.limits.timeout = branch.limits.timeout.min(outer.remaining_time());
                let stratified = branch
                    .program
                    .core
                    .components
                    .iter()
                    .all(|c| c.cycle.is_none());
                Ok(Some((
                    branch.meaning_with_deadline(&branch_options, Some(&*outer))?,
                    stratified,
                )))
            })();
            let (m, stratified) = match checked {
                Ok(None) => {
                    stats.branches.push(SplitBranch {
                        member,
                        existence: "empty-context",
                        uniqueness: "empty-context",
                        stratified: false,
                    });
                    continue;
                }
                Ok(Some(m)) => m,
                Err(e) => (unknown(options.meaning, query_inconclusive(e)?), false),
            };
            stats.branches.push(SplitBranch {
                member,
                existence: existence_label(&m.existence),
                uniqueness: uniqueness_label(&m.uniqueness),
                stratified,
            });
            // Known failures survive an unknown sibling. Proved requires all arms.
            match m.existence {
                x @ Existence::NoMeaning(_) => result.existence = x,
                x @ Existence::Inconclusive(_) => {
                    if !matches!(result.existence, Existence::NoMeaning(_)) {
                        result.existence = x;
                    }
                }
                _ => (),
            }
            match m.uniqueness {
                x @ Uniqueness::Multiple { .. } => result.uniqueness = x,
                x @ Uniqueness::Inconclusive(_) => {
                    if !matches!(result.uniqueness, Uniqueness::Multiple { .. }) {
                        result.uniqueness = x;
                    }
                }
                _ => (),
            }
        }
        result.split = Some(stats);
        Ok(Some(result))
    }
}
fn unknown(mode: MeaningMode, c: Inconclusive) -> Meaning {
    Meaning {
        mode,
        split: None,
        existence_stats: None,
        uniqueness_stats: None,
        existence: if mode == MeaningMode::Uniqueness {
            Existence::NotAnalysed
        } else {
            Existence::Inconclusive(c)
        },
        uniqueness: if mode == MeaningMode::Cone {
            Uniqueness::NotAnalysed
        } else {
            Uniqueness::Inconclusive(c)
        },
    }
}
pub(super) fn existence_label(e: &Existence) -> &'static str {
    match e {
        Existence::NotAnalysed => "not-analysed",
        Existence::EveryWorld => "every-world",
        Existence::NoMeaning(_) => "no-meaning",
        Existence::Inconclusive(_) => "inconclusive",
    }
}
pub(super) fn uniqueness_label(e: &Uniqueness) -> &'static str {
    match e {
        Uniqueness::NotAnalysed => "not-analysed",
        Uniqueness::AtMostOne => "at-most-one",
        Uniqueness::Multiple { .. } => "multiple-meanings",
        Uniqueness::Inconclusive(_) => "inconclusive",
    }
}
