//! Encoding-size experiment only: bounded local BDD proofs, no checking verdicts.
//! CNF elimination never modifies the original ground rules.
use crate::{
    limits::{Budget, Result},
    *,
};
use denotate_ir::{Corpus, RelationId};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Default)]
pub struct Size {
    pub variables: usize,
    pub clauses: usize,
    pub literals: usize,
    /// Owned vector capacities, excluding allocator overhead and ground program.
    pub storage_bytes: usize,
}
#[derive(Debug, Clone, Default)]
pub struct RelationSize {
    /// Variable/clause descriptors and literal capacities; excludes outer-vector slack.
    pub payload_bytes: usize,
    pub atom_variables: usize,
    pub auxiliary_variables: usize,
    pub clauses: usize,
    pub literals: usize,
}
#[derive(Debug)]
pub struct Report {
    pub before: Size,
    pub after: Size,
    /// Before elimination, after any pre-encoding simplification.
    pub relations: BTreeMap<RelationId, RelationSize>,
    pub after_relations: BTreeMap<RelationId, RelationSize>,
    pub eliminated: usize,
    pub reconstruction_bytes: usize,
    pub residual_atoms: usize,
    pub residual_rules: usize,
    pub fixed_atoms: usize,
}

#[derive(Clone)]
struct Clause {
    lits: Vec<i32>,
    owner: RelationId,
}
#[derive(Default)]
struct Cnf {
    clauses: Vec<Clause>,
    owners: Vec<(RelationId, bool)>, // bool: named atom, otherwise auxiliary
    protected: BTreeSet<usize>,
    eliminated: Vec<(usize, Vec<Clause>)>,
    literals: usize,
}
impl Cnf {
    fn var(&mut self, owner: RelationId, atom: bool, b: &mut Budget<'_>) -> Result<i32> {
        b.room(
            self.owners.len(),
            b.limits.max_atoms.min(i32::MAX as usize - 1),
            "CNF measurement",
            "variables",
        )?;
        self.owners.push((owner, atom));
        Ok(self.owners.len() as i32)
    }
    fn clause(&mut self, lits: Vec<i32>, owner: RelationId, b: &mut Budget<'_>) -> Result<()> {
        b.charge(lits.len() + 1, "CNF measurement")?;
        let Some(lits) = normalize(lits) else {
            return Ok(());
        };
        b.room(
            self.clauses.len(),
            b.limits.max_rules,
            "CNF measurement",
            "clauses",
        )?;
        b.room(
            self.literals.saturating_add(lits.len()),
            b.limits.max_dependencies.saturating_add(1),
            "CNF measurement",
            "literals",
        )?;
        self.literals += lits.len();
        self.clauses.push(Clause { lits, owner });
        Ok(())
    }
    fn size(&self) -> Size {
        Size {
            variables: self.owners.len() - self.eliminated.len(),
            clauses: self.clauses.len(),
            literals: self.clauses.iter().map(|c| c.lits.len()).sum(),
            storage_bytes: self.clauses.capacity() * std::mem::size_of::<Clause>()
                + self
                    .clauses
                    .iter()
                    .map(|c| c.lits.capacity() * 4)
                    .sum::<usize>()
                + self.owners.capacity() * std::mem::size_of::<(RelationId, bool)>(),
        }
    }
    fn by_relation(&self) -> BTreeMap<RelationId, RelationSize> {
        let mut rows = BTreeMap::<_, RelationSize>::new();
        let eliminated: BTreeSet<_> = self.eliminated.iter().map(|(v, _)| *v).collect();
        for (i, (r, atom)) in self.owners.iter().enumerate() {
            let row = rows.entry(*r).or_default();
            row.payload_bytes += std::mem::size_of::<(RelationId, bool)>();
            if eliminated.contains(&i) {
                continue;
            }
            if *atom {
                row.atom_variables += 1;
            } else {
                row.auxiliary_variables += 1;
            }
        }
        for c in &self.clauses {
            let row = rows.entry(c.owner).or_default();
            row.payload_bytes += std::mem::size_of::<Clause>() + c.lits.capacity() * 4;
            row.clauses += 1;
            row.literals += c.lits.len();
        }
        rows
    }
    /// One deterministic bounded pass. Only single-reader named definitions are
    /// candidates. Resolution must not increase either clauses or literal storage.
    fn eliminate(&mut self, candidates: &[usize], b: &mut Budget<'_>) -> Result<()> {
        // Index original and newly emitted clauses; tombstones avoid quadratic scans.
        let mut slots: Vec<_> = self.clauses.drain(..).map(Some).collect();
        let mut occurrences = vec![Vec::new(); self.owners.len()];
        for (i, c) in slots.iter().enumerate() {
            b.charge(c.as_ref().unwrap().lits.len() + 1, "CNF elimination index")?;
            for l in &c.as_ref().unwrap().lits {
                occurrences[l.unsigned_abs() as usize - 1].push(i);
            }
        }
        for &v in candidates {
            b.tick("CNF elimination")?;
            if self.protected.contains(&v) {
                continue;
            }
            b.charge(occurrences[v].len(), "CNF elimination index")?;
            let ids: Vec<_> = occurrences[v]
                .iter()
                .copied()
                .filter(|i| slots[*i].is_some())
                .collect();
            let (pos, neg): (Vec<_>, Vec<_>) = ids
                .iter()
                .copied()
                .partition(|i| slots[*i].as_ref().unwrap().lits.contains(&((v + 1) as i32)));
            // Local bound, independent of global checker limits; skipped candidates
            // leave the exact original clauses intact.
            if pos.len().saturating_mul(neg.len()) > 64 {
                continue;
            }
            let old_literals: usize = ids
                .iter()
                .map(|i| slots[*i].as_ref().unwrap().lits.len())
                .sum();
            let mut resolvents = BTreeSet::new();
            for i in &pos {
                for j in &neg {
                    let a = &slots[*i].as_ref().unwrap().lits;
                    let z = &slots[*j].as_ref().unwrap().lits;
                    b.charge(a.len() + z.len(), "CNF elimination")?;
                    if let Some(r) = normalize(
                        a.iter()
                            .chain(z)
                            .copied()
                            .filter(|l| l.unsigned_abs() as usize != v + 1)
                            .collect(),
                    ) {
                        resolvents.insert(r);
                    }
                }
            }
            if resolvents.len() > ids.len()
                || resolvents.iter().map(Vec::len).sum::<usize>() > old_literals
            {
                continue;
            }
            let removed: Vec<_> = ids.into_iter().map(|i| slots[i].take().unwrap()).collect();
            self.eliminated.push((v, removed));
            for lits in resolvents {
                for l in &lits {
                    occurrences[l.unsigned_abs() as usize - 1].push(slots.len());
                }
                slots.push(Some(Clause {
                    lits,
                    owner: self.owners[v].0,
                }));
            }
        }
        self.clauses = slots.into_iter().flatten().collect();
        Ok(())
    }
    #[cfg(test)]
    fn reconstruct(&self, mut values: Vec<bool>) -> Vec<bool> {
        for (v, clauses) in self.eliminated.iter().rev() {
            values[*v] = clauses.iter().any(|c| {
                c.lits.contains(&((*v + 1) as i32))
                    && !c
                        .lits
                        .iter()
                        .filter(|l| l.unsigned_abs() as usize != *v + 1)
                        .any(|l| values[l.unsigned_abs() as usize - 1] == (*l > 0))
            });
        }
        values
    }
}
fn normalize(lits: Vec<i32>) -> Option<Vec<i32>> {
    normalize_literals(lits, |l| -l)
}

/// Shared literal normalization for measurement and completion encoding.
/// A complementary pair makes a conjunction false (or a clause tautological).
pub(crate) fn normalize_literals<T: Copy + Ord>(
    mut lits: Vec<T>,
    negate: impl Fn(T) -> T,
) -> Option<Vec<T>> {
    lits.sort_unstable();
    lits.dedup();
    if lits.iter().any(|l| lits.binary_search(&negate(*l)).is_ok()) {
        None
    } else {
        Some(lits)
    }
}

/// A prepared whole-program measurement. Preparation folds fixed facts but does
/// not construct W, evaluate input-dependent conditions, or run admission.
/// The original graph is retained for validation; this is not a checking backend.
pub struct Measurement {
    program: GroundProgram,
}
impl Measurement {
    pub fn prepare(corpus: &Corpus, domains: &Domains, limits: &Limits) -> Result<Self> {
        let fixed = FixedPreparation::prepare(corpus, domains, limits)?;
        let program = GroundProgram::prepare_using_fixed(
            corpus,
            domains,
            &[],
            &BTreeSet::new(),
            &mut Budget::new(limits),
            None,
            Some(&fixed),
        )?;
        Ok(Self { program })
    }
    pub fn measure(&self, eliminate: bool, limits: &Limits) -> Result<Report> {
        let mut b = Budget::new(limits);
        b.tick("CNF measurement")?;
        let (mut cnf, candidates) = encode(&self.program, &mut b)?;
        self.report_cnf(&mut cnf, &candidates, eliminate, &mut b)
    }
    fn report_cnf(
        &self,
        cnf: &mut Cnf,
        candidates: &[usize],
        eliminate: bool,
        b: &mut Budget<'_>,
    ) -> Result<Report> {
        let before = cnf.size();
        let relations = cnf.by_relation();
        if eliminate {
            cnf.eliminate(candidates, b)?;
        }
        let reconstruction_bytes = cnf.eliminated.capacity()
            * std::mem::size_of::<(usize, Vec<Clause>)>()
            + cnf
                .eliminated
                .iter()
                .map(|(_, cs)| {
                    cs.capacity() * std::mem::size_of::<Clause>()
                        + cs.iter().map(|c| c.lits.capacity() * 4).sum::<usize>()
                })
                .sum::<usize>();
        let (fixed_atoms, _, _, _, _) = self.program.fixed_size();
        Ok(Report {
            before,
            after: cnf.size(),
            relations,
            after_relations: cnf.by_relation(),
            eliminated: cnf.eliminated.len(),
            reconstruction_bytes,
            residual_atoms: self.program.core.atoms.len(),
            residual_rules: self.program.core.rules.len(),
            fixed_atoms,
        })
    }
}
mod structure;
pub use structure::{RecursiveComponent, RecursiveReport, RecursiveSizes};
mod model;
mod simplify;
pub use simplify::{
    LocalDifference, Pass, PassStats, ProofObservation, ProofShape, SimplificationLimits, Variant,
};

fn encode(p: &GroundProgram, b: &mut Budget<'_>) -> Result<(Cnf, Vec<usize>)> {
    model::Model::new(p, b)?.encode(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{rel, rule};
    fn holds(c: &Cnf, values: &[bool]) -> bool {
        c.clauses.iter().all(|c| {
            c.lits
                .iter()
                .any(|l| values[l.unsigned_abs() as usize - 1] == (*l > 0))
        })
    }
    fn assignments(n: usize) -> impl Iterator<Item = Vec<bool>> {
        (0..1usize << n).map(move |bits| (0..n).map(|i| bits & (1 << i) != 0).collect())
    }
    #[test]
    fn elimination_preserves_projection_and_reconstructs_models() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let h = rel(&mut c, "h", false);
        let p = rel(&mut c, "p", false);
        rule(&mut c, h, &[(x, true)]);
        rule(&mut c, p, &[(h, true)]);
        let limits = Limits::default();
        let m = Measurement::prepare(&c, &Domains::new(), &limits).unwrap();
        let (mut cnf, candidates) = encode(&m.program, &mut Budget::new(&limits)).unwrap();
        let old = cnf.clauses.clone();
        cnf.eliminate(&candidates, &mut Budget::new(&limits))
            .unwrap();
        assert!(!cnf.eliminated.is_empty());
        for values in assignments(cnf.owners.len()) {
            if holds(&cnf, &values) {
                let full = cnf.reconstruct(values);
                assert!(old.iter().all(|c| {
                    c.lits
                        .iter()
                        .any(|l| full[l.unsigned_abs() as usize - 1] == (*l > 0))
                }));
            }
        }
        // Every original model remains a model of the projected formula.
        for values in assignments(cnf.owners.len()) {
            if old.iter().all(|c| {
                c.lits
                    .iter()
                    .any(|l| values[l.unsigned_abs() as usize - 1] == (*l > 0))
            }) {
                assert!(holds(&cnf, &values));
            }
        }
    }
    #[test]
    fn negative_cycle_keeps_both_meanings() {
        let mut c = Corpus::new();
        let p = rel(&mut c, "p", false);
        let h = rel(&mut c, "h", false);
        rule(&mut c, p, &[(h, true)]);
        rule(&mut c, h, &[(p, true)]);
        let l = Limits::default();
        let m = Measurement::prepare(&c, &Domains::new(), &l).unwrap();
        let (mut cnf, candidates) = encode(&m.program, &mut Budget::new(&l)).unwrap();
        cnf.eliminate(&candidates, &mut Budget::new(&l)).unwrap();
        assert_eq!(
            assignments(cnf.owners.len())
                .filter(|v| holds(&cnf, v))
                .count(),
            2
        );
        assert_eq!(
            crate::test_support::rewrites::stable_models(
                &m.program.atoms().cloned().collect::<Vec<_>>(),
                &m.program.inputs,
                &m.program.rules().cloned().collect::<Vec<_>>(),
                &BTreeSet::new()
            )
            .len(),
            2
        );
    }
    #[test]
    fn tiny_completions_match_independent_supported_model_oracle() {
        use crate::test_support::rewrites::{subsets, supported_models};
        for mask in 0..32 {
            let mut c = Corpus::new();
            let x = rel(&mut c, "x", true);
            let y = rel(&mut c, "y", true);
            let a = rel(&mut c, "a", false);
            let z = rel(&mut c, "z", false);
            let definitions = [
                (a, vec![(x, false), (y, false)]),
                (a, vec![(z, true)]),
                (z, vec![(a, false), (y, true)]),
                (z, vec![(x, true)]),
                (a, vec![(x, false)]),
            ];
            for (i, (h, body)) in definitions.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    rule(&mut c, *h, body);
                }
            }
            let l = Limits::default();
            let m = Measurement::prepare(&c, &Domains::new(), &l).unwrap();
            let (cnf, _) = encode(&m.program, &mut Budget::new(&l)).unwrap();
            let atoms = &m.program.core.atoms;
            let fixed: BTreeSet<_> = m
                .program
                .atoms()
                .filter(|a| m.program.fixed_value(a) == Some(true))
                .cloned()
                .collect();
            for world in subsets(&m.program.inputs.iter().cloned().collect::<Vec<_>>()) {
                let actual: BTreeSet<BTreeSet<_>> = assignments(cnf.owners.len())
                    .filter(|v| holds(&cnf, v))
                    .filter(|v| {
                        atoms.iter().enumerate().all(|(i, a)| {
                            !m.program.inputs.contains(a) || v[i] == world.contains(a)
                        })
                    })
                    .map(|v| {
                        fixed
                            .iter()
                            .cloned()
                            .chain(
                                atoms
                                    .iter()
                                    .enumerate()
                                    .filter(|(i, _)| v[*i])
                                    .map(|(_, a)| a.clone()),
                            )
                            .collect()
                    })
                    .collect();
                let expected = supported_models(
                    &m.program,
                    &m.program.rules().cloned().collect::<Vec<_>>(),
                    &world,
                );
                assert_eq!(actual, expected, "mask {mask}");
            }
        }
    }
    #[test]
    fn declared_cardinality_matches_exhaustive_input_worlds() {
        use denotate_ir::{Cardinality, Parameter, RelationRole};
        for kind in [Cardinality::AtMostOne, Cardinality::ExactlyOne] {
            for n in 0..=8 {
                let mut c = Corpus::new();
                let sort = c.declare_sort("S").unwrap();
                let values: Vec<_> = (0..n)
                    .map(|i| c.declare_constant(format!("v{i}"), sort).unwrap())
                    .collect();
                let input = c
                    .declare_relation(
                        "x",
                        RelationRole::Input,
                        [Parameter {
                            name: "s".into(),
                            sort,
                        }],
                    )
                    .unwrap();
                c.constrain_input(input, kind, []).unwrap();
                let l = Limits::default();
                let m = Measurement::prepare(&c, &Domains::from([(sort, values)]), &l).unwrap();
                let (cnf, _) = encode(&m.program, &mut Budget::new(&l)).unwrap();
                let auxiliaries = cnf.owners.iter().filter(|(_, named)| !named).count();
                assert_eq!(auxiliaries, if n <= 5 { 0 } else { n - 2 });
                for bits in 0..1usize << n {
                    let inputs: Vec<_> = (0..n).map(|i| bits & (1 << i) != 0).collect();
                    let permitted = assignments(auxiliaries).any(|aux| {
                        let mut values = inputs.clone();
                        values.extend(aux);
                        holds(&cnf, &values)
                    });
                    let count = bits.count_ones();
                    assert_eq!(
                        permitted,
                        if kind == Cardinality::ExactlyOne {
                            n == 0 || count == 1
                        } else {
                            count <= 1
                        }
                    );
                }
            }
        }
    }
    #[test]
    fn fixed_evidence_is_not_encoded_and_no_bdd_is_needed() {
        let mut c = Corpus::new();
        let f = rel(&mut c, "fact", false);
        rule(&mut c, f, &[]);
        let l = Limits {
            max_bdd_nodes: 0,
            max_bdd_tasks: 0,
            ..Limits::default()
        };
        let m = Measurement::prepare(&c, &Domains::new(), &l).unwrap();
        let r = m.measure(true, &l).unwrap();
        assert_eq!(r.before.variables, 0);
        assert!(r.fixed_atoms > 0);
    }
    #[test]
    fn limits_and_cancellation_are_errors_not_measurements() {
        let mut c = Corpus::new();
        rel(&mut c, "x", true);
        let l = Limits::default();
        let m = Measurement::prepare(&c, &Domains::new(), &l).unwrap();
        let cancelled = Limits::default();
        cancelled.cancellation.cancel();
        assert!(matches!(
            m.measure(true, &cancelled),
            Err(CheckError::Cancelled)
        ));
        assert!(
            m.measure(
                true,
                &Limits {
                    max_atoms: 0,
                    ..Limits::default()
                }
            )
            .is_err()
        );
        assert!(
            m.measure(
                true,
                &Limits {
                    max_work: 0,
                    ..Limits::default()
                }
            )
            .is_err()
        );
    }
}
