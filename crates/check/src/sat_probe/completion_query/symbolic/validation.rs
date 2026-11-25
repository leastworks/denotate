//! Invocation-local validation of successive models of one immutable cone.
//! The first assignment is checked in full. Thereafter only changed values and
//! their original producers/readers can invalidate an equation. This is not a
//! CNF-model acceptance shortcut and is never reused across scopes or edits.
use super::*;

pub(super) struct Index {
    read: Vec<usize>,
    readers: Vec<Vec<usize>>,
}
impl Index {
    pub fn new(c: &Cone, e: &Encoded, truth: Lit, b: &mut Budget<'_>) -> Result<Self> {
        b.charge(c.fixed.len() + c.rules.len(), "completion validation index")?;
        let variable = |i: usize| e.encoding.vars[i] != truth && e.encoding.vars[i] != !truth;
        let read = (0..c.fixed.len()).filter(|i| variable(*i)).collect();
        let mut readers = vec![Vec::new(); c.fixed.len()];
        for (j, r) in c.rules.iter().enumerate() {
            b.charge(r.body.len() + 1, "completion validation index")?;
            for (i, _) in &r.body {
                if variable(*i) {
                    readers[*i].push(j);
                }
            }
        }
        Ok(Self { read, readers })
    }
}
#[derive(Default)]
pub(super) struct State {
    values: Option<Vec<bool>>,
    alive: Vec<bool>,
    producers: Vec<usize>,
    rules_queued: Vec<bool>,
    heads_queued: Vec<bool>,
}
impl State {
    pub fn update<'a>(
        &'a mut self,
        c: &Cone,
        e: &Encoded,
        index: &Index,
        cnf: &Cnf,
        b: &mut Budget<'_>,
    ) -> Result<&'a [bool]> {
        if self.values.is_none() {
            let values = checked_assignment(c, &e.encoding, cnf, b)?;
            self.producers = vec![0; c.fixed.len()];
            for r in &c.rules {
                b.charge(r.body.len() + 1, "completion model validation")?;
                let alive = r.body.iter().all(|(i, p)| values[*i] == *p);
                self.alive.push(alive);
                if alive {
                    self.producers[r.head] += 1;
                }
            }
            self.rules_queued = vec![false; c.rules.len()];
            self.heads_queued = vec![false; c.fixed.len()];
            self.values = Some(values);
            return Ok(self.values.as_deref().unwrap());
        }
        let values = self.values.as_mut().unwrap();
        let mut rules = Vec::new();
        let mut heads = Vec::new();
        b.charge(index.read.len(), "completion model validation")?;
        for i in &index.read {
            let value = cnf.solver.value_lit(e.encoding.vars[*i]) == lbool::TRUE;
            if value == values[*i] {
                continue;
            }
            values[*i] = value;
            if !self.heads_queued[*i] {
                self.heads_queued[*i] = true;
                heads.push(*i);
            }
            b.charge(index.readers[*i].len(), "completion model validation")?;
            for j in &index.readers[*i] {
                if !self.rules_queued[*j] {
                    self.rules_queued[*j] = true;
                    rules.push(*j);
                }
            }
        }
        for j in rules {
            let r = &c.rules[j];
            b.charge(r.body.len() + 1, "completion model validation")?;
            self.rules_queued[j] = false;
            let alive = r.body.iter().all(|(i, p)| values[*i] == *p);
            if alive != self.alive[j] {
                if alive {
                    self.producers[r.head] += 1;
                } else {
                    self.producers[r.head] -= 1;
                }
                self.alive[j] = alive;
                if !self.heads_queued[r.head] {
                    self.heads_queued[r.head] = true;
                    heads.push(r.head);
                }
            }
        }
        for i in heads {
            b.tick("completion model validation")?;
            self.heads_queued[i] = false;
            if let Some(v) = c.fixed[i] {
                if v != values[i] {
                    return Err(CheckError::Internal(
                        "invalid incremental completion constant",
                    ));
                }
            } else if !c.input[i] && values[i] != (self.producers[i] != 0) {
                return Err(CheckError::Internal(
                    "incremental interpretation violates original completion",
                ));
            }
        }
        queries::validate_retained(c, values, b)?;
        for (kind, group) in &c.groups {
            b.charge(group.len() + 1, "completion model validation")?;
            let n = group.iter().filter(|i| values[**i]).count();
            if (kind.has_coverage() && n == 0)
                || (kind.has_uniqueness() && n > 1)
                || (*kind == Cardinality::Empty && n != 0)
            {
                return Err(CheckError::Internal(
                    "incremental interpretation violates input restriction",
                ));
            }
        }
        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_probe::completion_query::tests::{prepare, verification};
    use crate::test_support::rewrites::{rel, rule};
    #[test]
    fn successive_assignments_match_full_original_equation_validation() {
        let mut c = denotate_ir::Corpus::new();
        let i = rel(&mut c, "i", true);
        let j = rel(&mut c, "j", true);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, p, &[(i, false)]);
        rule(&mut c, p, &[(j, true)]);
        rule(&mut c, q, &[(p, false), (q, false)]);
        let v = verification(&mut c, None, &[]);
        let e = prepare(&c, v, &crate::Domains::new());
        let mut budget = Budget::new(&e.limits);
        let mut s = Solver::new(&e, &mut budget).unwrap();
        let encoded = s.encode(&e.cone, false).unwrap();
        let index = Index::new(&e.cone, &encoded, s.run.truth, s.run.budget).unwrap();
        let mut state = State::default();
        // Gray order changes one value at a time, including producer additions,
        // removals, head-only changes, and the circular q=true interpretation.
        for step in (0..16).chain((0..16).rev()) {
            let bits = step ^ (step >> 1);
            let pins: Vec<_> = encoded
                .encoding
                .vars
                .iter()
                .take(4)
                .enumerate()
                .map(|(i, l)| if bits & (1 << i) != 0 { *l } else { !*l })
                .collect();
            // Disable the equations, so invalid SAT assignments also exercise
            // the independent validator instead of being filtered by the solver.
            if !s.solve(&[], &pins).unwrap() {
                continue;
            }
            let full = checked_assignment(&e.cone, &encoded.encoding, &s.run.cnf, s.run.budget);
            let delta = state
                .update(&e.cone, &encoded, &index, &s.run.cnf, s.run.budget)
                .map(|v| v.to_vec());
            assert_eq!(delta.is_ok(), full.is_ok(), "assignment {bits}");
            if let (Ok(a), Ok(b)) = (&delta, &full) {
                assert_eq!(a, b);
            }
            if delta.is_err() {
                state = State::default();
            }
        }
    }
}
