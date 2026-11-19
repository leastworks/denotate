//! A bounded paired experiment, not a new simplification policy. Both calls see
//! exactly the same original snapshot; sequential rewriting cannot explain a delta.
use super::*;
#[derive(Debug)]
pub struct ProofObservation {
    pub shape: ProofShape,
    pub work: usize,
    pub answer: &'static str,
    pub cutoff: Option<CheckError>,
}
#[derive(Debug)]
pub struct LocalDifference {
    pub question: &'static str,
    pub head: GroundAtom,
    pub body: Vec<(GroundAtom, bool)>,
    pub premise: Option<(GroundAtom, bool)>,
    pub base: ProofObservation,
    pub comparison: ProofObservation,
}
fn observe(
    m: &Model,
    q: Question<'_>,
    local: &SimplificationLimits,
    b: &mut Budget<'_>,
) -> Result<ProofObservation> {
    let mut limits = b.limits.clone();
    limits.max_work = limits.max_work.min(local.max_proof_work).min(b.remaining());
    let globally_bounded = b.remaining() <= local.max_proof_work;
    let mut proof = Budget::new(&limits);
    let mut shape = ProofShape::default();
    let result = local::prove_observed(m, q, local, &mut proof, &mut shape);
    let work = limits.max_work.saturating_sub(proof.remaining());
    b.charge(work, "CNF paired local proofs")?;
    b.check("CNF paired local proofs")?;
    let (answer, cutoff) = match result {
        Ok(Answer::Yes) => ("proved", None),
        Ok(Answer::Constant(true)) => ("constant-true", None),
        Ok(Answer::Constant(false)) => ("constant-false", None),
        Ok(Answer::No) => ("unchanged", None),
        Err(CheckError::LimitExceeded {
            resource: "work", ..
        }) if globally_bounded => return Err(b.work_exhaustion("CNF paired local proofs")),
        Err(e @ CheckError::LimitExceeded { .. }) => ("cut-off", Some(e)),
        Err(e) => return Err(e),
    };
    Ok(ProofObservation {
        shape,
        work,
        answer,
        cutoff,
    })
}
impl Measurement {
    /// First proof lost under `comparison`, in original acyclic-head order.
    /// This diagnoses a same-snapshot resource effect, not aggregate differences
    /// between two sequentially rewritten programs. None means no such loss found.
    pub fn first_local_difference(
        &self,
        base: &SimplificationLimits,
        comparison: &SimplificationLimits,
        limits: &Limits,
    ) -> Result<Option<LocalDifference>> {
        let mut b = Budget::new(limits);
        let m = Model::new(&self.program, &mut b)?;
        for h in &m.order {
            if !m.eligible(*h) {
                continue;
            }
            let defs = m.definitions(*h, &mut b)?;
            let mut questions = vec![Question::Constant(*h)];
            for body in &defs {
                questions.push(Question::Dead(body));
                for l in body {
                    questions.push(Question::Implied(body, *l));
                }
            }
            for q in questions {
                let first = observe(&m, q, base, &mut b)?;
                if matches!(first.answer, "unchanged" | "cut-off") {
                    continue;
                }
                let second = observe(&m, q, comparison, &mut b)?;
                if first.answer == second.answer {
                    continue;
                }
                let lit = |l: i32| (m.atoms[atom(l)].clone(), l > 0);
                let (question, body, premise) = match q {
                    Question::Constant(_) => ("constant", Vec::new(), None),
                    Question::Dead(body) => {
                        ("dead-rule", body.iter().copied().map(lit).collect(), None)
                    }
                    Question::Implied(body, p) => (
                        "implied-premise",
                        body.iter().copied().map(lit).collect(),
                        Some(lit(p)),
                    ),
                };
                return Ok(Some(LocalDifference {
                    question,
                    head: m.atoms[*h].clone(),
                    body,
                    premise,
                    base: first,
                    comparison: second,
                }));
            }
        }
        Ok(None)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{rel, rule};
    #[test]
    fn larger_cone_can_lose_a_proof_by_expanding_an_irrelevant_provider() {
        // eq is costly under grouped x/y variable order. With a small cone it
        // is a free cut point. The implied x premise does not depend on eq.
        let mut c = Corpus::new();
        let xs: Vec<_> = (0..80)
            .map(|i| rel(&mut c, &format!("x{i}"), true))
            .collect();
        let ys: Vec<_> = (0..80)
            .map(|i| rel(&mut c, &format!("y{i}"), true))
            .collect();
        let eqs: Vec<_> = (0..80)
            .map(|i| rel(&mut c, &format!("eq{i}"), false))
            .collect();
        for i in 0..80 {
            rule(&mut c, eqs[i], &[(xs[i], false), (ys[i], false)]);
            rule(&mut c, eqs[i], &[(xs[i], true), (ys[i], true)]);
        }
        let eq = rel(&mut c, "eq", false);
        rule(
            &mut c,
            eq,
            &eqs.iter().map(|r| (*r, false)).collect::<Vec<_>>(),
        );
        let gate = rel(&mut c, "gate", false);
        rule(&mut c, gate, &[(xs[0], false)]);
        let out = rel(&mut c, "out", false);
        rule(&mut c, out, &[(eq, false), (gate, false), (xs[0], false)]);
        let limits = Limits {
            max_work: 20_000_000,
            ..Limits::default()
        };
        let m = Measurement::prepare(&c, &Domains::new(), &limits).unwrap();
        let big = SimplificationLimits {
            max_cone_atoms: 256,
            max_bdd_nodes: 65536,
            max_proof_work: 100000,
        };
        let d = m
            .first_local_difference(&Default::default(), &big, &limits)
            .unwrap()
            .expect("a larger cone loses the guard implication");
        assert_eq!(d.question, "implied-premise");
        assert_eq!(d.head.relation, out);
        assert_eq!(d.base.answer, "proved");
        assert_eq!(d.comparison.answer, "cut-off");
        assert!(d.comparison.shape.definitions > d.base.shape.definitions);
        assert!(d.comparison.cutoff.is_some());
    }
}
