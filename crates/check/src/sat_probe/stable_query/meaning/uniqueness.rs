use super::*;
use components::{Scope, ScopedModels};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UniquenessStats {
    /// local-proofs, downstream-cone, or whole-program (fallback).
    pub scope: &'static str,
    pub components: Vec<usize>,
    pub atoms: usize,
    pub inputs: usize,
    pub pair_queries: usize,
    pub extension_queries: usize,
    pub fallback_reason: Option<&'static str>,
}

impl Engine {
    pub(super) fn scoped_uniqueness(
        &mut self,
        unique_cones: &BTreeSet<usize>,
    ) -> Result<(Uniqueness, UniquenessStats)> {
        let _progress = self.limits.progress.scope("SAT uniqueness", None, true);
        let limits = self.limits.clone();
        let mut b = Budget::new(&limits);
        let mut stats = UniquenessStats {
            scope: "preparing",
            ..Default::default()
        };
        self.limits.progress.sat_uniqueness(&stats);
        let result = (|| {
            if let Some(e) = &self.append_failed {
                return Err(e.clone());
            }
            b.charge(self.program.core.components.len(), "SAT uniqueness scope")?;
            let mut downstream = vec![false; self.program.core.components.len()];
            for (i, c) in self.program.core.components.iter().enumerate() {
                b.charge(1 + c.dependencies.len(), "SAT uniqueness scope")?;
                // Unclassified cones (including when existence was skipped or
                // stopped early) are candidates, never silently treated as unique.
                downstream[i] = c.cycle.is_some() && !unique_cones.contains(&i)
                    || c.dependencies.iter().any(|d| downstream[d.index]);
                if downstream[i] {
                    stats.components.push(i);
                }
            }
            if stats.components.is_empty() {
                stats.scope = "local-proofs";
                return Ok(Uniqueness::AtMostOne);
            }
            stats.scope = "downstream-cone";
            self.limits.progress.sat_uniqueness(&stats);
            let scope = self.components_scope(stats.components.clone(), &mut b)?;
            stats.atoms = scope.cone.atoms.len();
            stats.inputs = scope.cone.input.iter().filter(|v| **v).count();
            self.limits.progress.sat_uniqueness(&stats);
            self.scoped_pair_uniqueness(&scope, &mut stats, &mut b)
        })();
        self.limits.progress.sat_uniqueness(&stats);
        match result {
            Ok(v) => Ok((v, stats)),
            Err(e) => {
                self.limits.progress.failure(&e);
                Ok((
                    Uniqueness::Inconclusive(query_inconclusive(
                        e.in_phase("SAT uniqueness", None),
                    )?),
                    stats,
                ))
            }
        }
    }

    fn scoped_pair_uniqueness(
        &mut self,
        scope: &Scope,
        stats: &mut UniquenessStats,
        b: &mut Budget<'_>,
    ) -> Result<Uniqueness> {
        stats.pair_queries += 1;
        let Some(pair) = self.scope_pair(scope, b)? else {
            return Ok(Uniqueness::AtMostOne);
        };
        self.extend_scoped_pair(scope, pair, stats, b)
    }

    fn extend_scoped_pair(
        &mut self,
        scope: &Scope,
        pair: ScopedModels,
        stats: &mut UniquenessStats,
        b: &mut Budget<'_>,
    ) -> Result<Uniqueness> {
        let observation = pair.world.observation(b)?;
        b.charge(
            observation.present.len() + observation.absent.len(),
            "SAT uniqueness extension",
        )?;
        let input_pins: Vec<_> = observation
            .present
            .iter()
            .map(|a| (a.clone(), true))
            .chain(observation.absent.iter().map(|a| (a.clone(), false)))
            .collect();
        let mut extended = Vec::new();
        for values in [
            &pair.first,
            pair.second
                .as_ref()
                .ok_or(CheckError::Internal("missing scoped second model"))?,
        ] {
            b.charge(
                input_pins.len() + scope.cone.atoms.len(),
                "SAT uniqueness extension",
            )?;
            let mut pins = input_pins.clone();
            pins.extend(
                scope
                    .cone
                    .atoms
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !scope.cone.input[*i])
                    .map(|(i, a)| (a.clone(), values[i])),
            );
            stats.extension_queries += 1;
            self.limits.progress.sat_uniqueness(stats);
            match self.phase_query(
                Mode::Program,
                &Query {
                    pins,
                    exclude: vec![],
                },
                b,
            )? {
                Answer::Model(m) => extended.push(m), // full reduct validation
                answer => {
                    stats.fallback_reason = Some(match answer {
                        Answer::NoModel => "scoped pair has no whole-program extension",
                        _ => "scoped pair extension was inconclusive",
                    });
                    stats.scope = "whole-program";
                    stats.pair_queries += 1;
                    self.limits.progress.sat_uniqueness(stats);
                    // No fresh phase allowance: extension and fallback retain
                    // ordinary per-query caps and share remaining work/deadline.
                    return self.whole_uniqueness(b);
                }
            }
        }
        let second = extended.pop().unwrap();
        let first = extended.pop().unwrap();
        Ok(Uniqueness::Multiple {
            observation,
            first,
            second,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{atom, rel, rule};

    #[test]
    fn a_pair_without_full_extensions_falls_back_and_never_becomes_global_ambiguity() {
        let mut c = Corpus::new();
        let a = rel(&mut c, "a", false);
        let z = rel(&mut c, "b", false);
        let bad = rel(&mut c, "bad", false);
        rule(&mut c, a, &[(z, true)]);
        rule(&mut c, z, &[(a, true)]);
        rule(&mut c, bad, &[(bad, true)]);
        let v = c
            .verification_in(denotate_ir::Namespace::default(), "v", [], [])
            .unwrap();
        let limits = Limits::default();
        let mut e = Engine::prepare(
            &c,
            &Domains::new(),
            &SemanticKeys::default(),
            v,
            &limits,
            QueryLimits::default(),
        )
        .unwrap();
        let root = e.program.core.atom_components[e.program.core.atom_index[&atom(a)]].index;
        let mut b = Budget::new(&limits);
        // Exercise the extension boundary directly. The production classifier
        // conservatively includes bad's unproved cone rather than omitting it.
        let scope = e.components_scope(vec![root], &mut b).unwrap();
        let pair = e.scope_pair(&scope, &mut b).unwrap().unwrap();
        let mut stats = UniquenessStats {
            scope: "downstream-cone",
            ..Default::default()
        };
        let timeout = e.cnf.solver.cb().timeout;
        assert!(matches!(
            e.extend_scoped_pair(&scope, pair, &mut stats, &mut b)
                .unwrap(),
            Uniqueness::AtMostOne
        ));
        assert_eq!(e.cnf.solver.cb().timeout, timeout);
        assert_eq!(stats.scope, "whole-program");
        assert_eq!(
            stats.fallback_reason,
            Some("scoped pair has no whole-program extension")
        );
        assert!(matches!(
            e.models(&Query::default()).unwrap(),
            Answer::NoModel
        ));
        assert!(matches!(
            e.worlds(&Query::default()).unwrap(),
            Answer::Model(_)
        ));
    }
}
