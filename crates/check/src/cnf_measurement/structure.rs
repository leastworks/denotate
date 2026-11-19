//! Original residual SCCs, before experimental rewrites or CNF elimination.
use super::*;
#[derive(Debug, Default)]
pub struct RecursiveSizes {
    pub components: usize,
    pub atoms: usize,
    pub rules: usize,
    pub largest_atoms: usize,
    pub largest_rules: usize,
    pub above_100_atoms: usize,
    /// Exact atom count -> number of components of that size.
    pub histogram: BTreeMap<usize, usize>,
}
#[derive(Debug)]
pub struct RecursiveComponent {
    /// Ordinal in this original residual graph, not a persistent identity.
    pub index: usize,
    pub negative: bool,
    pub atoms: usize,
    pub rules: usize,
    pub relations: BTreeMap<RelationId, usize>,
}
#[derive(Debug, Default)]
pub struct RecursiveReport {
    pub positive: RecursiveSizes,
    pub negative: RecursiveSizes,
    pub components: Vec<RecursiveComponent>,
}
impl Measurement {
    pub fn recursive_components(&self, limits: &Limits) -> Result<RecursiveReport> {
        let mut b = Budget::new(limits);
        let mut report = RecursiveReport::default();
        for (i, c) in self.program.core.components.iter().enumerate() {
            b.tick("CNF component report")?;
            if !c.recursive {
                continue;
            }
            let negative = c.cycle.is_some();
            let rules = self.program.component_rules[c.id.index].len();
            let size = if negative {
                &mut report.negative
            } else {
                &mut report.positive
            };
            size.components += 1;
            size.atoms += c.atoms.len();
            size.rules += rules;
            size.largest_atoms = size.largest_atoms.max(c.atoms.len());
            size.largest_rules = size.largest_rules.max(rules);
            size.above_100_atoms += usize::from(c.atoms.len() > 100);
            *size.histogram.entry(c.atoms.len()).or_default() += 1;
            let mut relations = BTreeMap::new();
            for a in &c.atoms {
                b.tick("CNF component report")?;
                *relations.entry(a.relation).or_default() += 1;
            }
            report.components.push(RecursiveComponent {
                index: i,
                negative,
                atoms: c.atoms.len(),
                rules,
                relations,
            });
        }
        Ok(report)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::rewrites::{rel, rule};
    #[test]
    fn histogram_counts_components_above_one_hundred_atoms() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "input", true);
        let ring: Vec<_> = (0..101)
            .map(|i| rel(&mut c, &format!("r{i}"), false))
            .collect();
        for i in 0..ring.len() {
            rule(&mut c, ring[i], &[(ring[(i + 1) % ring.len()], false)]);
        }
        rule(&mut c, ring[0], &[(x, false)]);
        let l = Limits::default();
        let m = Measurement::prepare(&c, &Domains::new(), &l).unwrap();
        let r = m.recursive_components(&l).unwrap();
        assert_eq!(r.positive.histogram, BTreeMap::from([(101, 1)]));
        assert_eq!(r.positive.above_100_atoms, 1);
        assert_eq!(r.positive.largest_atoms, 101);
        assert_eq!(r.positive.largest_rules, 102);
        assert_eq!(r.negative.components, 0);
    }
    #[test]
    fn recursive_report_separates_self_loops_and_signed_components() {
        let mut c = Corpus::new();
        let x = rel(&mut c, "x", true);
        let a = rel(&mut c, "a", false);
        let p = rel(&mut c, "p", false);
        let q = rel(&mut c, "q", false);
        rule(&mut c, a, &[(x, false), (a, false)]);
        rule(&mut c, a, &[(x, false)]);
        rule(&mut c, p, &[(x, false), (q, true)]);
        rule(&mut c, q, &[(p, true)]);
        let limits = Limits::default();
        let m = Measurement::prepare(&c, &Domains::new(), &limits).unwrap();
        let report = m.recursive_components(&limits).unwrap();
        assert_eq!(
            (
                report.positive.components,
                report.positive.atoms,
                report.positive.rules
            ),
            (1, 1, 2)
        );
        assert_eq!(
            (
                report.negative.components,
                report.negative.atoms,
                report.negative.rules
            ),
            (1, 2, 2)
        );
        assert_eq!(report.negative.histogram, BTreeMap::from([(2, 1)]));
        assert_eq!(report.negative.above_100_atoms, 0);
        let v = m.simplify_comparison(&Default::default(), &limits).unwrap();
        for v in v {
            for pass in v.passes {
                assert_eq!(
                    pass.unsupported,
                    report.positive.atoms + report.negative.atoms
                );
            }
        }
    }
}
