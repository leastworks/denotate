//! Test-only orchestration of the same preparation stages, with counters enabled.
use super::*;

impl GroundProgram {
    pub(crate) fn profile_preparation(
        corpus: &Corpus,
        domains: &Domains,
        constraints: &[InputAtMostOne],
        limits: &Limits,
    ) -> Result<(Self, crate::limits::PreparationProfile)> {
        limits.cancellation.check()?;
        let mut budget = Budget::new(limits);
        budget.enable_profile();
        let domains = validate_domains(corpus, domains, &mut budget)?;
        let mut p = Self::empty(corpus, domains);
        budget.mark("domains_and_allocation");
        sparse::populate(corpus, &mut p, &mut budget)?;
        p.build_groups(corpus, &mut budget)?;
        budget.mark("obligation_groups");
        p.build_input_groups(corpus, constraints, &mut budget)?;
        budget.mark("input_groups");
        graph::analyze(&mut p, &mut budget)?;
        budget.mark("graph_and_scc");
        limits.cancellation.check()?;
        Ok((p, budget.profile.unwrap()))
    }
}
