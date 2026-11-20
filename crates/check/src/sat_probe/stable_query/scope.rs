//! Program scope is fixed at preparation; selectors and caches never cross it.
use super::*;

#[derive(Debug, Clone, Default)]
pub enum PreparationScope {
    #[default]
    WholeProgram,
    ObligationCones,
    /// Reusable upstream-closed scope for consumers with explicit outputs.
    Roots(Vec<GroundAtom>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeSummary {
    pub label: &'static str,
    /// Original ground cone, including fixed evidence. Zero for whole-program scope
    /// (no extra inventory pass on the default path).
    pub atoms: usize,
    pub rule_instances: usize,
    pub outside_analysed: bool,
}
// Selected relation roots include legal tuples absent from the ground inventory.
// They have no producers/dependencies, but are still inside the query scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Members {
    atoms: BTreeSet<GroundAtom>,
    root_relations: BTreeSet<RelationId>,
}
impl Members {
    pub(super) fn contains(&self, atom: &GroundAtom) -> bool {
        self.root_relations.contains(&atom.relation) || self.atoms.contains(atom)
    }
}
impl Engine {
    pub(super) fn resolve_scoped(&self, atom: &GroundAtom) -> Result<Resolved> {
        if !self.input_relations.contains(&atom.relation)
            && self.scope_atoms.as_ref().is_some_and(|s| !s.contains(atom))
        {
            return Err(CheckError::InvalidRequest("atom outside SAT program scope"));
        }
        resolve(&self.program, atom)
    }
    pub fn scope(&self) -> &ScopeSummary {
        &self.scope
    }
    pub(super) fn validate_meaning_scope(&self, mode: MeaningMode) -> Result<()> {
        if mode == MeaningMode::Cone && self.scope.label != "obligation-cones" {
            return Err(CheckError::InvalidRequest(
                "cone meaning requires obligation-cone preparation",
            ));
        }
        Ok(())
    }
}

pub(super) fn restrict(
    scope: PreparationScope,
    original: &GroundProgram,
    program: &mut GroundProgram,
    cone: &mut Cone,
    origins: &[GroundRuleId],
    corpus: &Corpus,
    verification: VerificationId,
    b: &mut Budget<'_>,
) -> Result<(
    ScopeSummary,
    Option<Arc<Members>>,
    Option<Vec<GroundRuleId>>,
)> {
    let (label, roots, root_relations) = match scope {
        PreparationScope::WholeProgram => {
            return Ok((
                ScopeSummary {
                    label: "whole-program",
                    atoms: 0,
                    rule_instances: 0,
                    outside_analysed: true,
                },
                None,
                None,
            ));
        }
        PreparationScope::ObligationCones => {
            let relations: BTreeSet<_> = corpus
                .verification(verification)
                .unwrap()
                .obligations
                .iter()
                .map(|id| corpus.obligation(*id).unwrap().requirement.relation())
                .collect();
            let mut roots = Vec::new();
            for a in original.atoms() {
                b.tick("SAT scope roots")?;
                if relations.contains(&a.relation) {
                    roots.push(a.clone());
                }
            }
            ("obligation-cones", roots, relations)
        }
        PreparationScope::Roots(roots) => ("root-cones", roots, BTreeSet::new()),
    };
    let selected = original.dependency_cone_with_budget(roots, b)?;
    let summary = ScopeSummary {
        label,
        atoms: selected.facts.len(),
        rule_instances: selected.rules.len(),
        outside_analysed: false,
    };
    let members = Arc::new(Members {
        atoms: selected.facts,
        root_relations,
    });
    let mut kept = Vec::new();
    let mut kept_origins = Vec::new();
    let mut sat_rules = Vec::new();
    for (i, rule) in program.core.rules.iter().enumerate() {
        b.tick("SAT scope rules")?;
        if members.contains(&rule.head.atom) {
            let mut rule = rule.clone();
            rule.id.index = kept.len();
            kept.push(rule);
            kept_origins.push(origins[i]);
            sat_rules.push(cone.rules[i].clone());
        }
    }
    program.rules = kept;
    crate::graph::analyze(program, b)?;
    cone.rules = sat_rules;
    cone.source_rules = cone.rules.len();
    // W owns every restriction. Derived restrictions outside C have independent
    // equations there; imposing them on C's omitted atoms would change meaning.
    cone.groups.clear();
    Ok((summary, Some(members), Some(kept_origins)))
}
