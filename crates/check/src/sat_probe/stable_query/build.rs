use super::*;
use denotate_ir::{AssumptionCone, Corpus, SemanticKeys, VerificationId};

pub(super) fn prepare<'a>(
    corpus: &'a Corpus,
    domains: &Domains,
    keys: &'a SemanticKeys,
    verification: VerificationId,
    limits: &Limits,
) -> Result<(
    GroundProgram,
    Arc<crate::settled::SettledView>,
    WorkReceipts,
)> {
    let declaration = corpus
        .verification(verification)
        .ok_or(CheckError::InvalidRequest("unknown SAT verification"))?;
    let selected = declaration
        .assumptions
        .iter()
        .map(|a| corpus.assumption(*a).unwrap().restriction.relation())
        .collect::<Vec<_>>();
    let mut b = Budget::tracked(limits);
    let classification = corpus
        .validate_assumption_relations_with(selected, || b.tick("SAT assumption validation"))?;
    let fixed = FixedPreparation::prepare(corpus, domains, limits)?;
    let mut receipts = WorkReceipts::default();
    receipts
        .record(crate::QueryKey::FixedFacts, fixed.receipt.clone())
        .map_err(CheckError::Receipts)?;
    if classification
        .values()
        .any(|v| *v == AssumptionCone::NeedsGrounding)
    {
        let validation = fixed.assumption_preparation(keys, limits)?;
        for (r, kind) in &classification {
            if *kind == AssumptionCone::NeedsGrounding {
                validation.check(*r, keys, &mut b)?;
            }
        }
        if let Some((base, _)) = validation.programs() {
            for (key, receipt) in [
                (
                    crate::QueryKey::ResidualPreparation,
                    validation.residual_receipt.as_ref().unwrap(),
                ),
                (
                    crate::QueryKey::SettledAtoms,
                    validation.settled_receipt.as_ref().unwrap(),
                ),
                (crate::QueryKey::AssumptionValidation, &validation.receipt),
            ] {
                receipts
                    .record(key, receipt.clone())
                    .map_err(CheckError::Receipts)?;
            }
            return Ok((
                base.clone(),
                validation.settled().unwrap().clone(),
                receipts,
            ));
        }
    }
    let base = GroundProgram::prepare_using_fixed(
        corpus,
        domains,
        &[],
        &BTreeSet::new(),
        &mut b,
        None,
        Some(&fixed),
    )?;
    b.record(
        &mut receipts,
        crate::QueryKey::ResidualPreparation,
        [crate::QueryKey::FixedFacts],
    )?;
    let (view, receipt) = base.settle_atoms_accounted(Some(keys), limits);
    receipts
        .record(crate::QueryKey::SettledAtoms, receipt)
        .map_err(CheckError::Receipts)?;
    Ok((base, Arc::new(view?), receipts))
}

// Full residual rules with fixed truth as two anonymous constants. Fixed evidence
// stays in GroundProgram; millions of fixed atoms do not get copied into SAT arrays.
pub(super) fn cone(
    p: &GroundProgram,
    corpus: &denotate_ir::Corpus,
    verification: denotate_ir::VerificationId,
    b: &mut Budget<'_>,
) -> Result<Cone> {
    let n = p.core.atoms.len();
    if n >= i32::MAX as usize - 1 {
        return Err(CheckError::InvalidRequest("SAT original program too large"));
    }
    let atoms = p.core.atoms.clone();
    b.charge(n, "SAT original program")?;
    let index = &p.core.atom_index;
    let resolve = |a: &GroundAtom| {
        if let Some(v) = p.fixed_value(a) {
            if v { n } else { n + 1 }
        } else {
            index.get(a).copied().unwrap_or(n + 1)
        }
    };
    let mut rules = Vec::new();
    for r in &p.core.rules {
        b.charge(r.body.len() + 1, "SAT original rules")?;
        let mut body = r
            .body
            .iter()
            .map(|l| (resolve(&l.term.atom), l.polarity == Polarity::Positive))
            .collect::<Vec<_>>();
        body.sort_unstable();
        body.dedup();
        rules.push(Rule {
            head: index[&r.head.atom],
            body,
        });
    }
    let mut groups = Vec::new();
    let mut members = 0usize;
    for g in &p.universe_groups {
        b.room(
            groups.len(),
            b.limits.max_atoms,
            "SAT assumption groups",
            "groups",
        )?;
        let mut atoms = Vec::new();
        for a in &g.atoms {
            b.room(
                members,
                b.limits.max_dependencies,
                "SAT assumption groups",
                "members",
            )?;
            b.tick("SAT assumption groups")?;
            members += 1;
            atoms.push(resolve(a));
        }
        groups.push((g.kind, atoms));
    }
    let v = corpus.verification(verification).unwrap();
    for id in &v.assumptions {
        let r = &corpus.assumption(*id).unwrap().restriction;
        let mut grouped = BTreeMap::<Vec<ConstantId>, Vec<usize>>::new();
        if r.kind().has_coverage() {
            let signature = &p.signatures[&r.relation()];
            let domains = r
                .group_by()
                .iter()
                .map(|col| &p.domains[&signature[*col]])
                .collect::<Vec<_>>();
            if !domains.iter().any(|d| d.is_empty()) {
                let mut positions = vec![0; domains.len()];
                loop {
                    b.tick("SAT assumption groups")?;
                    b.room(
                        groups.len() + grouped.len(),
                        b.limits.max_atoms,
                        "SAT assumption groups",
                        "groups",
                    )?;
                    grouped.insert(
                        positions
                            .iter()
                            .enumerate()
                            .map(|(i, j)| domains[i][*j])
                            .collect(),
                        Vec::new(),
                    );
                    let mut i = positions.len();
                    loop {
                        if i == 0 {
                            break;
                        }
                        i -= 1;
                        positions[i] += 1;
                        if positions[i] < domains[i].len() {
                            break;
                        }
                        positions[i] = 0;
                    }
                    if positions.iter().all(|i| *i == 0) {
                        break;
                    }
                }
            }
        }
        for atom in p.atoms() {
            b.tick("SAT assumption tuples")?;
            if atom.relation == r.relation() {
                let key: Vec<_> = r.group_by().iter().map(|i| atom.arguments[*i]).collect();
                if !grouped.contains_key(&key) {
                    b.room(
                        groups.len() + grouped.len(),
                        b.limits.max_atoms,
                        "SAT assumption groups",
                        "groups",
                    )?;
                }
                b.room(
                    members,
                    b.limits.max_dependencies,
                    "SAT assumption groups",
                    "members",
                )?;
                members += 1;
                grouped.entry(key).or_default().push(resolve(atom));
            }
        }
        for g in grouped.into_values() {
            b.room(
                groups.len(),
                b.limits.max_atoms,
                "SAT assumption groups",
                "groups",
            )?;
            groups.push((r.kind(), g));
        }
    }
    let mut input = atoms
        .iter()
        .map(|a| p.inputs.contains(a))
        .collect::<Vec<_>>();
    input.extend([false, false]);
    let mut fixed = vec![None; n];
    fixed.extend([Some(true), Some(false)]);
    Ok(Cone {
        atoms,
        rules,
        source_rules: p.core.rules.len(),
        input,
        fixed,
        groups,
        target: vec![false; n + 2],
        duplicated: vec![false; n + 2],
    })
}
