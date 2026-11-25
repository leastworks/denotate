//! Shared projection of an already prepared program into the SAT encoder.
//! Preparation chooses semantics; this module neither folds nor prunes rules.
use super::*;

// Full residual rules with fixed truth as two anonymous constants. Fixed evidence
// stays in GroundProgram; millions of fixed atoms do not get copied into SAT arrays.
pub(super) fn original_cone(
    p: &GroundProgram,
    corpus: &denotate_ir::Corpus,
    verification: denotate_ir::VerificationId,
    b: &mut Budget<'_>,
) -> Result<Cone> {
    original_cone_with_assumptions(p, corpus, verification, true, b)
}
pub(super) fn completion_cone(
    p: &GroundProgram,
    corpus: &denotate_ir::Corpus,
    verification: denotate_ir::VerificationId,
    b: &mut Budget<'_>,
) -> Result<Cone> {
    original_cone_with_assumptions(p, corpus, verification, false, b)
}
fn original_cone_with_assumptions(
    p: &GroundProgram,
    corpus: &denotate_ir::Corpus,
    verification: denotate_ir::VerificationId,
    selected: bool,
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
            ground: Some(r.id),
            source: Some(r.source),
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
    for id in v.assumptions.iter().filter(|_| selected) {
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
        atoms: atoms.into(),
        rules: rules.into(),
        source_rules: p.core.rules.len(),
        retained: vec![].into(),
        input: input.into(),
        fixed,
        groups: groups.into(),
        target: vec![false; n + 2].into(),
        duplicated: vec![false; n + 2].into(),
    })
}
