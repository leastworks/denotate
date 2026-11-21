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
