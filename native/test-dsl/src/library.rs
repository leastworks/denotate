use denotate_ir::{
    ConstructionError, Corpus, Literal, ObligationId, Parameter, RelationId, RelationRole, SortId,
    Term,
};

pub struct MappingLibrary {
    pub slot: SortId,
    pub input: SortId,
    pub mapped_to: RelationId,
    pub present: RelationId,
    pub supplies: RelationId,
    pub available: RelationId,
    pub unique_input: ObligationId,
}

/// Build semantics, not a solver: no InputMapping-specific type exists in the IR.
pub fn build(corpus: &mut Corpus) -> Result<MappingLibrary, ConstructionError> {
    let slot = corpus.declare_sort("Slot")?;
    let input = corpus.declare_sort("Input")?;
    let mapped_to = corpus.declare_relation(
        "mapped_to",
        RelationRole::Derived,
        [Parameter::new("input", input), Parameter::new("slot", slot)],
    )?;
    let present = corpus.declare_relation(
        "present",
        RelationRole::Input,
        [Parameter::new("input", input)],
    )?;
    let supplies = corpus.declare_relation(
        "supplies",
        RelationRole::Derived,
        [Parameter::new("input", input), Parameter::new("slot", slot)],
    )?;
    let available = corpus.declare_relation(
        "available",
        RelationRole::Derived,
        [Parameter::new("slot", slot)],
    )?;

    let i = Term::variable("I", input);
    let d = Term::variable("D", slot);
    let head = corpus.atom(supplies, [i.clone(), d.clone()])?;
    let mapping = corpus.atom(mapped_to, [i.clone(), d.clone()])?;
    let presence = corpus.atom(present, [i.clone()])?;
    corpus.add_rule(
        head,
        [Literal::Positive(mapping), Literal::Positive(presence)],
    )?;

    let head = corpus.atom(available, [d.clone()])?;
    let supply = corpus.atom(supplies, [i, d])?;
    corpus.add_rule(head, [Literal::Positive(supply)])?;

    let unique_input = corpus.at_most_one(
        "one_input_per_slot",
        supplies,
        ["slot".into()],
        "Slot {slot} has overlapping InputMappings from {inputs}.",
    )?;
    Ok(MappingLibrary {
        slot,
        input,
        mapped_to,
        present,
        supplies,
        available,
        unique_input,
    })
}
