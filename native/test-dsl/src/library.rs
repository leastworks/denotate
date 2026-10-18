use denotate_ir::{
    ConstantId, ConstructionError, Corpus, Literal, ObligationId, Parameter, RelationId,
    RelationRole, SortId, Term,
};

pub struct MappingLibrary {
    pub slot: SortId,
    pub input: SortId,
    pub mapped_to: RelationId,
    pub present: RelationId,
    pub supplies: RelationId,
    pub available: RelationId,
    pub masked: RelationId,
    pub unique_input: ObligationId,
    pub integer: SortId,
    pub value: RelationId,
    pub slot_value: RelationId,
    pub other: ConstantId,
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
        RelationRole::Derived,
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
    let masked = corpus.declare_relation(
        "masked",
        RelationRole::Derived,
        [Parameter::new("slot", slot)],
    )?;

    let integer = corpus.declare_sort("IntegerCase")?;
    let other = corpus.declare_constant("other_integer", integer)?;
    let value = corpus.declare_relation(
        "value",
        RelationRole::Input,
        [
            Parameter::new("input", input),
            Parameter::new("value", integer),
        ],
    )?;
    let slot_value = corpus.declare_relation(
        "slot_value",
        RelationRole::Derived,
        [
            Parameter::new("slot", slot),
            Parameter::new("value", integer),
        ],
    )?;

    let i = Term::variable("I", input);
    let d = Term::variable("D", slot);
    let head = corpus.atom(supplies, [i.clone(), d.clone()])?;
    let mapping = corpus.atom(mapped_to, [i.clone(), d.clone()])?;
    let presence = corpus.atom(present, [i.clone()])?;
    let mask = corpus.atom(masked, [d.clone()])?;
    corpus.add_rule(
        head,
        [
            Literal::Positive(mapping),
            Literal::Positive(presence),
            Literal::Negative(mask),
        ],
    )?;

    let head = corpus.atom(available, [d.clone()])?;
    let supply = corpus.atom(supplies, [i, d])?;
    corpus.add_rule(head, [Literal::Positive(supply)])?;

    let i = Term::variable("I", input);
    let d = Term::variable("D", slot);
    let v = Term::variable("V", integer);
    let head = corpus.atom(present, [i.clone()])?;
    let body = corpus.atom(value, [i.clone(), v.clone()])?;
    corpus.add_rule(head, [Literal::Positive(body)])?;
    let head = corpus.atom(slot_value, [d.clone(), v.clone()])?;
    let supply = corpus.atom(supplies, [i.clone(), d])?;
    let input_value = corpus.atom(value, [i, v])?;
    corpus.add_rule(
        head,
        [Literal::Positive(supply), Literal::Positive(input_value)],
    )?;

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
        masked,
        unique_input,
        integer,
        value,
        slot_value,
        other,
    })
}
