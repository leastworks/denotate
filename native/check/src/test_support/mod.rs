//! Opt-in test probes and independent oracles. No frontend dependency.
pub mod completion;
pub mod rewrites;
pub mod sparse;
pub mod symbolic;
pub use crate::accounting::with_test_schedule;
pub use crate::boolean::with_test_input_order;

pub mod certification;

use crate::*;
use denotate_ir::SemanticKeys;
pub struct TestQueryRun<'a> {
    pub keys: &'a SemanticKeys,
    pub ground: &'a GroundKeyIndex,
    pub receipts: &'a mut WorkReceipts,
}
impl<'p> SymbolicMeaning<'p> {
    pub fn verify_test_queries(
        &self,
        limits: &Limits,
        completion: &Limits,
        certification: &Limits,
        queries: Option<&mut TestQueryRun<'_>>,
    ) -> std::result::Result<Verification<'p>, CheckError> {
        let mut queries = queries.map(|q| crate::accounting::QueryRun {
            keys: q.keys,
            ground: q.ground,
            receipts: q.receipts,
        });
        self.verify_queries(limits, completion, certification, queries.as_mut())
    }
}
pub fn component_rules(
    program: &GroundProgram,
    id: ComponentId,
) -> impl Iterator<Item = &GroundRule> {
    program.component_rules[id.index]
        .iter()
        .map(|i| &program.rules[*i])
}

/// Test-only evaluation of the opaque portable graph against structural inputs.
pub fn owned_condition_value(
    condition: &OwnedCondition,
    present: &std::collections::BTreeSet<AtomKey>,
) -> bool {
    condition.value_in(present).unwrap()
}
