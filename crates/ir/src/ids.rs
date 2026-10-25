use std::sync::atomic::{AtomicU64, Ordering};

// Private arena stamps keep handles from unrelated builders from aliasing.
// Handles are process-local, not serialized IDs or incremental editor identities.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub(crate) struct Arena(u64);

impl Arena {
    pub(crate) fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct OccurrenceId {
    pub(crate) arena: Arena,
    pub(crate) index: usize,
}

macro_rules! declaration_id {
    ($($name:ident),*) => {$(
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
        pub struct $name(pub(crate) OccurrenceId);

        impl From<$name> for OccurrenceId {
            fn from(id: $name) -> Self { id.0 }
        }
    )*};
}

declaration_id!(
    SortId,
    ConstantId,
    RelationId,
    RuleId,
    ObligationId,
    AssumptionId,
    VerificationId
);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct SnapshotId {
    pub(crate) arena: Arena,
    pub(crate) index: usize,
}
