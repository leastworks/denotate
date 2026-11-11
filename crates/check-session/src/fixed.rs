//! One source-independent fixed-cone query per session, bounded by checker limits.
//! There is no separate byte allowance for this single replaceable result. Replacing the
//! projection drops the old value; failures are explicitly cleared from Salsa.
use denotate_check::*;
use salsa::Setter;
use std::sync::{Arc, Mutex};

#[salsa::input]
struct Slot {
    #[returns(ref)]
    input: Option<Arc<FixedInput>>,
}
#[salsa::db]
trait Db: salsa::Database {
    fn operations(&self) -> OperationalLimits;
}
#[salsa::db]
#[derive(Clone)]
struct Database {
    storage: salsa::Storage<Self>,
    operations: Arc<Mutex<OperationalLimits>>,
}
impl Default for Database {
    fn default() -> Self {
        Self {
            storage: Default::default(),
            operations: Arc::new(Mutex::new((&Limits::default()).into())),
        }
    }
}
#[salsa::db]
impl salsa::Database for Database {}
#[salsa::db]
impl Db for Database {
    fn operations(&self) -> OperationalLimits {
        self.operations.lock().unwrap().clone()
    }
}
#[salsa::tracked]
fn fold(db: &dyn Db, slot: Slot) -> Result<Option<Arc<FixedValue>>, CheckError> {
    slot.input(db)
        .as_ref()
        .map(|input| fold_owned(input, &db.operations()).map(Arc::new))
        .transpose()
}

#[derive(Debug, Default, Clone, Copy)]
pub struct FixedStats {
    pub executed: usize,
    pub reused: usize,
    /// Direct preparations because session retention is disabled, never size bypasses.
    pub bypassed: usize,
    /// Accounted input/output payload and slot overhead, not measured heap or RSS.
    pub retained_bytes: usize,
}
#[derive(Default)]
pub(crate) struct FixedCache {
    db: Database,
    slot: Option<Slot>,
    pub stats: FixedStats,
}
impl FixedCache {
    pub fn bypass(&mut self) {
        self.clear();
        self.stats.bypassed += 1;
        self.stats.executed += 1;
    }
    pub fn clear(&mut self) {
        if let Some(slot) = self.slot {
            slot.set_input(&mut self.db).to(None);
            let _ = fold(&self.db, slot);
        }
        self.stats.retained_bytes = 0;
    }
}
impl FixedStore for FixedCache {
    fn fold(
        &mut self,
        input: FixedInput,
        operations: &OperationalLimits,
    ) -> Result<Arc<FixedValue>, CheckError> {
        operations.cancellation.check()?;
        *self.db.operations.lock().unwrap() = operations.clone();
        let slot = *self.slot.get_or_insert_with(|| Slot::new(&self.db, None));
        if slot.input(&self.db).as_deref() == Some(&input) {
            self.stats.reused += 1;
        } else {
            self.stats.executed += 1;
            slot.set_input(&mut self.db).to(Some(Arc::new(input)));
        }
        let result = fold(&self.db, slot)
            .clone()
            .and_then(|v| v.ok_or(CheckError::Internal("missing fixed value")));
        let result = result.and_then(|value| {
            operations.cancellation.check()?;
            Ok(value)
        });
        match &result {
            Ok(value) => {
                // On a hit, count the retained input's allocation sharing, not
                // the equal projection just supplied by the current snapshot.
                self.stats.retained_bytes = crate::retention::bytes(slot.input(&self.db))
                    .saturating_add(2048)
                    .saturating_add(crate::retention::bytes(value));
            }
            Err(_) => self.clear(),
        }
        result
    }
}
