use crate::*;
use std::time::Duration;

#[test]
fn charge_counters_reject_overflow_without_wrapping() {
    use crate::limits::Budget;
    let limits = Limits {
        max_work: usize::MAX,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let mut budget = Budget::tracked(&limits);
    budget.charge(usize::MAX, "boundary").unwrap();
    assert!(matches!(
        budget.charge(1, "boundary"),
        Err(CheckError::LimitExceeded {
            resource: "work",
            ..
        })
    ));
    let mut receipts = WorkReceipts::default();
    budget
        .record(&mut receipts, QueryKey::Preparation, [])
        .unwrap();
    let own = &receipts.get(&QueryKey::Preparation).unwrap().own;
    assert_eq!(own.work, usize::MAX);
    assert_eq!(own.by_phase["boundary"], usize::MAX);
    assert_eq!(own.rejected_work["boundary"], 1);

    let limits = Limits {
        max_work: 0,
        ..limits
    };
    let mut budget = Budget::tracked(&limits);
    assert!(matches!(
        budget.charge(usize::MAX, "boundary"),
        Err(CheckError::LimitExceeded { .. })
    ));
    assert!(matches!(
        budget.charge(1, "boundary"),
        Err(CheckError::Receipts(ReceiptError::Overflow))
    ));
    assert_eq!(budget.used(), 0);
}
