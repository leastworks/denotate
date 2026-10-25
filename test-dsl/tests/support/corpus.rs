//! The InputMapping regression corpus shared by tests across the repository:
//! hand-written programs in `fixtures/corpus.txt` plus generated normalization cases.
#![allow(dead_code)] // Each test uses part of the corpus.

/// Hand-written programs in file order; tests name them `corpus/NN`.
pub fn programs() -> Vec<&'static str> {
    include_str!("../../fixtures/corpus.txt")
        .split("\n---\n")
        .collect()
}

/// Hand-written programs that the frontend rejects with user errors, by index.
pub const REJECTED: [usize; 6] = [14, 15, 16, 32, 33, 34];

/// Hand-written programs that lower without user errors, with their index.
pub fn accepted() -> Vec<(usize, &'static str)> {
    programs()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !REJECTED.contains(i))
        .collect()
}

/// Generated programs with their document revisions; tests name them `generated/NN`.
pub fn generated() -> Vec<(u64, String)> {
    cases::capture_cases()
}

mod cases {
    include!("normalization_cases.rs");
}

/// Every program text, hand-written then generated, for tests that ignore revisions.
pub fn texts() -> Vec<String> {
    programs()
        .into_iter()
        .map(String::from)
        .chain(generated().into_iter().map(|(_, text)| text))
        .collect()
}
