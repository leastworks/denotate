//! A small client of Denotate's public IR API. Parsed or hand-built source-spanned ASTs
//! lower to relational rules with replayed checks and source-linked diagnostics.
//! The diagnostics server uses the same lowering and attribution APIs.

pub mod analysis;
pub mod ast;
pub mod attribution;
pub mod library;
pub mod lowering;
pub mod presentation;
pub mod syntax;
pub mod warnings;

pub mod export;

/// The production LSP entry point, also driven in memory by editor parity tests.
pub mod server;

// Shared test fixtures are also compiled as standalone integration-test crates.
#[cfg(test)]
extern crate self as denotate_test_dsl;
