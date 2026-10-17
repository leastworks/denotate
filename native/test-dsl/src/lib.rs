//! A small client of Denotate's public IR API. Parsed or hand-built source-spanned ASTs
//! lower to relational rules with replayed checks and source-linked diagnostics.
//! The diagnostics server uses the same lowering and attribution APIs.

pub mod ast;
pub mod attribution;
pub mod library;
pub mod lowering;
pub mod presentation;
pub mod syntax;
pub mod warnings;

// Exercise cached creator failures through the actual snapshot/checker bridge.
#[cfg(test)]
extern crate self as denotate_test_dsl;
#[cfg(test)]
#[path = "server/analysis.rs"]
mod analysis;
