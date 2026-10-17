//! A small client of Denotate's public IR API. Parsed or hand-built source-spanned ASTs
//! lower to relational rules with replayed checks and source-linked diagnostics.
//! Worker-backed editor integration is later.

pub mod ast;
pub mod library;
pub mod lowering;
pub mod presentation;
pub mod syntax;
pub mod warnings;
