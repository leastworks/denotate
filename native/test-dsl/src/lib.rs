//! A small client of Denotate's public IR API. Hand-built, source-spanned ASTs
//! lower to relational rules; parsing, checking and editor integration are later.

pub mod ast;
pub mod library;
pub mod lowering;
