//! Ground InputMapping syntax. Spans refer to immutable UTF-8 source snapshots.
//! Parsing is separate; there is no name resolution or IR identity in this AST.

use denotate_ir::SourceSpan;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    Input,
    Slot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub text: String,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub kind: Kind,
    pub names: Vec<Name>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mapping {
    pub target: Name,
    pub input: Name,
    pub condition: Option<Expr>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mask {
    pub target: Name,
    pub condition: Option<Expr>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Available(Name),
    Present(Name),
    Value {
        kind: Kind,
        name: Name,
        literal: Name,
    },
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not {
        keyword: SourceSpan,
        operand: Box<Expr>,
    },
    Group(Box<Expr>),
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Declaration>,
    pub mappings: Vec<Mapping>,
    pub masks: Vec<Mask>,
}
