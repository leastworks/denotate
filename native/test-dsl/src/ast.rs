//! Ground InputMapping syntax. Spans refer to immutable UTF-8 source snapshots.
//! There is deliberately no parser, name resolution or IR identity in this AST.

use denotate_ir::SourceSpan;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Input,
    Slot,
}

#[derive(Debug, Clone)]
pub struct Name {
    pub text: String,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub kind: Kind,
    pub names: Vec<Name>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct Mapping {
    pub target: Name,
    pub input: Name,
    pub condition: Option<Expr>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Available(Name),
    Present(Name),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not {
        keyword: SourceSpan,
        operand: Box<Expr>,
    },
    Group(Box<Expr>),
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub declarations: Vec<Declaration>,
    pub mappings: Vec<Mapping>,
}
