//! Frozen c840058 recipe normalizer; do not extend for later language features.
#![allow(dead_code)]
//! Pure Boolean normalization to arena-free construction instructions.
//! Statement-local occurrence keys and AST paths carry attribution, never spans.

use denotate_test_dsl::ast::Kind;
use denotate_test_dsl::lowering::semantic::*;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalOccurrence(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantRef {
    pub kind: Kind,
    pub name: String,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationRef {
    MappedTo,
    Masked,
    Present,
    Available,
    Helper(LocalOccurrence),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Argument {
    pub id: LocalOccurrence,
    pub value: ConstantRef,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    pub atom: LocalOccurrence,
    pub negative: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    Constant {
        id: LocalOccurrence,
        value: ConstantRef,
    },
    Helper {
        id: LocalOccurrence,
    },
    Atom {
        id: LocalOccurrence,
        relation: RelationRef,
        arguments: Vec<Argument>,
    },
    Rule {
        id: LocalOccurrence,
        head: LocalOccurrence,
        body: Vec<Literal>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recipe {
    pub(crate) form: Arc<SemanticStatement>,
    pub(crate) instructions: Vec<Instruction>,
    pub(crate) origins: BTreeMap<LocalOccurrence, AstPath>,
    pub(crate) guards: BTreeMap<LocalOccurrence, AstPath>,
    pub(crate) removals: BTreeMap<LocalOccurrence, AstPath>,
    next: usize,
}
impl Recipe {
    /// Names are validated separately. The assembler still checks construction
    /// and source compatibility; this function has no corpus or snapshot access.
    pub fn lower(form: Arc<SemanticStatement>) -> Self {
        let mut recipe = Self {
            form: form.clone(),
            instructions: vec![],
            origins: BTreeMap::new(),
            guards: BTreeMap::new(),
            removals: BTreeMap::new(),
            next: 0,
        };
        match form.as_ref() {
            SemanticStatement::Declaration { kind, names } => {
                for (index, name) in names.iter().enumerate() {
                    let id = recipe.occurrence(AstPath::DeclaredName(index));
                    recipe.instructions.push(Instruction::Constant {
                        id,
                        value: ConstantRef {
                            kind: *kind,
                            name: name.clone(),
                        },
                    });
                }
            }
            SemanticStatement::Mapping {
                target,
                input,
                condition,
            } => {
                let head = Head {
                    relation: RelationRef::MappedTo,
                    arguments: vec![
                        (
                            ConstantRef {
                                kind: Kind::Input,
                                name: input.clone(),
                            },
                            AstPath::Input,
                        ),
                        (
                            ConstantRef {
                                kind: Kind::Slot,
                                name: target.clone(),
                            },
                            AstPath::Target,
                        ),
                    ],
                    origin: AstPath::Statement,
                };
                recipe.define(
                    &head,
                    condition
                        .as_ref()
                        .map(|e| View::new(e, ExprPath::default())),
                    condition.is_some(),
                );
            }
            SemanticStatement::Mask { target, condition } => {
                let head = Head {
                    relation: RelationRef::Masked,
                    arguments: vec![(
                        ConstantRef {
                            kind: Kind::Slot,
                            name: target.clone(),
                        },
                        AstPath::Target,
                    )],
                    origin: AstPath::Statement,
                };
                recipe.define(
                    &head,
                    condition
                        .as_ref()
                        .map(|e| View::new(e, ExprPath::default())),
                    condition.is_some(),
                );
            }
        }
        recipe
    }

    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }
    pub fn origins(&self) -> &BTreeMap<LocalOccurrence, AstPath> {
        &self.origins
    }

    fn occurrence(&mut self, path: AstPath) -> LocalOccurrence {
        let id = LocalOccurrence(self.next);
        self.next += 1;
        self.origins.insert(id, path);
        id
    }
    fn atom(&mut self, head: &Head) -> LocalOccurrence {
        let id = self.occurrence(head.origin.clone());
        let arguments = head
            .arguments
            .iter()
            .map(|(value, path)| Argument {
                id: self.occurrence(path.clone()),
                value: value.clone(),
            })
            .collect();
        self.instructions.push(Instruction::Atom {
            id,
            relation: head.relation,
            arguments,
        });
        id
    }

    fn alternatives<'a>(view: View<'a>, result: &mut Vec<View<'a>>) {
        let view = view.peel();
        if let Expression::Or(a, b) = view.expr {
            if !view.negative {
                Self::alternatives(view.child(a, Step::Left), result);
                Self::alternatives(view.child(b, Step::Right), result);
                return;
            }
        }
        result.push(view);
    }
    fn define(&mut self, head: &Head, condition: Option<View<'_>>, guard: bool) {
        let mut alternatives = Vec::new();
        if let Some(view) = condition {
            Self::alternatives(view, &mut alternatives);
        }
        let alternatives: Vec<_> = if alternatives.is_empty() {
            vec![None]
        } else {
            alternatives.into_iter().map(Some).collect()
        };
        for alternative in alternatives {
            let mut body = Vec::new();
            if let Some(view) = alternative {
                self.body(view, &mut body);
            }
            let head_atom = self.atom(head);
            let id = self.occurrence(head.origin.clone());
            self.instructions.push(Instruction::Rule {
                id,
                head: head_atom,
                body,
            });
            if guard {
                self.guards
                    .insert(id, AstPath::Expression(ExprPath::default()));
            }
        }
    }
    fn body(&mut self, view: View<'_>, body: &mut Vec<Literal>) {
        let view = view.peel();
        match view.expr {
            Expression::And(a, b) if !view.negative => {
                self.body(view.child(a, Step::Left), body);
                self.body(view.child(b, Step::Right), body);
            }
            Expression::Or(a, b) if view.negative => {
                self.body(view.child(a, Step::Left), body);
                self.body(view.child(b, Step::Right), body);
            }
            Expression::Available(name) | Expression::Present(name) => {
                let (relation, kind) = if matches!(view.expr, Expression::Available(_)) {
                    (RelationRef::Available, Kind::Slot)
                } else {
                    (RelationRef::Present, Kind::Input)
                };
                let atom = self.atom(&Head {
                    relation,
                    arguments: vec![(
                        ConstantRef {
                            kind,
                            name: name.clone(),
                        },
                        AstPath::Argument(view.path.clone()),
                    )],
                    origin: AstPath::Expression(view.normalized_by.clone().unwrap_or(view.path)),
                });
                // Eligibility and edit ranges are decided from the current AST,
                // not from this expression's origin or from cached source text.
                if view.negative {
                    if let Some(path) = view.normalized_by {
                        self.removals.insert(atom, AstPath::Expression(path));
                    }
                }
                body.push(Literal {
                    atom,
                    negative: view.negative,
                });
            }
            Expression::And(..) | Expression::Or(..) => {
                let id = self.occurrence(AstPath::Expression(view.origin.clone()));
                self.instructions.push(Instruction::Helper { id });
                let helper = Head {
                    relation: RelationRef::Helper(id),
                    arguments: vec![],
                    origin: AstPath::Expression(view.origin.clone()),
                };
                // Positive helper definitions reset the use's negation context.
                self.define(&helper, Some(View::new(view.expr, view.path)), false);
                let atom = self.atom(&Head {
                    origin: AstPath::Expression(view.normalized_by.unwrap_or(view.origin)),
                    ..helper
                });
                body.push(Literal {
                    atom,
                    negative: view.negative,
                });
            }
            Expression::Not(_) | Expression::Group(_) => unreachable!("peel removes wrappers"),
        }
    }
}

struct Head {
    relation: RelationRef,
    arguments: Vec<(ConstantRef, AstPath)>,
    origin: AstPath,
}

struct View<'a> {
    expr: &'a Expression,
    path: ExprPath,
    origin: ExprPath,
    negative: bool,
    normalized_by: Option<ExprPath>,
}
impl<'a> View<'a> {
    fn new(expr: &'a Expression, path: ExprPath) -> Self {
        Self {
            expr,
            origin: path.clone(),
            path,
            negative: false,
            normalized_by: None,
        }
    }
    fn peel(mut self) -> Self {
        loop {
            match self.expr {
                Expression::Group(inner) => {
                    self.expr = inner;
                    self.path = self.path.child(Step::Inner);
                }
                Expression::Not(operand) => {
                    self.normalized_by.get_or_insert_with(|| self.path.clone());
                    self.negative = !self.negative;
                    self.path = self.path.child(Step::Operand);
                    self.origin = self.path.clone();
                    self.expr = operand;
                }
                _ => return self,
            }
        }
    }
    fn child(&self, expr: &'a Expression, step: Step) -> Self {
        let path = self.path.child(step);
        Self {
            expr,
            origin: path.clone(),
            path,
            negative: self.negative,
            normalized_by: self.normalized_by.clone(),
        }
    }
}
