//! Classical double-negation cancellation, then Lloyd–Topor with linear helpers.
//! Arena-free recipes and transformation facts. No Corpus, Salsa, source spans,
//! origin selection, or claim of preserving nested stable-model negation.
use std::{
    collections::{BTreeMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

pub trait Value: Clone + Eq + Hash + Debug {}
impl<T: Clone + Eq + Hash + Debug> Value for T {}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Argument<K> {
    pub key: K,
    /// Any variable occurrence, not just variables shared with the outer rule.
    pub variable: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Atom<P, K> {
    pub key: K,
    pub payload: P,
    pub arguments: Vec<Argument<K>>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Expression<L, K> {
    pub key: K,
    pub kind: ExpressionKind<L, K>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExpressionKind<L, K> {
    Leaf {
        payload: L,
        arguments: Vec<Argument<K>>,
    },
    And(Box<Expression<L, K>>, Box<Expression<L, K>>),
    Or(Box<Expression<L, K>>, Box<Expression<L, K>>),
    Not(Box<Expression<L, K>>),
    /// A transparent authored node; retained for attribution policy consumers.
    Group(Box<Expression<L, K>>),
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Definition<H, L, K> {
    pub head: Atom<H, K>,
    /// None denotes an unconditional definition.
    pub body: Option<Expression<L, K>>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Local(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Polarity {
    Positive,
    Negative,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutputKind {
    Helper,
    Rule,
    Head,
    Literal,
    Argument,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HelperRole {
    Neither,
    Definition(Local),
    Use(Local),
}
/// Facts only: consumers choose origins, guard context and edit eligibility.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Record<K> {
    pub node: K,
    /// Entry into this expression before peeling transparent groups/negations.
    /// After a `not`, this is its operand; unlike `node`, it may be a group.
    pub entry: K,
    pub argument: Option<K>,
    pub negations: Vec<K>,
    /// Arguments inherit their containing literal's polarity; heads/rules have None.
    pub polarity: Option<Polarity>,
    pub kind: OutputKind,
    pub helper: HelperRole,
    /// The original definition's head key, including inside helper definitions.
    pub root: K,
    /// Selected child keys at each OR split, outermost first.
    pub alternatives: Vec<K>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Target<H, L> {
    Head(H),
    Leaf(L),
    Helper(Local),
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OutputArgument {
    pub id: Local,
    pub variable: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Literal {
    pub atom: Local,
    pub polarity: Polarity,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Instruction<H, L> {
    Helper {
        id: Local,
    },
    Atom {
        id: Local,
        target: Target<H, L>,
        arguments: Vec<OutputArgument>,
    },
    Rule {
        id: Local,
        head: Local,
        body: Vec<Literal>,
    },
}
/// Only normalization constructs recipes; callers cannot corrupt transfer invariants.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Recipe<H, L, K> {
    instructions: Vec<Instruction<H, L>>,
    records: BTreeMap<Local, Vec<Record<K>>>,
}
impl<H, L, K> Recipe<H, L, K> {
    pub fn instructions(&self) -> &[Instruction<H, L>] {
        &self.instructions
    }
    pub fn records(&self) -> &BTreeMap<Local, Vec<Record<K>>> {
        &self.records
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructionError<K> {
    DuplicateInputKey(K),
    HelperCapturesVariables { expression: K },
}
impl<K: Debug> std::fmt::Display for ConstructionError<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid Boolean construction: {self:?}")
    }
}
impl<K: Debug> std::error::Error for ConstructionError<K> {}

type Result<T, K> = std::result::Result<T, ConstructionError<K>>;

/// All head, expression and argument keys must be unique within the definition.
/// Normalization does not bind variables. Installation must still check rule safety.
pub fn normalize<H: Value, L: Value, K: Value>(
    definition: &Definition<H, L, K>,
) -> Result<Recipe<H, L, K>, K> {
    fn insert<K: Value>(keys: &mut HashSet<K>, key: &K) -> Result<(), K> {
        if !keys.insert(key.clone()) {
            return Err(ConstructionError::DuplicateInputKey(key.clone()));
        }
        Ok(())
    }
    fn validate<L: Value, K: Value>(
        expr: &Expression<L, K>,
        keys: &mut HashSet<K>,
    ) -> Result<(), K> {
        insert(keys, &expr.key)?;
        match &expr.kind {
            ExpressionKind::Leaf { arguments, .. } => {
                for arg in arguments {
                    insert(keys, &arg.key)?;
                }
            }
            ExpressionKind::And(a, b) | ExpressionKind::Or(a, b) => {
                validate(a, keys)?;
                validate(b, keys)?;
            }
            ExpressionKind::Not(a) | ExpressionKind::Group(a) => validate(a, keys)?,
        }
        Ok(())
    }
    let mut keys = HashSet::new();
    insert(&mut keys, &definition.head.key)?;
    for arg in &definition.head.arguments {
        insert(&mut keys, &arg.key)?;
    }
    if let Some(body) = &definition.body {
        validate(body, &mut keys)?;
    }
    let mut builder = Builder {
        recipe: Recipe {
            instructions: vec![],
            records: BTreeMap::new(),
        },
    };
    let record = Record {
        node: definition.head.key.clone(),
        entry: definition.head.key.clone(),
        argument: None,
        negations: vec![],
        polarity: None,
        kind: OutputKind::Head,
        helper: HelperRole::Neither,
        root: definition.head.key.clone(),
        alternatives: vec![],
    };
    builder.define(
        Target::Head(definition.head.payload.clone()),
        &definition.head.arguments,
        record,
        definition.body.as_ref().map(View::new),
    )?;
    Ok(builder.recipe)
}

#[derive(Clone)]
struct View<'a, L, K> {
    expr: &'a Expression<L, K>,
    entry: K,
    negations: Vec<K>,
    negative: bool,
    alternatives: Vec<K>,
}
impl<'a, L: Value, K: Value> View<'a, L, K> {
    fn new(expr: &'a Expression<L, K>) -> Self {
        Self {
            expr,
            entry: expr.key.clone(),
            negations: vec![],
            negative: false,
            alternatives: vec![],
        }
    }
    fn peel(mut self) -> Self {
        loop {
            match &self.expr.kind {
                ExpressionKind::Group(inner) => self.expr = inner,
                ExpressionKind::Not(inner) => {
                    self.negations.push(self.expr.key.clone());
                    self.negative = !self.negative;
                    self.entry = inner.key.clone();
                    self.expr = inner;
                }
                _ => return self,
            }
        }
    }
    fn child(&self, expr: &'a Expression<L, K>) -> Self {
        Self {
            expr,
            entry: expr.key.clone(),
            ..self.clone()
        }
    }
    fn polarity(&self) -> Polarity {
        if self.negative {
            Polarity::Negative
        } else {
            Polarity::Positive
        }
    }
}
struct Builder<H, L, K> {
    recipe: Recipe<H, L, K>,
}
impl<H: Value, L: Value, K: Value> Builder<H, L, K> {
    fn occurrence(&mut self, record: Record<K>) -> Local {
        let id = Local(self.recipe.records.len());
        self.recipe.records.insert(id, vec![record]);
        id
    }
    fn atom(
        &mut self,
        target: Target<H, L>,
        arguments: &[Argument<K>],
        record: Record<K>,
    ) -> Local {
        let id = self.occurrence(record.clone());
        let arguments = arguments
            .iter()
            .map(|a| OutputArgument {
                id: self.occurrence(Record {
                    kind: OutputKind::Argument,
                    argument: Some(a.key.clone()),
                    ..record.clone()
                }),
                variable: a.variable,
            })
            .collect();
        self.recipe.instructions.push(Instruction::Atom {
            id,
            target,
            arguments,
        });
        id
    }
    fn alternatives<'a>(view: View<'a, L, K>, out: &mut Vec<View<'a, L, K>>) {
        let view = view.peel();
        if let ExpressionKind::Or(a, b) = &view.expr.kind {
            if !view.negative {
                for expr in [a, b] {
                    let mut child = view.child(expr);
                    child.alternatives.push(expr.key.clone());
                    Self::alternatives(child, out);
                }
                return;
            }
        }
        out.push(view);
    }
    fn define(
        &mut self,
        target: Target<H, L>,
        arguments: &[Argument<K>],
        record: Record<K>,
        body: Option<View<'_, L, K>>,
    ) -> Result<(), K> {
        let mut alternatives = vec![];
        if let Some(view) = body {
            Self::alternatives(view, &mut alternatives);
        }
        let alternatives = if alternatives.is_empty() {
            vec![None]
        } else {
            alternatives.into_iter().map(Some).collect()
        };
        for alternative in alternatives {
            let mut body = vec![];
            let mut head_record = record.clone();
            if let Some(view) = alternative {
                head_record.alternatives = view.alternatives.clone();
                self.body(view, &record, &mut body)?;
            }
            let head = self.atom(target.clone(), arguments, head_record.clone());
            let id = self.occurrence(Record {
                kind: OutputKind::Rule,
                ..head_record
            });
            self.recipe
                .instructions
                .push(Instruction::Rule { id, head, body });
        }
        Ok(())
    }
    fn body(
        &mut self,
        view: View<'_, L, K>,
        parent: &Record<K>,
        out: &mut Vec<Literal>,
    ) -> Result<(), K> {
        let view = view.peel();
        let record = Record {
            node: view.expr.key.clone(),
            entry: view.entry.clone(),
            argument: None,
            negations: view.negations.clone(),
            polarity: Some(view.polarity()),
            kind: OutputKind::Literal,
            helper: parent.helper,
            root: parent.root.clone(),
            alternatives: view.alternatives.clone(),
        };
        match &view.expr.kind {
            ExpressionKind::And(a, b) if !view.negative => {
                self.body(view.child(a), parent, out)?;
                self.body(view.child(b), parent, out)?;
            }
            ExpressionKind::Or(a, b) if view.negative => {
                self.body(view.child(a), parent, out)?;
                self.body(view.child(b), parent, out)?;
            }
            ExpressionKind::Leaf { payload, arguments } => {
                let atom = self.atom(Target::Leaf(payload.clone()), arguments, record);
                out.push(Literal {
                    atom,
                    polarity: view.polarity(),
                });
            }
            ExpressionKind::And(..) | ExpressionKind::Or(..) => {
                fn variables<L, K>(expr: &Expression<L, K>) -> bool {
                    match &expr.kind {
                        ExpressionKind::Leaf { arguments, .. } => {
                            arguments.iter().any(|a| a.variable)
                        }
                        ExpressionKind::And(a, b) | ExpressionKind::Or(a, b) => {
                            variables(a) || variables(b)
                        }
                        ExpressionKind::Not(a) | ExpressionKind::Group(a) => variables(a),
                    }
                }
                if variables(view.expr) {
                    return Err(ConstructionError::HelperCapturesVariables {
                        expression: view.expr.key.clone(),
                    });
                }
                let helper = Local(self.recipe.records.len());
                self.occurrence(Record {
                    kind: OutputKind::Helper,
                    polarity: None,
                    helper: HelperRole::Definition(helper),
                    negations: vec![],
                    ..record.clone()
                });
                self.recipe
                    .instructions
                    .push(Instruction::Helper { id: helper });
                let definition = Record {
                    kind: OutputKind::Head,
                    polarity: None,
                    helper: HelperRole::Definition(helper),
                    negations: vec![],
                    ..record.clone()
                };
                let mut defining_view = View::new(view.expr);
                defining_view.alternatives = view.alternatives.clone();
                self.define(Target::Helper(helper), &[], definition, Some(defining_view))?;
                let atom = self.atom(
                    Target::Helper(helper),
                    &[],
                    Record {
                        helper: HelperRole::Use(helper),
                        ..record
                    },
                );
                out.push(Literal {
                    atom,
                    polarity: view.polarity(),
                });
            }
            ExpressionKind::Not(_) | ExpressionKind::Group(_) => {
                unreachable!("peel removes wrappers")
            }
        }
        Ok(())
    }
}
