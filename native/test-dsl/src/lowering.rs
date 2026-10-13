//! Deterministic relational lowering, not semantic checking. In particular,
//! negative cycles are retained for the checker, not rejected by the frontend.

use crate::{
    ast::*,
    library::{self, MappingLibrary},
};
use denotate_ir::*;
use std::{collections::BTreeMap, fmt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
    UnknownName {
        name: String,
        expected: Kind,
    },
    WrongKind {
        name: String,
        expected: Kind,
        found: Kind,
    },
    DuplicateDeclaration {
        name: String,
        kind: Kind,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DslDiagnostic {
    pub kind: DiagnosticKind,
    pub span: SourceSpan,
    pub related: Vec<SourceSpan>,
}

#[derive(Debug)]
pub enum LoweringFailure {
    Construction(ConstructionError),
    Provenance(ProvenanceError),
    InvalidAst(String),
}

impl From<ConstructionError> for LoweringFailure {
    fn from(error: ConstructionError) -> Self {
        Self::Construction(error)
    }
}
impl From<ProvenanceError> for LoweringFailure {
    fn from(error: ProvenanceError) -> Self {
        Self::Provenance(error)
    }
}
impl fmt::Display for LoweringFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InputMapping lowering failed: {self:?}")
    }
}
impl std::error::Error for LoweringFailure {}

pub struct LoweredProgram {
    pub corpus: Corpus,
    pub library: MappingLibrary,
    pub provenance: Provenance,
}

pub enum LoweringOutcome {
    Lowered(LoweredProgram),
    UserErrors(Vec<DslDiagnostic>),
}

type Result<T> = std::result::Result<T, LoweringFailure>;
type Names = BTreeMap<(Kind, String), SourceSpan>;

/// All user errors are collected before constructing any IR. Source snapshots
/// stay owned by the caller and must remain available with the returned origins.
pub fn lower(program: &Program, sources: &Sources) -> Result<LoweringOutcome> {
    let mut names = Names::new();
    let mut diagnostics = Vec::new();
    for declaration in &program.declarations {
        sources.text(declaration.span)?;
        for name in &declaration.names {
            validate_name(name, sources)?;
            let key = (declaration.kind, name.text.clone());
            if let Some(previous) = names.get(&key) {
                diagnostics.push(DslDiagnostic {
                    kind: DiagnosticKind::DuplicateDeclaration {
                        name: name.text.clone(),
                        kind: declaration.kind,
                    },
                    span: name.span,
                    related: vec![*previous],
                });
            } else {
                names.insert(key, name.span);
            }
        }
    }
    for mapping in &program.mappings {
        sources.text(mapping.span)?;
        check_name(
            &mapping.target,
            Kind::Slot,
            &names,
            sources,
            &mut diagnostics,
        )?;
        check_name(
            &mapping.input,
            Kind::Input,
            &names,
            sources,
            &mut diagnostics,
        )?;
        if let Some(expr) = &mapping.condition {
            check_expr(expr, &names, sources, &mut diagnostics)?;
        }
    }
    if !diagnostics.is_empty() {
        return Ok(LoweringOutcome::UserErrors(diagnostics));
    }

    let mut corpus = Corpus::new();
    let library = library::build(&mut corpus)?;
    let mut lowerer = Lowerer {
        corpus,
        library,
        provenance: Provenance::new(),
        sources,
        constants: BTreeMap::new(),
        next_helper: 1,
    };
    for declaration in &program.declarations {
        for name in &declaration.names {
            let sort = match declaration.kind {
                Kind::Input => lowerer.library.input,
                Kind::Slot => lowerer.library.slot,
            };
            let id = lowerer.corpus.declare_constant(&name.text, sort)?;
            lowerer
                .constants
                .insert((declaration.kind, name.text.clone()), id);
            lowerer.attach(
                id,
                [
                    Origin::new(declaration.span, "declaration"),
                    Origin::new(name.span, "name"),
                ],
            )?;
        }
    }
    for mapping in &program.mappings {
        let head = Head {
            relation: lowerer.library.mapped_to,
            arguments: vec![
                lowerer.constant(&mapping.input, Kind::Input)?.into(),
                lowerer.constant(&mapping.target, Kind::Slot)?.into(),
            ],
            origins: vec![
                Origin::new(mapping.target.span, "target"),
                Origin::new(mapping.input.span, "input"),
            ],
            argument_origins: vec![
                Origin::new(mapping.input.span, "input"),
                Origin::new(mapping.target.span, "target"),
            ],
        };
        lowerer.define(
            &head,
            mapping.condition.as_ref().map(View::new),
            mapping.span,
            None,
        )?;
    }
    Ok(LoweringOutcome::Lowered(LoweredProgram {
        corpus: lowerer.corpus,
        library: lowerer.library,
        provenance: lowerer.provenance,
    }))
}

fn validate_name(name: &Name, sources: &Sources) -> Result<()> {
    if sources.text(name.span)? != name.text || name.text.is_empty() {
        return Err(LoweringFailure::InvalidAst(
            "name does not match its source span".into(),
        ));
    }
    Ok(())
}

fn check_name(
    name: &Name,
    expected: Kind,
    names: &Names,
    sources: &Sources,
    diagnostics: &mut Vec<DslDiagnostic>,
) -> Result<()> {
    validate_name(name, sources)?;
    if names.contains_key(&(expected, name.text.clone())) {
        return Ok(());
    }
    let other = match expected {
        Kind::Input => Kind::Slot,
        Kind::Slot => Kind::Input,
    };
    let (kind, related) = if let Some(span) = names.get(&(other, name.text.clone())) {
        (
            DiagnosticKind::WrongKind {
                name: name.text.clone(),
                expected,
                found: other,
            },
            vec![*span],
        )
    } else {
        (
            DiagnosticKind::UnknownName {
                name: name.text.clone(),
                expected,
            },
            vec![],
        )
    };
    diagnostics.push(DslDiagnostic {
        kind,
        span: name.span,
        related,
    });
    Ok(())
}

fn check_expr(
    expr: &Expr,
    names: &Names,
    sources: &Sources,
    diagnostics: &mut Vec<DslDiagnostic>,
) -> Result<()> {
    sources.text(expr.span)?;
    match &expr.kind {
        ExprKind::Available(name) => check_name(name, Kind::Slot, names, sources, diagnostics)?,
        ExprKind::Present(name) => check_name(name, Kind::Input, names, sources, diagnostics)?,
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            check_expr(a, names, sources, diagnostics)?;
            check_expr(b, names, sources, diagnostics)?;
        }
        ExprKind::Not { keyword, operand } => {
            if sources.text(*keyword)? != "not" {
                return Err(LoweringFailure::InvalidAst(
                    "not keyword span must contain 'not'".into(),
                ));
            }
            check_expr(operand, names, sources, diagnostics)?;
        }
        ExprKind::Group(inner) => check_expr(inner, names, sources, diagnostics)?,
    }
    Ok(())
}

/// Peeling parentheses/negations retains their original attribution. Polarity
/// is a lowering aid, not a new IR connective or an admissibility decision.
#[derive(Clone)]
struct View<'a> {
    expr: &'a Expr,
    span: SourceSpan,
    negative: bool,
    origins: Vec<Origin>,
}
impl<'a> View<'a> {
    fn new(expr: &'a Expr) -> Self {
        Self {
            expr,
            span: expr.span,
            negative: false,
            origins: vec![],
        }
    }
    fn peel(mut self) -> Self {
        loop {
            match &self.expr.kind {
                ExprKind::Group(inner) => self.expr = inner,
                ExprKind::Not { keyword, operand } => {
                    self.origins.push(Origin::new(*keyword, "not"));
                    self.origins
                        .push(Origin::new(self.expr.span, "negated expression"));
                    self.negative = !self.negative;
                    self.span = operand.span;
                    self.expr = operand;
                }
                _ => return self,
            }
        }
    }
    fn child(&self, expr: &'a Expr) -> Self {
        Self {
            expr,
            span: expr.span,
            negative: self.negative,
            origins: self.origins.clone(),
        }
    }
}

struct Head {
    relation: RelationId,
    arguments: Vec<Term>,
    origins: Vec<Origin>,
    argument_origins: Vec<Origin>,
}

struct Lowerer<'a> {
    corpus: Corpus,
    library: MappingLibrary,
    provenance: Provenance,
    sources: &'a Sources,
    constants: BTreeMap<(Kind, String), ConstantId>,
    next_helper: usize,
}

impl Lowerer<'_> {
    fn attach(
        &mut self,
        id: impl Into<OccurrenceId>,
        origins: impl IntoIterator<Item = Origin>,
    ) -> Result<()> {
        Ok(self
            .provenance
            .attach(&self.corpus, self.sources, id, origins)?)
    }
    fn constant(&self, name: &Name, kind: Kind) -> Result<ConstantId> {
        self.constants
            .get(&(kind, name.text.clone()))
            .copied()
            .ok_or_else(|| {
                LoweringFailure::InvalidAst("validated name missing during lowering".into())
            })
    }

    fn alternatives<'a>(view: View<'a>, result: &mut Vec<View<'a>>) {
        let view = view.peel();
        if let ExprKind::Or(a, b) = &view.expr.kind {
            if !view.negative {
                Self::alternatives(view.child(a), result);
                Self::alternatives(view.child(b), result);
                return;
            }
        }
        result.push(view);
    }

    fn define(
        &mut self,
        head: &Head,
        condition: Option<View<'_>>,
        statement: SourceSpan,
        helper: Option<SourceSpan>,
    ) -> Result<()> {
        let mut alternatives = Vec::new();
        if let Some(view) = condition {
            Self::alternatives(view, &mut alternatives);
        }
        let split = alternatives.len() > 1;
        let alternatives: Vec<_> = if alternatives.is_empty() {
            vec![None]
        } else {
            alternatives.into_iter().map(Some).collect()
        };
        for alternative in alternatives {
            let mut body = Vec::new();
            let mut links = Vec::new();
            if let Some(view) = &alternative {
                self.body(view.clone(), statement, &mut body, &mut links)?;
            }
            let atom = self.corpus.atom(head.relation, head.arguments.clone())?;
            links.push((atom.id(), head.origins.clone()));
            for (term, origin) in atom.arguments().iter().zip(&head.argument_origins) {
                links.push((term.id(), vec![origin.clone()]));
            }
            let id = self.corpus.add_rule(atom, body)?;
            let mut origins = vec![Origin::new(statement, "mapping")];
            if let Some(span) = helper {
                origins.push(Origin::new(span, "subexpression"));
            }
            if let Some(view) = alternative {
                if split {
                    origins.push(Origin::new(view.span, "alternative"));
                }
                origins.extend(view.origins);
            }
            self.attach(id, origins)?;
            for (id, origins) in links {
                self.attach(id, origins)?;
            }
        }
        Ok(())
    }

    fn body(
        &mut self,
        view: View<'_>,
        statement: SourceSpan,
        body: &mut Vec<Literal>,
        links: &mut Vec<(OccurrenceId, Vec<Origin>)>,
    ) -> Result<()> {
        let view = view.peel();
        match &view.expr.kind {
            ExprKind::And(a, b) if !view.negative => {
                self.body(view.child(a), statement, body, links)?;
                self.body(view.child(b), statement, body, links)?;
            }
            ExprKind::Or(a, b) if view.negative => {
                self.body(view.child(a), statement, body, links)?;
                self.body(view.child(b), statement, body, links)?;
            }
            ExprKind::Available(name) | ExprKind::Present(name) => {
                let (relation, kind) = if matches!(view.expr.kind, ExprKind::Available(_)) {
                    (self.library.available, Kind::Slot)
                } else {
                    (self.library.present, Kind::Input)
                };
                let atom = self
                    .corpus
                    .atom(relation, [self.constant(name, kind)?.into()])?;
                let mut origins = vec![Origin::new(view.expr.span, "condition")];
                origins.extend(view.origins);
                links.push((atom.id(), origins));
                links.push((
                    atom.arguments()[0].id(),
                    vec![Origin::new(name.span, "condition argument")],
                ));
                body.push(if view.negative {
                    Literal::Negative(atom)
                } else {
                    Literal::Positive(atom)
                });
            }
            ExprKind::And(..) | ExprKind::Or(..) => {
                // '$' is outside the planned DSL identifier alphabet. No user
                // relations are lowered. Library names avoid this prefix by
                // convention; IR duplicate-name checks catch actual collisions.
                let name = format!("$condition_{}", self.next_helper);
                self.next_helper += 1;
                let relation = self
                    .corpus
                    .declare_relation(name, RelationRole::Derived, [])?;
                let origin = Origin::new(view.span, "subexpression");
                self.attach(relation, [origin.clone()])?;
                let helper = Head {
                    relation,
                    arguments: vec![],
                    origins: vec![origin.clone()],
                    argument_origins: vec![],
                };
                self.define(
                    &helper,
                    Some(View::new(view.expr)),
                    statement,
                    Some(view.span),
                )?;
                let atom = self.corpus.atom(relation, [])?;
                let mut origins = vec![origin];
                origins.extend(view.origins);
                links.push((atom.id(), origins));
                body.push(if view.negative {
                    Literal::Negative(atom)
                } else {
                    Literal::Positive(atom)
                });
            }
            ExprKind::Not { .. } | ExprKind::Group(_) => {
                return Err(LoweringFailure::InvalidAst("unpeeled condition".into()));
            }
        }
        Ok(())
    }
}
