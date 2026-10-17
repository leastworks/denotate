//! Deterministic relational lowering, not semantic checking. In particular,
//! negative cycles are retained for the checker, not rejected by the frontend.

use crate::{
    ast::*,
    attribution::{Attribution, AttributionError, SourceView},
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
    Attribution(AttributionError),
}

impl From<AttributionError> for LoweringFailure {
    fn from(error: AttributionError) -> Self {
        Self::Attribution(error)
    }
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
    pub attribution: Attribution,
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
    let library_rules: Vec<_> = corpus.rules().map(|r| r.id).collect();
    let mut lowerer = Lowerer {
        corpus,
        library,
        attribution: Attribution::default(),
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
            lowerer.attach(id, name.span)?;
        }
    }
    for mapping in &program.mappings {
        let head = Head {
            relation: lowerer.library.mapped_to,
            arguments: vec![
                lowerer.constant(&mapping.input, Kind::Input)?.into(),
                lowerer.constant(&mapping.target, Kind::Slot)?.into(),
            ],
            origin: mapping.span,
            argument_origins: vec![mapping.input.span, mapping.target.span],
        };
        let removals = crate::warnings::removals(mapping, sources)?;
        lowerer.define(
            &head,
            mapping.condition.as_ref().map(View::new),
            mapping.span,
            mapping.condition.as_ref().map(|expr| expr.span),
            &removals,
        )?;
    }
    for rule in lowerer.corpus.rules() {
        lowerer.attribution.rewrites.owners.insert(
            rule.id,
            if library_rules.contains(&rule.id) {
                crate::warnings::Contribution::Library
            } else {
                crate::warnings::Contribution::Program
            },
        );
    }
    lowerer.attribution.validate(&lowerer.corpus, sources)?;
    Ok(LoweringOutcome::Lowered(LoweredProgram {
        corpus: lowerer.corpus,
        library: lowerer.library,
        attribution: lowerer.attribution,
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
    /// Outermost authored negation affecting this literal. Child views inherit
    /// it; helper definitions start a fresh context. Also ties a direct safe
    /// removal to the AST node, never to a search through provenance spans.
    normalized_by: Option<&'a Expr>,
}
impl<'a> View<'a> {
    fn new(expr: &'a Expr) -> Self {
        Self {
            expr,
            span: expr.span,
            negative: false,
            normalized_by: None,
        }
    }
    fn peel(mut self) -> Self {
        loop {
            match &self.expr.kind {
                ExprKind::Group(inner) => self.expr = inner,
                ExprKind::Not { operand, .. } => {
                    self.normalized_by.get_or_insert(self.expr);
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
            normalized_by: self.normalized_by,
        }
    }
}

struct Head {
    relation: RelationId,
    arguments: Vec<Term>,
    origin: SourceSpan,
    argument_origins: Vec<SourceSpan>,
}

struct Lowerer<'a> {
    corpus: Corpus,
    library: MappingLibrary,
    attribution: Attribution,
    sources: &'a Sources,
    constants: BTreeMap<(Kind, String), ConstantId>,
    next_helper: usize,
}

impl Lowerer<'_> {
    fn attach(&mut self, id: impl Into<OccurrenceId>, span: SourceSpan) -> Result<()> {
        Ok(self.attribution.provenance.attach(
            &self.corpus,
            self.sources,
            id,
            [Origin::new(span)],
        )?)
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
        guard: Option<SourceSpan>,
        removals: &[(&Expr, crate::warnings::SourceEdit)],
    ) -> Result<()> {
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
            let mut links = Vec::new();
            if let Some(view) = &alternative {
                self.body(view.clone(), &mut body, &mut links, removals)?;
            }
            let atom = self.corpus.atom(head.relation, head.arguments.clone())?;
            links.push((atom.id(), head.origin));
            for (term, origin) in atom.arguments().iter().zip(&head.argument_origins) {
                links.push((term.id(), *origin));
            }
            let id = self.corpus.add_rule(atom, body)?;
            self.attach(id, statement)?;
            if let Some(span) = guard {
                let view =
                    SourceView::try_from(self.sources.snapshot(span.snapshot())?.view.as_str())?;
                self.attribution.guards.insert((id, view), span);
            }
            for (id, origins) in links {
                self.attach(id, origins)?;
            }
        }
        Ok(())
    }

    fn body(
        &mut self,
        view: View<'_>,
        body: &mut Vec<Literal>,
        links: &mut Vec<(OccurrenceId, SourceSpan)>,
        removals: &[(&Expr, crate::warnings::SourceEdit)],
    ) -> Result<()> {
        let view = view.peel();
        match &view.expr.kind {
            ExprKind::And(a, b) if !view.negative => {
                self.body(view.child(a), body, links, removals)?;
                self.body(view.child(b), body, links, removals)?;
            }
            ExprKind::Or(a, b) if view.negative => {
                self.body(view.child(a), body, links, removals)?;
                self.body(view.child(b), body, links, removals)?;
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
                links.push((
                    atom.id(),
                    view.normalized_by.map_or(view.expr.span, |expr| expr.span),
                ));
                links.push((atom.arguments()[0].id(), name.span));
                if view.negative {
                    for (expr, edit) in removals {
                        if view
                            .normalized_by
                            .is_some_and(|origin| std::ptr::eq(origin, *expr))
                        {
                            self.attribution
                                .rewrites
                                .removals
                                .insert(atom.id(), edit.clone());
                        }
                    }
                }
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
                self.attach(relation, view.span)?;
                let helper = Head {
                    relation,
                    arguments: vec![],
                    origin: view.span,
                    argument_origins: vec![],
                };
                self.define(&helper, Some(View::new(view.expr)), view.span, None, &[])?;
                let atom = self.corpus.atom(relation, [])?;
                links.push((
                    atom.id(),
                    view.normalized_by.map_or(view.span, |expr| expr.span),
                ));
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
