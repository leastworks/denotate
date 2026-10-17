//! InputMapping's source contract. Generic provenance remains many-to-many;
//! this lowerer does not fuse authored constructs, so each occurrence has at
//! most one distinct origin in each view. Presentation labels are not origins.

use crate::warnings::RewriteMetadata;
use denotate_ir::*;
use std::{collections::BTreeMap, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceView {
    TestDsl,
    Denotate,
}

impl SourceView {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::TestDsl => "test-dsl",
            Self::Denotate => "denotate",
        }
    }
}

impl TryFrom<&str> for SourceView {
    type Error = AttributionError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "test-dsl" => Ok(Self::TestDsl),
            "denotate" => Ok(Self::Denotate),
            other => Err(AttributionError::UnknownView(other.into())),
        }
    }
}

#[derive(Debug)]
pub enum AttributionError {
    Provenance(ProvenanceError),
    UnknownView(String),
    MultipleOrigins {
        occurrence: OccurrenceId,
        view: SourceView,
    },
    InvalidMetadata(&'static str),
}

impl From<ProvenanceError> for AttributionError {
    fn from(error: ProvenanceError) -> Self {
        Self::Provenance(error)
    }
}
impl fmt::Display for AttributionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Creator-facing attribution failure: {self:?}")
    }
}
impl std::error::Error for AttributionError {}

/// One source-dependent bundle to refresh when a source snapshot changes.
#[derive(Debug, Default)]
pub struct Attribution {
    pub provenance: Provenance,
    /// Complete authored guards for quoting, not split-alternative metadata.
    pub guards: BTreeMap<(RuleId, SourceView), SourceSpan>,
    pub rewrites: RewriteMetadata,
    /// Authored masks (including their helper rules), for mask-cycle locations
    /// and unconditional coverage warnings. This is DSL metadata, not IR roles.
    pub masks: BTreeMap<RuleId, MaskAttribution>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskAttribution {
    pub target: ConstantId,
    pub statement: SourceSpan,
    pub condition: Option<SourceSpan>,
}

impl Attribution {
    /// Validate all entries, even those no diagnostic would inspect. This is
    /// also the entry point for directly constructed or augmented fixtures.
    pub fn validate(&self, corpus: &Corpus, sources: &Sources) -> Result<(), AttributionError> {
        for (id, origins) in self.provenance.entries() {
            if !corpus.contains_occurrence(id) {
                return Err(ProvenanceError::UnknownOccurrence(id).into());
            }
            let mut seen = BTreeMap::new();
            for origin in origins {
                sources.text(origin.span)?;
                let view =
                    SourceView::try_from(sources.snapshot(origin.span.snapshot())?.view.as_str())?;
                if let Some(previous) = seen.insert(view, origin.span) {
                    if previous != origin.span {
                        return Err(AttributionError::MultipleOrigins {
                            occurrence: id,
                            view,
                        });
                    }
                }
            }
        }
        for ((rule, view), span) in &self.guards {
            if corpus.rule(*rule).is_none() {
                return Err(AttributionError::InvalidMetadata(
                    "guard belongs to another corpus",
                ));
            }
            sources.text(*span)?;
            let actual = SourceView::try_from(sources.snapshot(span.snapshot())?.view.as_str())?;
            if actual != *view {
                return Err(AttributionError::InvalidMetadata(
                    "guard has the wrong source view",
                ));
            }
        }
        for rule in self.rewrites.owners.keys() {
            if corpus.rule(*rule).is_none() {
                return Err(AttributionError::InvalidMetadata(
                    "rewrite owner belongs to another corpus",
                ));
            }
        }
        for (rule, mask) in &self.masks {
            if corpus.rule(*rule).is_none() || corpus.constant(mask.target).is_none() {
                return Err(AttributionError::InvalidMetadata(
                    "mask belongs to another corpus",
                ));
            }
            sources.text(mask.statement)?;
            for span in std::iter::once(mask.statement).chain(mask.condition) {
                sources.text(span)?;
                if SourceView::try_from(sources.snapshot(span.snapshot())?.view.as_str())?
                    != SourceView::TestDsl
                    || span.snapshot() != mask.statement.snapshot()
                    || span.byte_range().start < mask.statement.byte_range().start
                    || span.byte_range().end > mask.statement.byte_range().end
                {
                    return Err(AttributionError::InvalidMetadata(
                        "mask attribution is outside its DSL statement",
                    ));
                }
            }
        }
        for (occurrence, edit) in &self.rewrites.removals {
            if !corpus.contains_occurrence(*occurrence) {
                return Err(ProvenanceError::UnknownOccurrence(*occurrence).into());
            }
            sources.text(edit.span)?;
            SourceView::try_from(sources.snapshot(edit.span.snapshot())?.view.as_str())?;
        }
        Ok(())
    }

    pub fn origin(
        &self,
        id: impl Into<OccurrenceId>,
        sources: &Sources,
        view: SourceView,
    ) -> Result<Option<SourceSpan>, AttributionError> {
        let id = id.into();
        let mut result = None;
        for origin in self.provenance.origins(id) {
            let actual =
                SourceView::try_from(sources.snapshot(origin.span.snapshot())?.view.as_str())?;
            sources.text(origin.span)?;
            if actual == view {
                if result.is_some_and(|previous| previous != origin.span) {
                    return Err(AttributionError::MultipleOrigins {
                        occurrence: id,
                        view,
                    });
                }
                result = Some(origin.span);
            }
        }
        Ok(result)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedLocation {
    pub span: SourceSpan,
    pub label: String,
}
impl RelatedLocation {
    pub fn new(span: SourceSpan, label: impl Into<String>) -> Self {
        Self {
            span,
            label: label.into(),
        }
    }
}
