use crate::{Corpus, OccurrenceId, SnapshotId, ids::Arena};
use std::{collections::BTreeMap, fmt, ops::Range, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceError {
    EmptyDocumentIdentity,
    SnapshotConflict {
        uri: String,
        revision: u64,
    },
    UnknownSnapshot(SnapshotId),
    InvalidUtf8Range {
        snapshot: SnapshotId,
        start: usize,
        end: usize,
    },
    UnknownOccurrence(OccurrenceId),
}

impl fmt::Display for ProvenanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Invalid source attribution: {self:?}")
    }
}
impl std::error::Error for ProvenanceError {}

type Result<T> = std::result::Result<T, ProvenanceError>;

#[derive(Debug)]
pub struct SourceSnapshot {
    pub id: SnapshotId,
    pub uri: String,
    /// Caller-assigned immutable revision. A revised document gets a new snapshot.
    pub revision: u64,
    /// Frontend-defined view name, e.g. "test-dsl" or "denotate".
    pub view: String,
    pub text: Arc<str>,
}

/// A half-open UTF-8 byte range, NOT UTF-16 LSP columns. The editor adapter
/// converts using this snapshot, never the current text of a different revision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceSpan {
    snapshot: SnapshotId,
    start: usize,
    end: usize,
}

impl SourceSpan {
    pub fn snapshot(self) -> SnapshotId {
        self.snapshot
    }
    pub fn byte_range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Immutable source snapshots, separate from the corpus and its semantic IDs.
#[derive(Debug)]
pub struct Sources {
    arena: Arena,
    snapshots: Vec<SourceSnapshot>,
}

impl Default for Sources {
    fn default() -> Self {
        Self {
            arena: Arena::new(),
            snapshots: Vec::new(),
        }
    }
}

impl Sources {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(
        &mut self,
        uri: impl Into<String>,
        revision: u64,
        view: impl Into<String>,
        text: impl Into<Arc<str>>,
    ) -> Result<SnapshotId> {
        let uri = uri.into();
        let view = view.into();
        let text = text.into();
        if uri.is_empty() || view.is_empty() {
            return Err(ProvenanceError::EmptyDocumentIdentity);
        }
        if let Some(previous) = self
            .snapshots
            .iter()
            .find(|s| s.uri == uri && s.revision == revision)
        {
            return if previous.text == text && previous.view == view {
                Ok(previous.id)
            } else {
                Err(ProvenanceError::SnapshotConflict { uri, revision })
            };
        }
        let id = SnapshotId {
            arena: self.arena,
            index: self.snapshots.len(),
        };
        self.snapshots.push(SourceSnapshot {
            id,
            uri,
            revision,
            view,
            text,
        });
        Ok(id)
    }

    pub fn snapshot(&self, id: SnapshotId) -> Result<&SourceSnapshot> {
        if id.arena != self.arena {
            return Err(ProvenanceError::UnknownSnapshot(id));
        }
        self.snapshots
            .get(id.index)
            .ok_or(ProvenanceError::UnknownSnapshot(id))
    }

    pub fn span(&self, snapshot: SnapshotId, bytes: Range<usize>) -> Result<SourceSpan> {
        let source = self.snapshot(snapshot)?;
        if source.text.get(bytes.clone()).is_none() {
            return Err(ProvenanceError::InvalidUtf8Range {
                snapshot,
                start: bytes.start,
                end: bytes.end,
            });
        }
        Ok(SourceSpan {
            snapshot,
            start: bytes.start,
            end: bytes.end,
        })
    }

    pub fn text(&self, span: SourceSpan) -> Result<&str> {
        self.snapshot(span.snapshot)?
            .text
            .get(span.byte_range())
            .ok_or(ProvenanceError::InvalidUtf8Range {
                snapshot: span.snapshot,
                start: span.start,
                end: span.end,
            })
    }
}

/// A source occurrence and its frontend-defined role ("target", "condition",
/// "library", etc.). Roles describe attribution, not relational semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin {
    pub span: SourceSpan,
    pub role: String,
}

impl Origin {
    pub fn new(span: SourceSpan, role: impl Into<String>) -> Self {
        Self {
            span,
            role: role.into(),
        }
    }
}

/// Many-to-many lowering attribution. Not a derivation proof or an error message.
/// Attach after committing occurrences to a corpus. Updates only add origins;
/// another source revision/view gets another attribution table if needed.
#[derive(Debug, Default)]
pub struct Provenance {
    links: BTreeMap<OccurrenceId, Vec<Origin>>,
}

impl Provenance {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn attach(
        &mut self,
        corpus: &Corpus,
        sources: &Sources,
        occurrence: impl Into<OccurrenceId>,
        origins: impl IntoIterator<Item = Origin>,
    ) -> Result<()> {
        let occurrence = occurrence.into();
        if !corpus.contains_occurrence(occurrence) {
            return Err(ProvenanceError::UnknownOccurrence(occurrence));
        }
        let origins: Vec<_> = origins.into_iter().collect();
        // Validate the complete addition before changing the table.
        for origin in &origins {
            sources.text(origin.span)?;
        }
        let existing = self.links.entry(occurrence).or_default();
        for origin in origins {
            if !existing.contains(&origin) {
                existing.push(origin);
            }
        }
        Ok(())
    }

    pub fn origins(&self, occurrence: impl Into<OccurrenceId>) -> &[Origin] {
        self.links
            .get(&occurrence.into())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// A split copies origins to each output; a merge takes the union. The
    /// caller chooses corresponding occurrences, not just their enclosing rules.
    pub fn inherit(
        &mut self,
        corpus: &Corpus,
        sources: &Sources,
        target: impl Into<OccurrenceId>,
        inputs: &[OccurrenceId],
    ) -> Result<()> {
        let mut origins = Vec::new();
        for input in inputs {
            if !corpus.contains_occurrence(*input) {
                return Err(ProvenanceError::UnknownOccurrence(*input));
            }
            origins.extend_from_slice(self.origins(*input));
        }
        self.attach(corpus, sources, target, origins)
    }

    pub fn in_view<'a>(
        &'a self,
        occurrence: impl Into<OccurrenceId>,
        sources: &Sources,
        view: &str,
    ) -> Result<Vec<&'a Origin>> {
        let mut result = Vec::new();
        for origin in self.origins(occurrence) {
            if sources.snapshot(origin.span.snapshot)?.view == view {
                result.push(origin);
            }
        }
        Ok(result)
    }

    pub fn occurrences_at(&self, span: SourceSpan) -> Vec<OccurrenceId> {
        self.links
            .iter()
            .filter(|(_, origins)| origins.iter().any(|origin| origin.span == span))
            .map(|(occurrence, _)| *occurrence)
            .collect()
    }
}
