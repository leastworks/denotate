//! Content identities, character coordinates and caller-owned origin resolution.
use denotate_ir::*;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceIdentity {
    pub uri: String,
    pub view: String,
    pub hash: String,
}
impl SourceIdentity {
    pub fn of(snapshot: &SourceSnapshot) -> Self {
        Self {
            uri: snapshot.uri.clone(),
            view: snapshot.view.clone(),
            hash: content_hash(&snapshot.text),
        }
    }
}
pub fn content_hash(text: &str) -> String {
    format!("sha256:{:x}", Sha256::digest(text.as_bytes()))
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Coordinate {
    pub line: usize,
    pub column: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OriginDescriptor {
    pub source: SourceIdentity,
    pub start: Coordinate,
    pub end: Coordinate,
}
/// Coordinates count Unicode scalar values; LF alone advances the line.
pub fn coordinate(text: &str, byte: usize) -> Option<Coordinate> {
    let prefix = text.get(..byte)?;
    let mut position = Coordinate { line: 1, column: 1 };
    for c in prefix.chars() {
        if c == '\n' {
            position.line += 1;
            position.column = 1;
        } else {
            position.column += 1;
        }
    }
    Some(position)
}
pub fn byte_offset(text: &str, target: Coordinate) -> Option<usize> {
    let mut position = Coordinate { line: 1, column: 1 };
    for (byte, c) in text.char_indices() {
        if position == target {
            return Some(byte);
        }
        if c == '\n' {
            position.line += 1;
            position.column = 1;
        } else {
            position.column += 1;
        }
    }
    (position == target).then_some(text.len())
}

/// Convert a batch with one forward scan, including within a very long line.
/// Only requested, valid boundaries are retained; memory does not scale with the
/// source's character count. Single-coordinate callers can use `byte_offset`.
pub(crate) fn byte_offsets(
    text: &str,
    targets: impl IntoIterator<Item = Coordinate>,
) -> BTreeMap<Coordinate, usize> {
    let mut offsets = BTreeMap::new();
    let mut chars = text.char_indices();
    let mut position = Coordinate { line: 1, column: 1 };
    let mut byte = 0;
    for target in targets.into_iter().collect::<BTreeSet<_>>() {
        while position < target {
            let Some((at, c)) = chars.next() else { break };
            byte = at + c.len_utf8();
            if c == '\n' {
                position.line += 1;
                position.column = 1;
            } else {
                position.column += 1;
            }
        }
        if position == target {
            offsets.insert(target, byte);
        }
    }
    offsets
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batched_coordinates_match_scalar_lookup_including_invalid_boundaries() {
        for text in [
            "",
            "\u{feff}é😀e\u{301}\r\nend\n",
            "a\rb",
            "\n\n",
            "first\nlast",
        ] {
            let targets = (0..=5)
                .flat_map(|line| (0..=12).map(move |column| Coordinate { line, column }))
                .rev()
                .collect::<Vec<_>>();
            let offsets = byte_offsets(text, targets.clone());
            for target in targets {
                assert_eq!(
                    offsets.get(&target).copied(),
                    byte_offset(text, target),
                    "{text:?}: {target:?}"
                );
            }
        }
    }

    #[test]
    fn batch_handles_long_lines_overlapping_ranges_repeated_endpoints_and_eof() {
        let text = format!("\u{feff}{}", "é😀e\u{301}\r".repeat(1000));
        let mut targets = (1..=5002)
            .step_by(47)
            .map(|column| Coordinate { line: 1, column })
            .collect::<Vec<_>>();
        targets.extend([
            Coordinate {
                line: 1,
                column: 5002,
            }, // EOF, with no final newline.
            Coordinate {
                line: 1,
                column: 5003,
            },
            Coordinate { line: 2, column: 1 },
        ]);
        let mut repeated = targets.clone();
        repeated.extend(targets.iter().rev());
        let offsets = byte_offsets(&text, repeated);
        for target in targets {
            assert_eq!(offsets.get(&target).copied(), byte_offset(&text, target));
        }
    }
}
impl OriginDescriptor {
    pub fn of(sources: &Sources, origin: &Origin) -> Result<Self, ProvenanceError> {
        let snapshot = sources.snapshot(origin.span.snapshot())?;
        sources.text(origin.span)?;
        let range = origin.span.byte_range();
        Ok(Self {
            source: SourceIdentity::of(snapshot),
            start: coordinate(&snapshot.text, range.start).unwrap(),
            end: coordinate(&snapshot.text, range.end).unwrap(),
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unavailable {
    Missing,
    Inaccessible(String),
    HashMismatch,
    NoResolver,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OriginNotice {
    pub source: SourceIdentity,
    pub reason: Unavailable,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OriginTarget {
    Occurrence(OccurrenceId),
}
/// Descriptor associations are retained even when a source cannot be resolved.
#[derive(Debug, Default)]
pub struct EmbeddedOrigins {
    pub associations: BTreeMap<OriginTarget, Vec<OriginDescriptor>>,
    pub notices: Vec<OriginNotice>,
    pub provenance: Provenance,
}
impl crate::LoadedProgram {
    /// Origins of the smallest annotated occurrence containing the cursor.
    /// More specific occurrence maps take precedence over an enclosing rule's
    /// `self` map. Equal spans retain every distinct identity and range.
    /// Nonempty ranges include their end for a caret just after a token.
    pub fn origins_at(&self, uri: &str, byte: usize) -> Vec<OriginDescriptor> {
        let mut smallest = usize::MAX;
        let mut found = std::collections::BTreeSet::new();
        for (target, descriptors) in &self.embedded.associations {
            let spans = match target {
                OriginTarget::Occurrence(id) => self
                    .provenance
                    .origins(*id)
                    .iter()
                    .map(|o| o.span)
                    .collect::<Vec<_>>(),
            };
            for span in spans {
                let range = span.byte_range();
                if !(range.contains(&byte) || !range.is_empty() && byte == range.end)
                    || !self
                        .sources
                        .snapshot(span.snapshot())
                        .is_ok_and(|s| s.uri == uri)
                {
                    continue;
                }
                if range.len() < smallest {
                    smallest = range.len();
                    found.clear();
                }
                if range.len() == smallest {
                    found.extend(descriptors.iter().cloned());
                }
            }
        }
        found.into_iter().collect()
    }
}
pub trait OriginResolver {
    fn resolve(&mut self, source: &SourceIdentity) -> Result<Arc<str>, Unavailable>;
}
impl<F> OriginResolver for F
where
    F: FnMut(&SourceIdentity) -> Result<Arc<str>, Unavailable>,
{
    fn resolve(&mut self, source: &SourceIdentity) -> Result<Arc<str>, Unavailable> {
        self(source)
    }
}
/// Immutable snapshots can resolve every historical view/content identity they hold.
impl OriginResolver for &Sources {
    fn resolve(&mut self, source: &SourceIdentity) -> Result<Arc<str>, Unavailable> {
        let mut found = false;
        for snapshot in self
            .snapshots()
            .filter(|s| s.uri == source.uri && s.view == source.view)
        {
            found = true;
            if content_hash(&snapshot.text) == source.hash {
                return Ok(snapshot.text.clone());
            }
        }
        Err(if found {
            Unavailable::HashMismatch
        } else {
            Unavailable::Missing
        })
    }
}
