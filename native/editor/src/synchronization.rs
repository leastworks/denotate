use crate::Document;
use lsp_types::{TextDocumentContentChangeEvent, Url};
use serde_json::Value;
use std::{collections::HashMap, ops::Deref};

/// Per-document synchronization only. The frontend decides whether losing one
/// document also blocks its dependents (or, in B, the whole workspace).
pub struct Documents<D> {
    documents: HashMap<Url, D>,
    // Latest rejected version. Retained text cannot be used until resync.
    rejected: HashMap<Url, i32>,
}

impl<D> Default for Documents<D> {
    fn default() -> Self {
        Self {
            documents: HashMap::new(),
            rejected: HashMap::new(),
        }
    }
}

// Read-only map access keeps source lookup convenient without allowing a caller
// to replace text while accidentally retaining an out-of-sync marker.
impl<D> Deref for Documents<D> {
    type Target = HashMap<Url, D>;
    fn deref(&self) -> &Self::Target {
        &self.documents
    }
}

impl<D> Documents<D> {
    pub fn insert(&mut self, uri: Url, document: D) {
        self.rejected.remove(&uri);
        self.documents.insert(uri, document);
    }

    pub fn remove(&mut self, uri: &Url) {
        self.rejected.remove(uri);
        self.documents.remove(uri);
    }

    /// True only on the first loss of sync, when stale diagnostics need clearing.
    pub fn lose_sync(&mut self, uri: &Url, version: i32) -> bool {
        let first = !self.rejected.contains_key(uri);
        self.rejected
            .entry(uri.clone())
            .and_modify(|v| *v = (*v).max(version))
            .or_insert(version);
        first
    }

    pub fn has_out_of_sync(&self) -> bool {
        !self.rejected.is_empty()
    }

    pub fn rejected_version(&self, uri: &Url) -> Option<i32> {
        self.rejected.get(uri).copied()
    }
}

impl<D: AsRef<Document>> Documents<D> {
    /// Select changes safe to apply to the retained text. The frontend commits
    /// a successful parse with insert(), or marks failure with lose_sync().
    pub fn changes<'a>(
        &self,
        uri: &Url,
        version: i32,
        changes: &'a [TextDocumentContentChangeEvent],
    ) -> Result<Option<&'a [TextDocumentContentChangeEvent]>, &'static str> {
        let previous = self
            .documents
            .get(uri)
            .ok_or("Change before open")?
            .as_ref();
        if !previous.open
            || version <= self.rejected_version(uri).unwrap_or(previous.version)
            || changes.is_empty()
        {
            return Ok(None);
        }
        // A full replacement makes earlier changes irrelevant, and is the only
        // safe basis for editing a document whose retained text is stale.
        let full = changes.iter().rposition(|c| c.range.is_none());
        if self.rejected.contains_key(uri) && full.is_none() {
            return Err("Document is out of sync; reopen or send full text.");
        }
        Ok(Some(&changes[full.unwrap_or(0)..]))
    }

    /// Recover document identity from a didChange payload rejected by decoding.
    /// The caller retains only textDocument metadata, not the full change text.
    pub fn malformed_change(&self, metadata: &Value) -> Option<(Url, i32)> {
        let uri = Url::parse(metadata["uri"].as_str()?).ok()?;
        let doc = self.documents.get(&uri)?.as_ref();
        if !doc.open {
            return None;
        }
        let version = metadata["version"]
            .as_i64()
            .and_then(|v| i32::try_from(v).ok())
            .unwrap_or(doc.version);
        Some((uri, version))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recovery_state_is_per_document_and_replacement_or_removal_clears_it() {
        let a = Url::parse("file:///a.any").unwrap();
        let b = Url::parse("file:///b.any").unwrap();
        let mut documents = Documents::default();
        documents.insert(a.clone(), "a retained snapshot");
        documents.insert(b.clone(), "b independent snapshot");
        assert!(documents.lose_sync(&a, 5));
        assert!(!documents.lose_sync(&a, 4));
        assert_eq!(documents.rejected_version(&a), Some(5));
        assert_eq!(documents.rejected_version(&b), None);
        assert_eq!(documents[&b], "b independent snapshot");
        assert!(!documents.lose_sync(&a, 6));
        assert_eq!(documents.rejected_version(&a), Some(6));
        documents.insert(a.clone(), "a reopened snapshot");
        assert!(!documents.has_out_of_sync());
        assert!(documents.lose_sync(&a, 2));
        documents.remove(&a);
        assert!(!documents.has_out_of_sync());
        assert!(!documents.contains_key(&a));
        assert_eq!(documents.len(), 1);
    }
}
