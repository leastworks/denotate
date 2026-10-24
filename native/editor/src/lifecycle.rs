//! Text-document notification decoding and transactional synchronization. The
//! frontend supplies parsing wrappers and stored/removed/sync-lost side effects.
use crate::{transport::Result, Document, Documents};
use lsp_server::{Connection, Notification};
use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    TextDocumentContentChangeEvent, Url,
};
use tree_sitter::Parser;

pub trait Lifecycle {
    type Stored: AsRef<Document>;
    type Parsed;
    fn documents_and_parser(&mut self) -> (&Documents<Self::Stored>, &mut Parser);
    fn parse_open(parser: &mut Parser, text: String, version: i32) -> Self::Parsed;
    fn parse_change(
        previous: &Self::Stored,
        parser: &mut Parser,
        changes: &[TextDocumentContentChangeEvent],
        version: i32,
    ) -> std::result::Result<Self::Parsed, &'static str>;
    fn stored(
        &mut self,
        connection: &Connection,
        uri: Url,
        document: Self::Parsed,
        opened: bool,
        new_document: bool,
    ) -> Result<()>;
    fn removed(&mut self, connection: &Connection, uri: &Url) -> Result<()>;
    fn sync_lost(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()>;
}

pub fn handles(method: &str) -> bool {
    matches!(
        method,
        "textDocument/didOpen" | "textDocument/didChange" | "textDocument/didClose"
    )
}
/// Call after language-specific pre-filters. A rejected change retains the old
/// snapshot, marks it unusable through sync_lost, and returns the decoding/edit
/// error. An explicit open or a newer full replacement can restore authority.
pub fn notification<H: Lifecycle>(
    handler: &mut H,
    connection: &Connection,
    n: Notification,
) -> Result<()> {
    match n.method.as_str() {
        "textDocument/didOpen" => {
            let p: DidOpenTextDocumentParams = serde_json::from_value(n.params)?;
            let t = p.text_document;
            let (documents, parser) = handler.documents_and_parser();
            let new_document = !documents.contains_key(&t.uri);
            let document = H::parse_open(parser, t.text, t.version);
            handler.stored(connection, t.uri, document, true, new_document)?;
        }
        "textDocument/didChange" => {
            // Only clone identity/version, never the potentially large text payload.
            let metadata = n.params["textDocument"].clone();
            let p: DidChangeTextDocumentParams = match serde_json::from_value(n.params) {
                Ok(p) => p,
                Err(error) => {
                    if let Some((uri, version)) =
                        handler.documents_and_parser().0.malformed_change(&metadata)
                    {
                        handler.sync_lost(connection, &uri, version)?;
                    }
                    return Err(error.into());
                }
            };
            let uri = p.text_document.uri;
            let version = p.text_document.version;
            let (documents, parser) = handler.documents_and_parser();
            let previous = documents.get(&uri).ok_or("Change before open")?;
            let changed = documents
                .changes(&uri, version, &p.content_changes)
                .and_then(|changes| {
                    changes
                        .map(|changes| H::parse_change(previous, parser, changes, version))
                        .transpose()
                });
            match changed {
                Ok(Some(document)) => handler.stored(connection, uri, document, false, false)?,
                Ok(None) => (),
                Err(error) => {
                    handler.sync_lost(connection, &uri, version)?;
                    return Err(error.into());
                }
            }
        }
        "textDocument/didClose" => {
            let p: DidCloseTextDocumentParams = serde_json::from_value(n.params)?;
            handler.removed(connection, &p.text_document.uri)?;
        }
        _ => return Err("Not a document lifecycle notification".into()),
    }
    Ok(())
}
