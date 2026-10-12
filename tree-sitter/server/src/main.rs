mod formatting;
mod projection;
mod rename;
mod semantic;
mod syntax;

use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, DocumentSymbolParams, FileChangeType,
    InitializeParams, TextDocumentPositionParams, Url,
};
use serde_json::{json, Value};
use std::{collections::HashMap, error::Error, fs, path::PathBuf};
use syntax::Document;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

struct Server {
    parser: tree_sitter::Parser,
    documents: HashMap<Url, Document>,
    roots: Vec<PathBuf>,
    test_mode: bool,
    semantics: semantic::Semantics,
    diagnostics: HashMap<Url, Vec<Diagnostic>>,
    diagnostics_dirty: bool,
}

impl Server {
    fn send(connection: &Connection, method: &str, params: Value) -> Result<()> {
        connection
            .sender
            .send(Message::Notification(Notification::new(
                method.into(),
                params,
            )))?;
        Ok(())
    }

    fn refresh_diagnostics(&mut self) {
        if !self.diagnostics_dirty {
            return;
        }
        self.diagnostics = self
            .documents
            .iter()
            .map(|(uri, doc)| {
                let mut diagnostics = doc.diagnostics();
                diagnostics.extend(self.semantics.diagnostics(uri, doc));
                (uri.clone(), diagnostics)
            })
            .collect();
        self.diagnostics_dirty = false;
    }

    fn publish(&mut self, connection: &Connection, uri: &Url) -> Result<()> {
        self.refresh_diagnostics();
        if let Some(doc) = self.documents.get(uri) {
            Self::send(
                connection,
                "textDocument/publishDiagnostics",
                json!({
                    "uri": uri, "version": doc.version, "diagnostics": self.diagnostics[uri]
                }),
            )?;
        } else {
            Self::send(
                connection,
                "textDocument/publishDiagnostics",
                json!({"uri": uri, "diagnostics": []}),
            )?;
        }
        Ok(())
    }

    fn publish_all(&mut self, connection: &Connection) -> Result<()> {
        // Refresh all indexed dependents. Salsa reuses unchanged semantics;
        // selective publication/scheduling is not claimed by this prototype.
        let mut uris: Vec<_> = self.documents.keys().cloned().collect();
        uris.sort();
        for uri in &uris {
            self.publish(connection, uri)?;
        }
        // A barrier covers the entire update, including importer diagnostics.
        // Otherwise a caller waiting on the library can observe old importer
        // diagnostics that were still queued behind an earlier library barrier.
        if self.test_mode {
            for uri in uris {
                Self::send(
                    connection,
                    "denotate/test/validated",
                    json!({"uri": uri, "version": self.documents[&uri].version}),
                )?;
            }
        }
        Ok(())
    }

    fn store(&mut self, uri: Url, doc: Document) {
        // A declaration change can invalidate diagnostics in any importer.
        self.diagnostics_dirty = true;
        self.semantics.update(&uri, &doc);
        self.documents.insert(uri, doc);
    }

    fn remove(&mut self, uri: &Url) {
        self.documents.remove(uri);
        self.semantics.remove(uri);
        self.diagnostics.remove(uri);
        self.diagnostics_dirty = true;
    }

    fn read_disk(&mut self, uri: &Url) -> Result<()> {
        // Flat workspaces only. No parent-directory discovery, recursion, or
        // filesystem reads for arbitrary LSP URIs (including symlink escapes).
        let path = uri.to_file_path().map_err(|_| "Expected a file URI")?;
        let path = path.canonicalize()?;
        if !self
            .roots
            .iter()
            .any(|root| root.canonicalize().ok().as_deref() == path.parent())
            || path.extension().is_none_or(|ext| ext != "den")
        {
            return Err("File is outside the flat Denotate workspace".into());
        }
        let text = fs::read_to_string(path)?;
        // Match VS Code's disk-to-editor coordinate space without altering disk.
        let text = text.strip_prefix('\u{feff}').unwrap_or(&text).to_owned();
        let doc = Document::new(&mut self.parser, text, 0, false);
        self.store(uri.clone(), doc);
        Ok(())
    }

    fn request(&mut self, request: &Request) -> Result<Value> {
        match request.method.as_str() {
            "textDocument/formatting" | "textDocument/rangeFormatting" => {
                let params: DocumentSymbolParams = serde_json::from_value(request.params.clone())?;
                let uri = params.text_document.uri;
                if !self.documents.contains_key(&uri) {
                    self.read_disk(&uri)?;
                }
                let range = request
                    .params
                    .get("range")
                    .map(|r| serde_json::from_value(r.clone()))
                    .transpose()?;
                Ok(formatting::format(&self.documents[&uri], range))
            }
            "textDocument/documentSymbol" | "textDocument/semanticTokens/full" => {
                let params: DocumentSymbolParams = serde_json::from_value(request.params.clone())?;
                let uri = params.text_document.uri;
                if !self.documents.contains_key(&uri) {
                    self.read_disk(&uri)?;
                }
                if request.method == "textDocument/documentSymbol" {
                    Ok(serde_json::to_value(self.documents[&uri].symbols())?)
                } else {
                    Ok(self.semantics.semantic_tokens(&uri, &self.documents[&uri]))
                }
            }
            "textDocument/definition"
            | "textDocument/completion"
            | "textDocument/references"
            | "textDocument/hover"
            | "textDocument/signatureHelp"
            | "textDocument/prepareRename"
            | "textDocument/rename" => {
                let params: TextDocumentPositionParams =
                    serde_json::from_value(request.params.clone())?;
                let uri = params.text_document.uri;
                if !self.documents.contains_key(&uri) {
                    self.read_disk(&uri)?;
                }
                if matches!(
                    request.method.as_str(),
                    "textDocument/prepareRename" | "textDocument/rename"
                ) {
                    // Normally publication has already refreshed this cache.
                    // Also cover cold requests and files loaded lazily by requests.
                    self.refresh_diagnostics();
                }
                let doc = &self.documents[&uri];
                Ok(match request.method.as_str() {
                    "textDocument/definition" => {
                        self.semantics
                            .definition(&uri, doc, params.position, &self.documents)
                    }
                    "textDocument/references" => self.semantics.references(
                        &uri,
                        doc,
                        params.position,
                        request.params["context"]["includeDeclaration"] == true,
                        &self.documents,
                    ),
                    "textDocument/hover" => self.semantics.hover(&uri, doc, params.position),
                    "textDocument/signatureHelp" => {
                        self.semantics.signature_help(&uri, doc, params.position)
                    }
                    "textDocument/prepareRename" | "textDocument/rename" => rename::rename(
                        &self.semantics,
                        &self.documents,
                        &self.diagnostics,
                        &self.roots,
                        &uri,
                        params.position,
                        if request.method == "textDocument/rename" {
                            Some(
                                request.params["newName"]
                                    .as_str()
                                    .ok_or("Missing newName")?,
                            )
                        } else {
                            None
                        },
                    )
                    .map_err(|e| -> Box<dyn Error> { e.into() })?,
                    _ => self.semantics.completion(&uri, doc, params.position),
                })
            }
            "denotate/test/analysis" if self.test_mode => Ok(self.semantics.stats()),
            // Serial owner loop: all prior notification work is complete.
            "denotate/test/idle" if self.test_mode => Ok(Value::Null),
            _ => Err("Unsupported request".into()),
        }
    }

    fn notification(&mut self, connection: &Connection, notification: Notification) -> Result<()> {
        match notification.method.as_str() {
            "textDocument/didOpen" => {
                let params: DidOpenTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                let text = params.text_document;
                let doc = Document::new(&mut self.parser, text.text, text.version, true);
                self.store(text.uri, doc);
                self.publish_all(connection)?;
            }
            "textDocument/didChange" => {
                let params: DidChangeTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                let uri = params.text_document.uri;
                let previous = self.documents.get(&uri).ok_or("Change before open")?;
                if !previous.open || params.text_document.version <= previous.version {
                    return Ok(());
                }
                // Full sync until B4 adds ranged edits and old-tree reuse.
                if params
                    .content_changes
                    .iter()
                    .any(|change| change.range.is_some())
                {
                    return Err("Server advertises full-document synchronization".into());
                }
                if let Some(last) = params.content_changes.into_iter().last() {
                    let doc = Document::new(
                        &mut self.parser,
                        last.text,
                        params.text_document.version,
                        true,
                    );
                    self.store(uri, doc);
                    self.publish_all(connection)?;
                }
            }
            "textDocument/didClose" => {
                let params: DidCloseTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                self.remove(&params.text_document.uri);
                self.publish(connection, &params.text_document.uri)?;
                // Closing an unsaved buffer restores disk facts, not stale edits.
                let _ = self.read_disk(&params.text_document.uri);
                self.publish_all(connection)?;
            }
            "workspace/didChangeWatchedFiles" => {
                let params: DidChangeWatchedFilesParams =
                    serde_json::from_value(notification.params)?;
                let mut removed = vec![];
                for event in params.changes {
                    // Unsaved open buffers remain authoritative over disk events.
                    if self.documents.get(&event.uri).is_some_and(|doc| doc.open) {
                        continue;
                    }
                    self.remove(&event.uri);
                    if event.typ != FileChangeType::DELETED {
                        if let Err(error) = self.read_disk(&event.uri) {
                            eprintln!("disk update: {error}");
                        }
                    }
                    if !self.documents.contains_key(&event.uri) {
                        removed.push(event.uri);
                    }
                }
                // Publish after the entire batch, never an intermediate corpus.
                for uri in removed {
                    self.publish(connection, &uri)?;
                }
                self.publish_all(connection)?;
            }
            _ => {} // Unsupported notifications; cancellation is still B4 work.
        }
        Ok(())
    }
}

fn run(connection: &Connection) -> Result<()> {
    let params = connection.initialize(json!({
        "positionEncoding": "utf-16", "textDocumentSync": {"openClose": true, "change": 1},
        "documentSymbolProvider": true, "definitionProvider": true,
        "completionProvider": {"triggerCharacters": ["(", ",", ":"]},
        "referencesProvider": true, "hoverProvider": true, "renameProvider": {"prepareProvider": true},
        "documentFormattingProvider": true, "documentRangeFormattingProvider": true,
        "signatureHelpProvider": {"triggerCharacters": ["(", ","], "retriggerCharacters": [","]},
        "semanticTokensProvider": {"legend": {"tokenTypes": ["type", "variable", "function", "namespace", "parameter"], "tokenModifiers": ["readonly"]}, "full": true}
    }))?;
    let initialize: InitializeParams = serde_json::from_value(params.clone())?;
    #[allow(deprecated)]
    let roots: Vec<_> = initialize
        .workspace_folders
        .map(|folders| folders.into_iter().map(|f| f.uri).collect::<Vec<_>>())
        .unwrap_or_else(|| initialize.root_uri.into_iter().collect())
        .into_iter()
        // Preserve client URI spelling (e.g. /var vs /private/var on macOS).
        // Canonical paths are used only for filesystem access checks.
        .filter_map(|uri| uri.to_file_path().ok())
        .collect();
    let mut server = Server {
        parser: syntax::parser(),
        documents: HashMap::new(),
        roots,
        test_mode: std::env::var("DENOTATE_TEST_MODE").as_deref() == Ok("1"),
        semantics: semantic::Semantics::default(),
        diagnostics: HashMap::new(),
        diagnostics_dirty: true,
    };
    // Only direct .den children of explicitly opened roots; never walk ancestors
    // or dependencies outside the workspace. Stable order also stabilizes catalog.
    let mut files = vec![];
    for root in &server.roots {
        for entry in fs::read_dir(root)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "den") {
                if let Ok(uri) = Url::from_file_path(path) {
                    files.push(uri);
                }
            }
        }
    }
    files.sort();
    files.dedup();
    for uri in files {
        if let Err(error) = server.read_disk(&uri) {
            eprintln!("workspace read: {error}");
        }
    }
    if params["capabilities"]["workspace"]["didChangeWatchedFiles"]["dynamicRegistration"] == true {
        connection.sender.send(Message::Request(Request::new(1.into(), "client/registerCapability".into(), json!({
            "registrations": [{"id": "denotate-files", "method": "workspace/didChangeWatchedFiles",
                "registerOptions": {"watchers": [{"globPattern": "**/*.den", "kind": 7}]}}]
        }))))?;
    }
    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    break;
                }
                let supported = matches!(
                    request.method.as_str(),
                    "textDocument/documentSymbol"
                        | "textDocument/semanticTokens/full"
                        | "textDocument/definition"
                        | "textDocument/completion"
                        | "textDocument/references"
                        | "textDocument/hover"
                        | "textDocument/signatureHelp"
                        | "textDocument/rename"
                        | "textDocument/prepareRename"
                        | "textDocument/formatting"
                        | "textDocument/rangeFormatting"
                ) || (server.test_mode
                    && matches!(
                        request.method.as_str(),
                        "denotate/test/idle" | "denotate/test/analysis"
                    ));
                let response = if !supported {
                    Response::new_err(
                        request.id,
                        -32601,
                        format!("Unsupported request: {}", request.method),
                    )
                } else {
                    match server.request(&request) {
                        Ok(value) => Response::new_ok(request.id, value),
                        Err(error) => Response::new_err(request.id, -32602, error.to_string()),
                    }
                };
                connection.sender.send(Message::Response(response))?;
            }
            Message::Notification(notification) => {
                if notification.method == "exit" {
                    break;
                }
                if let Err(error) = server.notification(connection, notification) {
                    eprintln!("notification rejected: {error}");
                }
            }
            Message::Response(_) => {} // Registration acknowledgment.
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let (connection, threads) = Connection::stdio();
    let result = run(&connection);
    drop(connection);
    threads.join()?;
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn published_diagnostics_are_reused_and_invalidated_with_dependencies() {
        let mut server = Server {
            parser: syntax::parser(),
            documents: HashMap::new(),
            roots: vec![],
            test_mode: false,
            semantics: semantic::Semantics::default(),
            diagnostics: HashMap::new(),
            diagnostics_dirty: true,
        };
        let library = Url::parse("file:///computation.den").unwrap();
        let program = Url::parse("file:///example.den").unwrap();
        let doc = Document::new(
            &mut server.parser,
            "module example; use computation; const a: Slot; r(a);".into(),
            1,
            true,
        );
        server.store(program.clone(), doc);
        let (connection, client) = Connection::memory();
        server.publish(&connection, &program).unwrap();
        let Message::Notification(published) = client.receiver.recv().unwrap() else {
            panic!("diagnostics expected")
        };
        assert_eq!(
            published.params["diagnostics"],
            json!(server.diagnostics[&program])
        );
        assert!(!server.diagnostics[&program].is_empty());
        let cached = server.diagnostics[&program].as_ptr();
        server.refresh_diagnostics();
        assert_eq!(cached, server.diagnostics[&program].as_ptr());

        // Loading a dependency outside publication must invalidate importers too.
        let doc = Document::new(
            &mut server.parser,
            "module computation; sort Slot; relation r(x: Slot);".into(),
            0,
            false,
        );
        server.store(library.clone(), doc);
        assert!(server.diagnostics_dirty);
        server.refresh_diagnostics();
        assert!(server.diagnostics[&program].is_empty());
        assert!(server.diagnostics[&library].is_empty());

        let doc = Document::new(
            &mut server.parser,
            "module computation; sort Slot; relation r(x: );".into(),
            1,
            true,
        );
        server.store(library.clone(), doc);
        server.refresh_diagnostics();
        assert!(server.diagnostics[&library]
            .iter()
            .any(|d| d.source.as_deref() == Some("denotate-syntax")));

        server.remove(&library);
        assert!(!server.diagnostics.contains_key(&library));
        server.refresh_diagnostics();
        assert!(server.diagnostics[&program]
            .iter()
            .any(|d| d.code == Some(lsp_types::NumberOrString::String("resolution".into()))));
    }
}
