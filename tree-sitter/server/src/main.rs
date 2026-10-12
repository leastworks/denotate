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
use std::{
    collections::{HashMap, VecDeque},
    error::Error,
    fs,
    path::PathBuf,
};
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
    // Latest rejected version; retained text is not authoritative until resync.
    out_of_sync: HashMap<Url, i32>,
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
        if !self.out_of_sync.is_empty() {
            return Ok(());
        }
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
        // A missing observation can affect every importer. Pause the whole
        // small prototype workspace rather than publishing guessed dependents.
        if !self.out_of_sync.is_empty() {
            return Ok(());
        }
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
        self.out_of_sync.remove(&uri);
        // A declaration change can invalidate diagnostics in any importer.
        self.diagnostics_dirty = true;
        self.semantics.update(&uri, &doc);
        self.documents.insert(uri, doc);
    }

    fn remove(&mut self, uri: &Url) {
        self.out_of_sync.remove(uri);
        self.documents.remove(uri);
        self.semantics.remove(uri);
        self.diagnostics.remove(uri);
        self.diagnostics_dirty = true;
    }

    fn lose_sync(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()> {
        let newly_lost = !self.out_of_sync.contains_key(uri);
        self.out_of_sync
            .entry(uri.clone())
            .and_modify(|v| *v = (*v).max(version))
            .or_insert(version);
        self.semantics.remove(uri);
        self.diagnostics.clear();
        self.diagnostics_dirty = true;
        if newly_lost {
            // Withdraw stale diagnostics, without claiming to have analyzed a
            // version of the now-unknown text or emitting a validation barrier.
            Self::send(
                connection,
                "textDocument/publishDiagnostics",
                json!({"uri": uri, "diagnostics": []}),
            )?;
        }
        Ok(())
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
        if request.method.starts_with("textDocument/") && !self.out_of_sync.is_empty() {
            return Err("Workspace is out of sync; reopen the affected document or send a full-text change.".into());
        }
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
                // Keep only identity/version for recovery if decoding fails;
                // do not clone the potentially large full-text change payload.
                let metadata = notification.params["textDocument"].clone();
                let params: DidChangeTextDocumentParams =
                    match serde_json::from_value(notification.params) {
                        Ok(params) => params,
                        Err(error) => {
                            if let Some(uri) =
                                metadata["uri"].as_str().and_then(|s| Url::parse(s).ok())
                            {
                                if let Some(doc) = self.documents.get(&uri).filter(|d| d.open) {
                                    let version = metadata["version"]
                                        .as_i64()
                                        .and_then(|v| i32::try_from(v).ok())
                                        .unwrap_or(doc.version);
                                    self.lose_sync(connection, &uri, version)?;
                                }
                            }
                            return Err(error.into());
                        }
                    };
                let uri = params.text_document.uri;
                let previous = self.documents.get(&uri).ok_or("Change before open")?;
                if !previous.open
                    || params.text_document.version
                        <= self
                            .out_of_sync
                            .get(&uri)
                            .copied()
                            .unwrap_or(previous.version)
                {
                    return Ok(());
                }
                if !params.content_changes.is_empty() {
                    // A full replacement makes earlier changes in this batch
                    // irrelevant and is the only safe basis after a rejection.
                    let full = params
                        .content_changes
                        .iter()
                        .rposition(|c| c.range.is_none());
                    if self.out_of_sync.contains_key(&uri) && full.is_none() {
                        self.lose_sync(connection, &uri, params.text_document.version)?;
                        return Err("Document is out of sync; reopen or send full text.".into());
                    }
                    let changed = previous.changed(
                        &mut self.parser,
                        &params.content_changes[full.unwrap_or(0)..],
                        params.text_document.version,
                    );
                    let doc = match changed {
                        Ok(doc) => doc,
                        Err(error) => {
                            self.lose_sync(connection, &uri, params.text_document.version)?;
                            return Err(error.into());
                        }
                    };
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
            _ => {} // Late cancellation is harmless; queued/active checks live in dispatch.
        }
        Ok(())
    }
}

// Bounded draining prevents an endless stream from monopolizing dispatch.
// This is a checkpoint, not preemption of parsing or synchronous Salsa calls.
fn receive_ready(connection: &Connection, pending: &mut VecDeque<Message>) {
    pending.extend(connection.receiver.try_iter().take(256));
}

fn take_cancellation(pending: &mut VecDeque<Message>, id: &lsp_server::RequestId) -> bool {
    let mut cancelled = false;
    pending.retain(|message| {
        let matches = matches!(message, Message::Notification(n)
            if n.method == "$/cancelRequest" && n.params.get("id") == Some(&json!(id)));
        cancelled |= matches;
        !matches
    });
    cancelled
}

fn run(connection: &Connection) -> Result<()> {
    let params = connection.initialize(json!({
        "positionEncoding": "utf-16", "textDocumentSync": {"openClose": true, "change": 2},
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
        out_of_sync: HashMap::new(),
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
    let mut pending = VecDeque::new();
    loop {
        if pending.is_empty() {
            let Ok(message) = connection.receiver.recv() else {
                break;
            };
            pending.push_back(message);
        }
        receive_ready(connection, &mut pending);
        let Some(message) = pending.pop_front() else {
            continue;
        };
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    break;
                }
                dispatch_request(&mut server, request, connection, &mut pending)?;
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

fn dispatch_request(
    server: &mut Server,
    request: Request,
    connection: &Connection,
    pending: &mut VecDeque<Message>,
) -> Result<()> {
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
    let mut response = if take_cancellation(pending, &request.id) {
        Response::new_err(request.id.clone(), -32800, "Request cancelled".into())
    } else if !supported {
        Response::new_err(
            request.id.clone(),
            -32601,
            format!("Unsupported request: {}", request.method),
        )
    } else {
        match server.request(&request) {
            Ok(value) => Response::new_ok(request.id.clone(), value),
            Err(error) => Response::new_err(
                request.id.clone(),
                if server.out_of_sync.is_empty() {
                    -32602
                } else {
                    -32801
                },
                error.to_string(),
            ),
        }
    };
    receive_ready(connection, pending);
    if take_cancellation(pending, &request.id) {
        response = Response::new_err(request.id, -32800, "Request cancelled".into());
    }
    connection.sender.send(Message::Response(response))?;
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
    fn old_versions_and_invalid_ranges_cannot_replace_current_observation() {
        let mut server = Server {
            parser: syntax::parser(),
            documents: HashMap::new(),
            roots: vec![],
            test_mode: true,
            semantics: semantic::Semantics::default(),
            diagnostics: HashMap::new(),
            diagnostics_dirty: true,
            out_of_sync: HashMap::new(),
        };
        let uri = Url::parse("file:///example.den").unwrap();
        let doc = Document::new(&mut server.parser, "module example; sort S".into(), 4, true);
        server.store(uri.clone(), doc);
        let (transport, client) = Connection::memory();
        server.publish(&transport, &uri).unwrap();
        let Message::Notification(initial) = client.receiver.recv().unwrap() else {
            panic!("initial diagnostics expected")
        };
        assert!(!initial.params["diagnostics"].as_array().unwrap().is_empty());
        let assert_withdrawal = || {
            let Message::Notification(clear) = client.receiver.try_recv().unwrap() else {
                panic!("diagnostic withdrawal expected")
            };
            assert_eq!(clear.method, "textDocument/publishDiagnostics");
            assert_eq!(clear.params, json!({"uri": uri, "diagnostics": []}));
            // In particular, no validated barrier for the rejected observation.
            assert!(client.receiver.try_recv().is_err());
        };
        for version in [3, 4] {
            server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
                "textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": "broken"}]
            }))).unwrap();
        }
        let invalid = server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
            "textDocument": {"uri": uri, "version": 5}, "contentChanges": [
                {"range": {"start": {"line":0,"character":0}, "end": {"line":0,"character":0}}, "text":" "},
                {"range": {"start": {"line":0,"character":2}, "end": {"line":0,"character":1}}, "text":"bad"}
            ]
        })));
        assert!(invalid.is_err());
        assert_eq!(server.documents[&uri].version, 4);
        assert_eq!(server.documents[&uri].text, "module example; sort S");
        assert_withdrawal();
        assert_eq!(server.out_of_sync[&uri], 5);
        assert!(!server.semantics.files.contains_key(&uri));
        // An otherwise applicable subsequent range must not run on stale text.
        assert!(server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
            "textDocument": {"uri": uri, "version": 6}, "contentChanges": [{
                "range": {"start":{"line":0,"character":21},"end":{"line":0,"character":21}}, "text":"x"
            }]
        }))).is_err());
        assert_eq!(server.out_of_sync[&uri], 6);
        assert_eq!(server.documents[&uri].version, 4);
        server.publish_all(&transport).unwrap();
        assert!(client.receiver.try_recv().is_err());
        for method in [
            "textDocument/formatting",
            "textDocument/rename",
            "textDocument/prepareRename",
            "textDocument/definition",
        ] {
            let error = server
                .request(&Request::new(
                    1.into(),
                    method.into(),
                    json!({"textDocument":{"uri":uri}}),
                ))
                .unwrap_err();
            assert!(error.to_string().contains("out of sync"));
        }
        // A later full replacement is authoritative even after earlier ranges
        // in the same notification; no stale prefix is needed to apply it.
        server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
            "textDocument": {"uri": uri, "version": 7}, "contentChanges": [
                {"range":{"start":{"line":0,"character":3},"end":{"line":0,"character":1}},"text":"bad"},
                {"text":"module example; sort Recovered;"}
            ]
        }))).unwrap();
        assert!(server.out_of_sync.is_empty());
        assert_eq!(server.documents[&uri].version, 7);
        assert_eq!(
            server.documents[&uri].text,
            "module example; sort Recovered;"
        );
        let Message::Notification(publication) = client.receiver.recv().unwrap() else {
            panic!("publication expected")
        };
        assert_eq!(publication.params["version"], 7);
        assert_eq!(publication.params["diagnostics"], json!([]));
        let Message::Notification(barrier) = client.receiver.recv().unwrap() else {
            panic!("recovery validation expected")
        };
        assert_eq!(barrier.method, "denotate/test/validated");
        assert_eq!(barrier.params["version"], 7);
        // Even payloads rejected by deserialization lose sync, not just ranges
        // rejected by the text editor. didOpen starts a new authoritative buffer.
        assert!(server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
            "textDocument":{"uri":uri,"version":8}, "contentChanges":[{"text":"x","range":{"start":{"line":-1,"character":0},"end":{"line":0,"character":0}}}]
        }))).is_err());
        assert_eq!(server.out_of_sync[&uri], 8);
        assert_withdrawal();
        server.notification(&transport, Notification::new("textDocument/didOpen".into(), json!({
            "textDocument":{"uri":uri,"version":1,"languageId":"denotate","text":"module example; sort Reopened;"}
        }))).unwrap();
        assert!(server.out_of_sync.is_empty());
        assert_eq!(server.documents[&uri].version, 1);
        assert_eq!(
            server.documents[&uri].text,
            "module example; sort Reopened;"
        );
    }

    #[test]
    fn cancellation_checkpoints_preserve_other_messages_and_ignore_late_ids() {
        let (server, client) = Connection::memory();
        let id = lsp_server::RequestId::from(7);
        let change = Message::Notification(Notification::new(
            "textDocument/didChange".into(),
            json!({"version": 3}),
        ));
        client.sender.send(change.clone()).unwrap();
        client
            .sender
            .send(Message::Notification(Notification::new(
                "$/cancelRequest".into(),
                json!({"id": 7}),
            )))
            .unwrap();
        let mut pending = VecDeque::new();
        receive_ready(&server, &mut pending);
        assert!(take_cancellation(&mut pending, &id));
        assert_eq!(pending.len(), 1);
        assert_eq!(
            serde_json::to_value(pending.front().unwrap()).unwrap(),
            serde_json::to_value(change).unwrap()
        );
        assert!(!take_cancellation(&mut pending, &id));
        client
            .sender
            .send(Message::Notification(Notification::new(
                "$/cancelRequest".into(),
                json!({"id": 7}),
            )))
            .unwrap();
        receive_ready(&server, &mut pending);
        assert!(!take_cancellation(&mut pending, &8.into()));
        assert!(take_cancellation(&mut pending, &id));
    }

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
            out_of_sync: HashMap::new(),
        };
        // Exercise the real dispatch path with cancellation already queued:
        // even malformed params must not reach request execution.
        let (transport, client) = Connection::memory();
        let mut pending = VecDeque::from([Message::Notification(Notification::new(
            "$/cancelRequest".into(),
            json!({"id": 7}),
        ))]);
        dispatch_request(
            &mut server,
            Request::new(7.into(), "textDocument/rename".into(), Value::Null),
            &transport,
            &mut pending,
        )
        .unwrap();
        let Message::Response(reply) = client.receiver.recv().unwrap() else {
            panic!("response expected")
        };
        assert_eq!(reply.error.unwrap().code, -32800);
        assert!(reply.result.is_none());
        assert!(server.diagnostics_dirty);
        assert!(client.receiver.try_recv().is_err());
        // Cancellation received at the post-computation checkpoint also wins.
        client
            .sender
            .send(Message::Notification(Notification::new(
                "$/cancelRequest".into(),
                json!({"id": 8}),
            )))
            .unwrap();
        server.test_mode = true;
        dispatch_request(
            &mut server,
            Request::new(8.into(), "denotate/test/analysis".into(), json!({})),
            &transport,
            &mut pending,
        )
        .unwrap();
        let Message::Response(reply) = client.receiver.recv().unwrap() else {
            panic!("response expected")
        };
        assert_eq!(reply.error.unwrap().code, -32800);
        assert!(reply.result.is_none());
        server.test_mode = false;
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

        // The owner can have computed a diagnostic set before a newer input.
        // Publication must refresh from that input, never relabel the old set.

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
        server.publish(&connection, &program).unwrap();
        let Message::Notification(published) = client.receiver.recv().unwrap() else {
            panic!("diagnostics expected")
        };
        assert_eq!(published.params["diagnostics"], json!([]));
        assert_eq!(published.params["version"], 1); // importer itself did not change

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
