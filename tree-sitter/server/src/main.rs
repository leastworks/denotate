mod syntax;

use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DocumentSymbolParams, FileChangeType, InitializeParams, Url,
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

    fn publish(&self, connection: &Connection, uri: &Url) -> Result<()> {
        if let Some(doc) = self.documents.get(uri) {
            Self::send(
                connection,
                "textDocument/publishDiagnostics",
                json!({
                    "uri": uri, "version": doc.version, "diagnostics": doc.diagnostics()
                }),
            )?;
            if self.test_mode {
                Self::send(
                    connection,
                    "denotate/test/validated",
                    json!({"uri": uri, "version": doc.version}),
                )?;
            }
        } else {
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
            .any(|root| path.parent() == Some(root.as_path()))
            || path.extension().is_none_or(|ext| ext != "den")
        {
            return Err("File is outside the flat Denotate workspace".into());
        }
        let text = fs::read_to_string(path)?;
        // Match VS Code's disk-to-editor coordinate space without altering disk.
        let text = text.strip_prefix('\u{feff}').unwrap_or(&text).to_owned();
        let doc = Document::new(&mut self.parser, text, 0, false);
        self.documents.insert(uri.clone(), doc);
        Ok(())
    }

    fn request(&mut self, request: &Request) -> Result<Value> {
        match request.method.as_str() {
            "textDocument/documentSymbol" => {
                let params: DocumentSymbolParams = serde_json::from_value(request.params.clone())?;
                let uri = params.text_document.uri;
                if !self.documents.contains_key(&uri) {
                    self.read_disk(&uri)?;
                }
                Ok(serde_json::to_value(self.documents[&uri].symbols())?)
            }
            // B1 is serial: all prior notification work is already complete.
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
                self.documents.insert(text.uri.clone(), doc);
                self.publish(connection, &text.uri)?;
            }
            "textDocument/didChange" => {
                let params: DidChangeTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                let uri = params.text_document.uri;
                let previous = self.documents.get(&uri).ok_or("Change before open")?;
                if !previous.open || params.text_document.version <= previous.version {
                    return Ok(());
                }
                // Advertise Full sync in B1; ranged edits and old-tree reuse are B4.
                if params
                    .content_changes
                    .iter()
                    .any(|change| change.range.is_some())
                {
                    return Err("B1 advertises full-document synchronization".into());
                }
                if let Some(last) = params.content_changes.into_iter().last() {
                    let doc = Document::new(
                        &mut self.parser,
                        last.text,
                        params.text_document.version,
                        true,
                    );
                    self.documents.insert(uri.clone(), doc);
                    self.publish(connection, &uri)?;
                }
            }
            "textDocument/didClose" => {
                let params: DidCloseTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                self.documents.remove(&params.text_document.uri);
                self.publish(connection, &params.text_document.uri)?;
            }
            "workspace/didChangeWatchedFiles" => {
                let params: DidChangeWatchedFilesParams =
                    serde_json::from_value(notification.params)?;
                for event in params.changes {
                    // Unsaved open buffers remain authoritative over disk events.
                    if self.documents.get(&event.uri).is_some_and(|doc| doc.open) {
                        continue;
                    }
                    self.documents.remove(&event.uri);
                    if event.typ != FileChangeType::DELETED {
                        if let Err(error) = self.read_disk(&event.uri) {
                            eprintln!("disk update: {error}");
                        }
                    }
                    self.publish(connection, &event.uri)?;
                }
            }
            _ => {} // No semantic or cancellation capability claimed in B1.
        }
        Ok(())
    }
}

fn run(connection: &Connection) -> Result<()> {
    let params = connection.initialize(json!({
        "positionEncoding": "utf-16", "textDocumentSync": {"openClose": true, "change": 1},
        "documentSymbolProvider": true
    }))?;
    let initialize: InitializeParams = serde_json::from_value(params.clone())?;
    #[allow(deprecated)]
    let roots: Vec<_> = initialize
        .workspace_folders
        .map(|folders| folders.into_iter().map(|f| f.uri).collect::<Vec<_>>())
        .unwrap_or_else(|| initialize.root_uri.into_iter().collect())
        .into_iter()
        .filter_map(|uri| uri.to_file_path().ok()?.canonicalize().ok())
        .collect();
    let mut server = Server {
        parser: syntax::parser(),
        documents: HashMap::new(),
        roots,
        test_mode: std::env::var("DENOTATE_TEST_MODE").as_deref() == Ok("1"),
    };
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
                let supported = request.method == "textDocument/documentSymbol"
                    || (server.test_mode && request.method == "denotate/test/idle");
                let response = if !supported {
                    Response::new_err(
                        request.id,
                        -32601,
                        format!("Not implemented in B1: {}", request.method),
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
