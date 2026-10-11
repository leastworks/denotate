use serde_json::{json, Value};
use std::{
    fs,
    io::{BufRead, BufReader, Read, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{mpsc, Arc, Mutex},
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};
use tempfile::TempDir;

const TIMEOUT: Duration = Duration::from_secs(20);

/// Apply LSP TextEdits against the original text, never against shifted offsets.
/// Reject invalid ranges instead of letting a malformed server edit pass a test.
#[allow(dead_code)] // This support module is compiled into each integration test.
pub fn apply_edits(text: &str, edits: &[Value]) -> String {
    let mut lines = vec![0];
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\r' {
            i += 1;
            if bytes.get(i) == Some(&b'\n') {
                i += 1;
            }
            lines.push(i);
        } else if bytes[i] == b'\n' {
            i += 1;
            lines.push(i);
        } else {
            i += 1;
        }
    }
    let offset = |position: &Value| {
        let line = position["line"].as_u64().expect("line number") as usize;
        let column = position["character"].as_u64().expect("UTF-16 column") as usize;
        let start = *lines.get(line).expect("line outside document");
        let mut units = 0;
        for (byte, ch) in text[start..].char_indices() {
            if units == column {
                return start + byte;
            }
            assert!(ch != '\r' && ch != '\n', "column past end of line");
            units += ch.len_utf16();
            assert!(units <= column, "position splits a UTF-16 surrogate pair");
        }
        assert_eq!(units, column, "column past end of document");
        text.len()
    };
    let mut ranges: Vec<_> = edits
        .iter()
        .map(|edit| {
            let start = offset(&edit["range"]["start"]);
            let end = offset(&edit["range"]["end"]);
            assert!(start <= end, "reversed edit range");
            (
                start,
                end,
                edit["newText"].as_str().expect("edit replacement"),
            )
        })
        .collect();
    // Stable order preserves the supplied order for insertions at one position.
    ranges.sort_by_key(|(start, end, _)| (*start, *end));
    for pair in ranges.windows(2) {
        assert!(pair[0].1 <= pair[1].0, "overlapping edits");
    }
    let mut result = text.to_owned();
    for (start, end, replacement) in ranges.into_iter().rev() {
        result.replace_range(start..end, replacement);
    }
    result
}

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

pub fn file_uri(path: &Path) -> String {
    let path = path.to_str().expect("UTF-8 test path").replace('\\', "/");
    let mut uri = if path.starts_with('/') {
        "file://"
    } else {
        "file:///"
    }
    .to_string();
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || b"/-._~:".contains(&byte) {
            uri.push(byte as char);
        } else {
            uri.push_str(&format!("%{byte:02X}"));
        }
    }
    uri
}

pub struct Client {
    child: Child,
    input: ChildStdin,
    messages: mpsc::Receiver<Result<Value, String>>,
    readers: Vec<JoinHandle<()>>,
    stderr: Arc<Mutex<String>>,
    trace: Vec<String>,
    pending: Vec<Value>,
    registrations: Vec<Value>,
    publications: Vec<Value>,
    next_id: u64,
    pub workspace: TempDir,
    pub capabilities: Value,
}

impl Client {
    pub fn start(fixture: &str) -> Self {
        let workspace = tempfile::Builder::new()
            .prefix("denotate lsp ")
            .tempdir()
            .unwrap();
        for entry in fs::read_dir(root().join("fixtures").join(fixture)).unwrap() {
            let entry = entry.unwrap();
            if entry.path().extension().is_some_and(|ext| ext == "den") {
                fs::copy(entry.path(), workspace.path().join(entry.file_name())).unwrap();
            }
        }
        let server = root().join("langium/dist/server.mjs");
        let executable = std::env::var("DENOTATE_LSP_COMMAND").unwrap_or_else(|_| "node".into());
        let args: Vec<String> = match std::env::var("DENOTATE_LSP_ARGS") {
            Ok(args) => {
                serde_json::from_str(&args).expect("DENOTATE_LSP_ARGS must be a JSON string array")
            }
            Err(_) => {
                assert!(
                    server.exists(),
                    "Run npm run build in frontend-prototype/langium first"
                );
                vec![server.to_string_lossy().into_owned(), "--stdio".into()]
            }
        };
        let mut child = Command::new(executable)
            .args(args)
            .env("DENOTATE_TEST_MODE", "1")
            .current_dir(workspace.path())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("launch LSP server");
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
        let error = child.stderr.take().unwrap();
        let (sender, messages) = mpsc::channel();
        let output_reader = thread::spawn(move || {
            let mut output = BufReader::new(output);
            loop {
                let frame = (|| -> Result<Value, String> {
                    let mut length = None;
                    loop {
                        let mut line = String::new();
                        if output.read_line(&mut line).map_err(|e| e.to_string())? == 0 {
                            return Err("server stdout closed".into());
                        }
                        if line == "\r\n" || line == "\n" {
                            break;
                        }
                        if let Some((key, value)) = line.split_once(':') {
                            if key.eq_ignore_ascii_case("Content-Length") {
                                length =
                                    Some(value.trim().parse::<usize>().map_err(|e| e.to_string())?);
                            }
                        }
                    }
                    let length = length.ok_or("missing Content-Length")?;
                    if length > 8 * 1024 * 1024 {
                        return Err("oversized LSP frame".into());
                    }
                    let mut bytes = vec![0; length];
                    output.read_exact(&mut bytes).map_err(|e| e.to_string())?;
                    serde_json::from_slice(&bytes).map_err(|e| e.to_string())
                })();
                let stop = frame.is_err();
                if sender.send(frame).is_err() || stop {
                    break;
                }
            }
        });
        let stderr = Arc::new(Mutex::new(String::new()));
        let error_buffer = stderr.clone();
        let error_reader = thread::spawn(move || {
            for line in BufReader::new(error).lines() {
                match line {
                    Ok(line) => {
                        let mut out = error_buffer.lock().unwrap();
                        out.push_str(&line);
                        out.push('\n');
                    }
                    Err(_) => break,
                }
            }
        });
        let mut client = Self {
            child,
            input,
            messages,
            readers: vec![output_reader, error_reader],
            stderr,
            trace: vec![],
            pending: vec![],
            registrations: vec![],
            publications: vec![],
            next_id: 1,
            workspace,
            capabilities: Value::Null,
        };
        let uri = file_uri(client.workspace.path());
        let initialized = client.request("initialize", json!({
            "processId": std::process::id(), "rootUri": uri,
            "workspaceFolders": [{"uri": uri, "name": "fixture"}],
            "capabilities": {
                "general": {"positionEncodings": ["utf-16"]},
                "workspace": {"workspaceFolders": true, "configuration": true,
                    "didChangeWatchedFiles": {"dynamicRegistration": true}},
                "textDocument": {
                    "documentSymbol": {"hierarchicalDocumentSymbolSupport": true},
                    "completion": {"completionItem": {"snippetSupport": false}},
                    "semanticTokens": {
                        "requests": {"full": true}, "tokenTypes": ["type", "variable", "function", "namespace", "parameter"],
                        "tokenModifiers": ["readonly"], "formats": ["relative"]
                    }
                }
            }
        }));
        client.capabilities = initialized["capabilities"].clone();
        client.notify("initialized", json!({}));
        client
    }

    fn send(&mut self, message: Value) {
        let body = serde_json::to_vec(&message).unwrap();
        self.trace.push(format!("> {message}"));
        write!(self.input, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.input.write_all(&body).unwrap();
        self.input.flush().unwrap();
    }

    pub fn notify(&mut self, method: &str, params: Value) {
        self.send(json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    fn wait(&mut self, predicate: impl Fn(&Value) -> bool) -> Value {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            if let Some(index) = self.pending.iter().position(&predicate) {
                return self.pending.remove(index);
            }
            let message = self
                .messages
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .expect("LSP timed out; protocol trace follows")
                .expect("LSP framing/connection failure");
            self.trace.push(format!("< {message}"));
            if message["method"] == "textDocument/publishDiagnostics" {
                self.publications.push(message["params"].clone());
            }
            if message.get("id").is_some() && message.get("method").is_some() {
                let method = message["method"].as_str().unwrap();
                let result = match method {
                    "workspace/configuration" => Value::Array(
                        message["params"]["items"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .map(|_| json!({}))
                            .collect(),
                    ),
                    "workspace/workspaceFolders" => {
                        json!([{"uri": file_uri(self.workspace.path()), "name": "fixture"}])
                    }
                    "client/registerCapability" => {
                        self.registrations.extend(
                            message["params"]["registrations"]
                                .as_array()
                                .unwrap()
                                .clone(),
                        );
                        Value::Null
                    }
                    "client/unregisterCapability" | "window/workDoneProgress/create" => Value::Null,
                    other => panic!("Unhandled server request: {other}"),
                };
                self.send(json!({"jsonrpc": "2.0", "id": message["id"], "result": result}));
                if predicate(&message) {
                    return message;
                }
            } else if predicate(&message) {
                return message;
            } else {
                self.pending.push(message);
            }
        }
    }

    pub fn request(&mut self, method: &str, params: Value) -> Value {
        let reply = self.request_reply(method, params);
        assert!(reply.get("error").is_none(), "{method}: {reply}");
        reply["result"].clone()
    }

    pub fn request_reply(&mut self, method: &str, params: Value) -> Value {
        let id = self.begin_request(method, params);
        self.await_reply(id)
    }

    #[allow(dead_code)]
    pub fn begin_request(&mut self, method: &str, params: Value) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        id
    }

    #[allow(dead_code)]
    pub fn await_reply(&mut self, id: u64) -> Value {
        // Server and client request IDs have independent namespaces.
        let reply = self.wait(|message| message["id"] == id && message.get("method").is_none());
        reply
    }

    #[allow(dead_code)]
    pub fn notification(&mut self, method: &str) -> Value {
        self.wait(|m| m["method"] == method)["params"].clone()
    }

    #[allow(dead_code)]
    pub fn publications(&self) -> &[Value] {
        &self.publications
    }

    pub fn open(&mut self, file: &str) -> (String, String) {
        let path = self.workspace.path().join(file);
        let source = fs::read_to_string(&path).unwrap();
        let uri = file_uri(&path);
        self.discard_diagnostics(&uri);
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument": {
                "uri": uri, "languageId": "denotate", "version": 1, "text": source
            }}),
        );
        self.validated(&uri, 1);
        (uri, source)
    }

    pub fn validated(&mut self, uri: &str, version: i64) {
        self.wait(|m| {
            m["method"] == "denotate/test/validated"
                && m["params"]["uri"] == uri
                && m["params"]["version"] == version
        });
        // The test protocol requires a fresh full publication, even unchanged.
        // Older cached diagnostics were discarded before sending the edit/open.
        self.diagnostics(uri);
    }

    fn discard_diagnostics(&mut self, uri: &str) {
        self.pending.retain(|m| {
            !(m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri)
        });
    }

    pub fn diagnostics(&self, uri: &str) -> Value {
        self.pending
            .iter()
            .rev()
            .find(|m| m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri)
            .expect("server must publish fresh diagnostics after open/change and before its validation barrier, even when unchanged")["params"]["diagnostics"]
            .clone()
    }

    pub fn change(&mut self, uri: &str, version: i64, text: &str) {
        self.change_without_waiting(uri, version, text);
        self.validated(uri, version);
    }

    #[allow(dead_code)]
    pub fn change_without_waiting(&mut self, uri: &str, version: i64, text: &str) {
        self.discard_diagnostics(uri);
        self.notify(
            "textDocument/didChange",
            json!({
                "textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": text}]
            }),
        );
    }

    pub fn shutdown(&mut self) {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
    }

    #[allow(dead_code)] // Used by the resolution integration binary, not editor.rs.
    pub fn file_watcher_registration(&mut self) -> Value {
        if !self
            .registrations
            .iter()
            .any(|r| r["method"] == "workspace/didChangeWatchedFiles")
        {
            self.wait(|m| {
                m["method"] == "client/registerCapability"
                    && m["params"]["registrations"].as_array().is_some_and(|rs| {
                        rs.iter()
                            .any(|r| r["method"] == "workspace/didChangeWatchedFiles")
                    })
            });
        }
        self.registrations
            .iter()
            .find(|r| r["method"] == "workspace/didChangeWatchedFiles")
            .unwrap()
            .clone()
    }

    #[allow(dead_code)] // Used by the resolution integration binary, not editor.rs.
    pub fn watched_change(&mut self, file: &str, kind: u32, dependent_uri: &str, version: i64) {
        let changed_uri = file_uri(&self.workspace.path().join(file));
        self.discard_diagnostics(dependent_uri);
        // Also require a fresh publication when asserting deletion clears the
        // changed file's diagnostics; do not reuse an earlier empty result.
        self.discard_diagnostics(&changed_uri);
        self.pending.retain(|m| {
            !(m["method"] == "denotate/test/validated" && m["params"]["uri"] == dependent_uri)
        });
        self.notify(
            "workspace/didChangeWatchedFiles",
            json!({"changes": [{
                "uri": changed_uri, "type": kind
            }]}),
        );
        // Disk changes do not increment the dependent editor document version.
        // Serialized events still require a fresh diagnostic/build publication.
        self.validated(dependent_uri, version);
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        // Always reap, including after a failed assertion or timed-out response.
        let _ = self.child.kill();
        let _ = self.child.wait();
        for reader in self.readers.drain(..) {
            let _ = reader.join();
        }
        if thread::panicking() {
            eprintln!(
                "LSP stderr:\n{}\nProtocol:\n{}",
                self.stderr.lock().unwrap(),
                self.trace.join("\n")
            );
        }
    }
}
