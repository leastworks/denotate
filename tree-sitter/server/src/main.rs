mod bridge;
mod catalog;
mod checking;
mod formatting;
mod presentation;
mod rename;
mod semantic;
mod syntax;
mod timing;

use denotate_editor::{
    test_support,
    transport::{self, send, Result},
    Documents,
};
use lsp_server::{Connection, Message, Notification, Request, ResponseError};
use lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, DocumentSymbolParams, FileChangeType,
    InitializeParams, TextDocumentPositionParams, Url,
};
use serde_json::{json, Value};
use std::{collections::HashMap, error::Error, fs, path::PathBuf};
use syntax::Document;

struct Server {
    parser: tree_sitter::Parser,
    documents: Documents<Document>,
    roots: Vec<PathBuf>,
    test_mode: bool,
    semantics: semantic::Semantics,
    diagnostics: HashMap<Url, Vec<Diagnostic>>,
    diagnostics_dirty: bool,
    catalog: catalog::Catalog,
    bridge: bridge::Bridge,
    checking: checking::Checking,
    observations: HashMap<Url, u64>,
    observation: u64,
}

impl Server {
    fn canonical_document(uri: &Url) -> String {
        uri.to_file_path()
            .ok()
            .map(|p| catalog::uri(&p))
            .unwrap_or_else(|| uri.to_string())
    }
    fn refresh_memberships(&mut self) {
        self.catalog.refresh(
            &self.roots,
            self.documents
                .iter()
                .filter(|(_, d)| d.open)
                .filter_map(|(u, _)| u.to_file_path().ok()),
        );
        let removed = self
            .documents
            .iter()
            .filter(|(u, d)| {
                !d.open
                    && u.to_file_path()
                        .is_ok_and(|p| !self.catalog.files.contains(&catalog::identity(&p)))
            })
            .map(|(u, _)| u.clone())
            .collect::<Vec<_>>();
        for uri in removed {
            self.remove(&uri);
        }
        let files = self.catalog.files.clone();
        for path in files {
            let canonical = catalog::uri(&path);
            let known = self
                .documents
                .keys()
                .any(|u| Self::canonical_document(u) == canonical);
            if !known {
                // Keep client workspace spelling for all positions and edits.
                let path = self
                    .roots
                    .iter()
                    .find_map(|root| {
                        path.strip_prefix(catalog::identity(root))
                            .ok()
                            .map(|rel| root.join(rel))
                    })
                    .unwrap_or(path);
                if let Ok(uri) = Url::from_file_path(path) {
                    let _ = self.read_disk(&uri);
                }
            }
        }
        self.refresh_contexts();
    }
    fn refresh_contexts(&mut self) {
        let aliases: HashMap<_, _> = self
            .documents
            .keys()
            .map(|u| (Self::canonical_document(u), u.to_string()))
            .collect();
        let mut programs = vec![];
        // Reset member failures from the retained manifest graph on every edit.
        for (root, program) in &self.catalog.programs {
            let mut syntax_errors = vec![];
            let mut errors = program
                .roots
                .keys()
                .flat_map(|r| self.catalog.nodes[r].errors.clone())
                .collect::<Vec<_>>();
            for canonical in program.roots.values().flat_map(|r| &r.files) {
                if self.catalog.home(canonical).is_none() {
                    errors.push(format!(
                        "{canonical}: membership does not establish a unique home program"
                    ));
                }
                let actual = aliases.get(canonical).unwrap_or(canonical);
                let uri = Url::parse(actual).unwrap();
                match self.documents.get(&uri) {
                    None => errors.push(format!("{canonical}: member unavailable")),
                    Some(_) if self.documents.rejected_version(&uri).is_some() => {
                        errors.push(format!("{canonical}: document out of sync"))
                    }
                    Some(doc) if !doc.diagnostics().is_empty() => {
                        syntax_errors.push(format!("{canonical}: invalid member syntax"))
                    }
                    _ => {}
                }
            }
            self.catalog.errors.insert(root.clone(), errors);
            self.catalog
                .syntax_errors
                .insert(root.clone(), syntax_errors);
            let mut program = program.clone();
            for node in program.roots.values_mut() {
                node.files = node
                    .files
                    .iter()
                    .map(|u| aliases.get(u).cloned().unwrap_or_else(|| u.clone()))
                    .collect();
            }
            programs.push(program);
        }
        self.semantics.memberships(&programs);
        for uri in self.documents.keys() {
            let canonical = Self::canonical_document(uri);
            let status = self.catalog.status(&canonical);
            if status["state"] == "standalone" {
                self.semantics.set_context(uri, Some(uri.to_string()));
            } else {
                self.semantics
                    .set_context(uri, self.catalog.context(&canonical));
            }
        }
        self.diagnostics_dirty = true;
    }
    fn root_status(&self, uri: &Url) -> Value {
        let mut status = self.catalog.status(&Self::canonical_document(uri));
        status["uri"] = json!(uri);
        if status["state"] == "standalone" {
            let mut errors = self
                .diagnostics
                .get(uri)
                .into_iter()
                .flatten()
                .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
                .map(|d| d.message.clone())
                .collect::<Vec<_>>();
            if self.documents.rejected_version(uri).is_some() {
                errors = vec!["Document out of sync; reopen or send full text".into()];
            }
            status["errors"] = json!(errors);
        }
        let root = status["homeProgram"]
            .as_str()
            .unwrap_or(uri.as_str())
            .to_owned();
        self.checking.status(&root, &mut status);
        status
    }
    fn program_status(&self, root: &str) -> Value {
        let mut status = self.catalog.program_status(root);
        self.checking.status(root, &mut status);
        status
    }
    fn announce(&mut self, connection: &Connection) -> Result<()> {
        let watch = self
            .catalog
            .nodes
            .keys()
            .filter_map(|s| {
                Url::parse(s)
                    .ok()?
                    .to_file_path()
                    .ok()?
                    .parent()
                    .map(|p| catalog::uri(p))
            })
            .collect::<Vec<_>>();
        if self.bridge.enabled {
            send(
                connection,
                "denotate/rootsChanged",
                json!({"watchFolders":watch}),
            )?;
        }
        self.bridge.update(connection)?;
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
        self.catalog.resolution_errors.clear();
        let aliases: HashMap<_, _> = self
            .documents
            .keys()
            .map(|u| (Self::canonical_document(u), u.clone()))
            .collect();
        // Every root is a program, including library roots. Inspect its entire
        // membership, while keeping normal publication in user-owned files.
        for (root, program) in &self.catalog.programs {
            if !self.catalog.errors[root].is_empty() {
                continue;
            }
            let own = &program.roots[root].files;
            let mut failures = vec![];
            let members = program
                .roots
                .values()
                .flat_map(|r| r.files.iter())
                .collect::<std::collections::BTreeSet<_>>();
            for canonical in members {
                let Some(uri) = aliases.get(canonical) else {
                    continue;
                };
                let Some(doc) = self.documents.get(uri) else {
                    continue;
                };
                for issue in self.semantics.core.diagnostics(root, uri.as_str()) {
                    if issue.warning {
                        continue;
                    }
                    failures.push(format!("{canonical}: {}", issue.message));
                    if own.contains(canonical) || issue.code != "resolution" {
                        continue;
                    }
                    // A consumer can introduce ambiguity in a library's namespace.
                    // Attribute that failure to its conflicting user declarations,
                    // never to the library's otherwise unaffected home view.
                    let Some(reference) = self.semantics.reference_at(uri, issue.span.start) else {
                        continue;
                    };
                    let candidates = self.semantics.core.candidates(
                        root,
                        uri.as_str(),
                        &reference.scope,
                        &reference.lookup,
                        Some(&reference.name),
                    );
                    if candidates.len() < 2 {
                        continue;
                    }
                    for candidate in candidates {
                        let Ok(target_uri) = Url::parse(&candidate.uri) else {
                            continue;
                        };
                        let target_canonical = Self::canonical_document(&target_uri);
                        if !own.contains(&target_canonical)
                            || self.catalog.home(&target_canonical).as_ref() != Some(root)
                        {
                            continue;
                        }
                        let target = semantic::Target {
                            uri: target_uri.clone(),
                            rule: None,
                            id: candidate.id,
                        };
                        let Some(span) = self.semantics.target_span(&target) else {
                            continue;
                        };
                        let Some(target_doc) = self.documents.get(&target_uri) else {
                            continue;
                        };
                        let mut diagnostic = semantic::diagnostic(doc, &issue);
                        let related = lsp_types::DiagnosticRelatedInformation {
                            location: lsp_types::Location {
                                uri: uri.clone(),
                                range: diagnostic.range,
                            },
                            message: "Library reference fails in this consumer program".into(),
                        };
                        diagnostic.range = lsp_types::Range::new(
                            target_doc.position(span.start),
                            target_doc.position(span.end),
                        );
                        diagnostic.message = format!("In {root}: {}", issue.message);
                        diagnostic.related_information = Some(vec![related]);
                        self.diagnostics
                            .entry(target_uri)
                            .or_default()
                            .push(diagnostic);
                    }
                }
            }
            failures.sort();
            failures.dedup();
            self.catalog
                .resolution_errors
                .insert(root.clone(), failures);
        }
        self.diagnostics_dirty = false;
    }

    fn publish(&mut self, connection: &Connection, uri: &Url) -> Result<()> {
        if self.documents.rejected_version(uri).is_some() {
            return Ok(());
        }
        self.refresh_diagnostics();
        if let Some(doc) = self.documents.get(uri) {
            send(
                connection,
                "textDocument/publishDiagnostics",
                json!({
                    "uri": uri, "version": doc.version, "diagnostics": self.diagnostics[uri].iter().cloned().chain(self.checking.diagnostics(uri)).collect::<Vec<_>>()
                }),
            )?;
        } else {
            send(
                connection,
                "textDocument/publishDiagnostics",
                json!({"uri": uri, "diagnostics": []}),
            )?;
        }
        Ok(())
    }

    fn publish_all(&mut self, connection: &Connection) -> Result<()> {
        self.refresh_contexts();
        self.announce(connection)?;
        self.sync_checks()?;
        // Refresh all indexed dependents. Salsa reuses unchanged semantics;
        // selective publication/scheduling is not claimed by this prototype.
        let mut uris: Vec<_> = self
            .documents
            .keys()
            .filter(|u| self.documents.rejected_version(u).is_none())
            .cloned()
            .collect();
        uris.sort();
        for uri in &uris {
            self.publish(connection, uri)?;
        }
        // A barrier covers the entire update, including importer diagnostics.
        // Otherwise a caller waiting on the library can observe old importer
        // diagnostics that were still queued behind an earlier library barrier.
        if self.test_mode {
            for uri in uris {
                test_support::validated(connection, &uri, self.documents[&uri].version)?;
            }
        }
        self.announce(connection)?;
        Ok(())
    }

    fn store(&mut self, uri: Url, doc: Document) {
        self.observation += 1;
        self.observations.insert(uri.clone(), self.observation);
        let canonical = Self::canonical_document(&uri);
        let aliases = self
            .documents
            .keys()
            .filter(|old| *old != &uri && Self::canonical_document(old) == canonical)
            .cloned()
            .collect::<Vec<_>>();
        for alias in aliases {
            self.remove(&alias);
        }
        // A declaration change can invalidate diagnostics in any importer.
        self.diagnostics_dirty = true;
        self.semantics.update(&uri, &doc);
        self.bridge.observe(uri.as_str(), &doc);
        self.documents.insert(uri, doc);
    }

    fn remove(&mut self, uri: &Url) {
        self.observations.remove(uri);
        self.documents.remove(uri);
        self.semantics.remove(uri);
        self.bridge.remove(uri.as_str());
        self.diagnostics.remove(uri);
        self.diagnostics_dirty = true;
    }

    fn lose_sync(&mut self, connection: &Connection, uri: &Url, version: i32) -> Result<()> {
        let newly_lost = self.documents.lose_sync(uri, version);
        self.semantics.remove(uri);
        self.bridge.remove(uri.as_str());
        self.diagnostics.clear();
        self.diagnostics_dirty = true;
        if newly_lost {
            // Withdraw stale diagnostics, without claiming to have analyzed a
            // version of the now-unknown text or emitting a validation barrier.
            send(
                connection,
                "textDocument/publishDiagnostics",
                json!({"uri": uri, "diagnostics": []}),
            )?;
        }
        self.refresh_contexts();
        self.sync_checks()?;
        for other in self
            .documents
            .keys()
            .filter(|u| *u != uri)
            .cloned()
            .collect::<Vec<_>>()
        {
            self.publish(connection, &other)?;
        }
        self.announce(connection)?;
        Ok(())
    }

    fn read_disk(&mut self, uri: &Url) -> Result<()> {
        let path = uri.to_file_path().map_err(|_| "Expected a file URI")?;
        let path = path.canonicalize()?;
        if (!self
            .roots
            .iter()
            .any(|root| path.starts_with(catalog::identity(root)))
            && !self.catalog.files.contains(&path))
            || path.extension().is_none_or(|ext| ext != "den")
        {
            return Err("File is outside known Denotate roots".into());
        }
        let text = fs::read_to_string(path)?;
        // Match VS Code's disk-to-editor coordinate space without altering disk.
        let text = text.strip_prefix('\u{feff}').unwrap_or(&text).to_owned();
        let doc = Document::new(&mut self.parser, text, 0, false);
        self.store(uri.clone(), doc);
        Ok(())
    }

    fn request(&mut self, request: &Request) -> Result<Value> {
        let _timer = request
            .method
            .starts_with("textDocument/")
            .then(|| timing::interval("editorRequest"));
        if request.method.starts_with("textDocument/")
            && request.params["textDocument"]["uri"]
                .as_str()
                .and_then(|u| Url::parse(u).ok())
                .is_some_and(|u| self.documents.rejected_version(&u).is_some())
        {
            return Err("Document is out of sync; reopen it or send a full-text change.".into());
        }
        match request.method.as_str() {
            "denotate/roots" => {
                self.refresh_diagnostics();
                if let Some(uri) = request.params["uri"].as_str() {
                    Ok(self.root_status(&Url::parse(uri)?))
                } else {
                    let mut programs = self
                        .catalog
                        .programs
                        .keys()
                        .map(|r| self.program_status(r))
                        .collect::<Vec<_>>();
                    for uri in self.documents.keys() {
                        if self.catalog.status(&Self::canonical_document(uri))["state"]
                            == "standalone"
                        {
                            let mut status = self.root_status(uri);
                            status["program"] = json!(uri);
                            programs.push(status);
                        }
                    }
                    Ok(json!({"programs":programs}))
                }
            }
            "denotate/originStatus" => Ok(self
                .bridge
                .status(request.params["uri"].as_str().ok_or("Missing uri")?)),
            "textDocument/codeAction" => {
                let uri = Url::parse(
                    request.params["textDocument"]["uri"]
                        .as_str()
                        .ok_or("Missing uri")?,
                )?;
                Ok(if self.root_status(&uri)["state"] == "standalone" {
                    json!([{"title":"Create den.root here","kind":"quickfix","command":{"title":"Create den.root here","command":"denotate.createRoot","arguments":[uri]}},{"title":"Create den.root in another folder…","kind":"quickfix","command":{"title":"Choose root folder","command":"denotate.createRoot","arguments":[uri,null,true]}}])
                } else {
                    json!([])
                })
            }

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
            "denotate/test/analysis" if self.test_mode => {
                let mut result = self.semantics.stats();
                if let Some(timings) = timing::snapshot() {
                    result["timings"] = json!({"rust": timings});
                }
                Ok(result)
            }
            "denotate/test/profiling" if self.test_mode => {
                timing::reset(request.params.as_bool().ok_or("Expected boolean")?);
                Ok(Value::Null)
            }
            // Serial owner loop: all prior notification work is complete.
            test_support::IDLE if self.test_mode => Ok(Value::Null),
            _ => Err("Unsupported request".into()),
        }
    }

    fn notification(&mut self, connection: &Connection, notification: Notification) -> Result<()> {
        // Manifest snapshots use the filename-based full-text bridge, even if
        // the user has assigned the denotate language ID to a JSON manifest.
        if notification.method.starts_with("textDocument/")
            && notification.params["textDocument"]["uri"]
                .as_str()
                .and_then(|s| Url::parse(s).ok())
                .and_then(|u| u.to_file_path().ok())
                .is_some_and(|p| p.file_name().is_some_and(|n| n == "den.root"))
        {
            return Ok(());
        }
        match notification.method.as_str() {
            "denotate/manifest" => {
                let p = notification.params;
                let uri = Url::parse(p["uri"].as_str().ok_or("Missing manifest uri")?)?;
                let path = catalog::identity(&uri.to_file_path().map_err(|_| "Expected file URI")?);
                if path.file_name().is_none_or(|n| n != "den.root") {
                    return Err("Expected den.root".into());
                }
                if p["closed"] == true {
                    self.catalog.open.remove(&path);
                } else {
                    let version = p["version"].as_i64().ok_or("Missing manifest version")?;
                    if self
                        .catalog
                        .open
                        .get(&path)
                        .is_some_and(|m| m.version >= version)
                    {
                        return Ok(());
                    }
                    self.catalog.open.insert(
                        path,
                        catalog::Manifest {
                            text: p["text"].as_str().ok_or("Missing manifest text")?.into(),
                            version,
                        },
                    );
                }
                self.refresh_memberships();
                self.publish_all(connection)?;
            }
            "workspace/didChangeConfiguration" => {
                self.checking.config =
                    checking::Config::read(&notification.params["settings"]["denotate"])?;
                self.publish_all(connection)?;
            }
            "denotate/originChanged" => {
                self.bridge.invalidate(connection, &notification.params)?;
                self.publish_all(connection)?;
            }

            "textDocument/didOpen" => {
                let params: DidOpenTextDocumentParams =
                    serde_json::from_value(notification.params)?;
                let text = params.text_document;
                let new_document = !self.documents.contains_key(&text.uri);
                let doc = Document::new(&mut self.parser, text.text, text.version, true);
                self.store(text.uri, doc);
                if new_document {
                    self.refresh_memberships();
                }
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
                            if let Some((uri, version)) = self.documents.malformed_change(&metadata)
                            {
                                self.lose_sync(connection, &uri, version)?;
                            }
                            return Err(error.into());
                        }
                    };
                let uri = params.text_document.uri;
                let previous = self.documents.get(&uri).ok_or("Change before open")?;
                let changes = match self.documents.changes(
                    &uri,
                    params.text_document.version,
                    &params.content_changes,
                ) {
                    Ok(changes) => changes,
                    Err(error) => {
                        self.lose_sync(connection, &uri, params.text_document.version)?;
                        return Err(error.into());
                    }
                };
                if let Some(changes) = changes {
                    let changed =
                        previous.changed(&mut self.parser, changes, params.text_document.version);
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
                self.refresh_memberships();
                self.publish_all(connection)?;
            }
            "workspace/didChangeWorkspaceFolders" => {
                let event = &notification.params["event"];
                if let Some(removed) = event["removed"].as_array() {
                    for folder in removed {
                        if let Some(path) = folder["uri"]
                            .as_str()
                            .and_then(|u| Url::parse(u).ok())
                            .and_then(|u| u.to_file_path().ok())
                        {
                            self.roots
                                .retain(|r| catalog::identity(r) != catalog::identity(&path));
                        }
                    }
                }
                if let Some(added) = event["added"].as_array() {
                    for folder in added {
                        if let Some(path) = folder["uri"]
                            .as_str()
                            .and_then(|u| Url::parse(u).ok())
                            .and_then(|u| u.to_file_path().ok())
                        {
                            if !self
                                .roots
                                .iter()
                                .any(|r| catalog::identity(r) == catalog::identity(&path))
                            {
                                self.roots.push(path);
                            }
                        }
                    }
                }
                self.refresh_memberships();
                self.publish_all(connection)?;
            }
            "workspace/didChangeWatchedFiles" => {
                let params: DidChangeWatchedFilesParams =
                    serde_json::from_value(notification.params)?;
                let mut removed = vec![];
                for mut event in params.changes {
                    if event
                        .uri
                        .to_file_path()
                        .is_ok_and(|p| p.file_name().is_some_and(|n| n == "den.root"))
                    {
                        continue;
                    }
                    let canonical = Self::canonical_document(&event.uri);
                    if let Some(existing) = self
                        .documents
                        .keys()
                        .find(|u| Self::canonical_document(u) == canonical)
                    {
                        event.uri = existing.clone();
                    }
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
                self.refresh_memberships();
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

fn run(connection: &Connection) -> Result<()> {
    run_with_mode(
        connection,
        std::env::var("DENOTATE_TEST_MODE").as_deref() == Ok("1"),
    )
}
fn run_with_mode(connection: &Connection, test_mode: bool) -> Result<()> {
    let params = connection.initialize(json!({
        "workspace": {"workspaceFolders": {"supported": true,"changeNotifications": true}},
        "positionEncoding": "utf-16", "textDocumentSync": {"openClose": true, "change": 2},
        "documentSymbolProvider": true, "definitionProvider": true, "codeActionProvider": true,
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
        documents: Documents::default(),
        roots,
        test_mode,
        semantics: semantic::Semantics::default(),
        diagnostics: HashMap::new(),
        diagnostics_dirty: true,
        catalog: catalog::Catalog::default(),
        bridge: bridge::Bridge::default(),
        checking: checking::Checking::default(),
        observations: HashMap::new(),
        observation: 0,
    };
    server.bridge.enabled = params["initializationOptions"]["originSnapshotBridge"] == true;
    server.checking.config = checking::Config::read(&params["initializationOptions"]["denotate"])?;
    server.checking.enable(test_mode)?;
    server.refresh_memberships();
    // Bridge clients own workspace and external-root watchers. Other clients can
    // opt into standard registration; origin authority is never inferred from it.
    if !server.bridge.enabled
        && params["capabilities"]["workspace"]["didChangeWatchedFiles"]["dynamicRegistration"]
            == true
    {
        connection.sender.send(Message::Request(Request::new(1.into(), "client/registerCapability".into(), json!({
            "registrations": [{"id": "denotate-files", "method": "workspace/didChangeWatchedFiles",
                "registerOptions": {"watchers": [{"globPattern": "**/*.den", "kind": 7},{"globPattern":"**/den.root","kind":7}]}}]
        }))))?;
    }
    server.announce(connection)?;
    server.serve_checks(connection)
}

impl transport::Handler for Server {
    fn response(&mut self, _connection: &Connection, response: lsp_server::Response) -> Result<()> {
        self.bridge.response(response);
        Ok(())
    }
    fn supports_request(&self, method: &str) -> bool {
        matches!(
            method,
            "denotate/roots"
                | "denotate/originStatus"
                | "textDocument/codeAction"
                | "textDocument/documentSymbol"
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
        ) || (self.test_mode
            && matches!(
                method,
                test_support::IDLE | "denotate/test/analysis" | "denotate/test/profiling"
            ))
    }

    fn request(&mut self, request: &Request) -> std::result::Result<Value, ResponseError> {
        Server::request(self, request).map_err(|error| ResponseError {
            code: if self.documents.has_out_of_sync() {
                -32801
            } else {
                -32602
            },
            message: error.to_string(),
            data: None,
        })
    }

    fn notification(&mut self, connection: &Connection, notification: Notification) -> Result<()> {
        Server::notification(self, connection, notification)
    }
}

fn main() -> Result<()> {
    transport::stdio(run)
}

#[cfg(test)]
mod tests {
    use super::*;
    use denotate_editor::transport::{dispatch_request, receive_ready, take_cancellation};
    use std::collections::VecDeque;

    #[test]
    fn old_versions_and_invalid_ranges_cannot_replace_current_observation() {
        let mut server = Server {
            parser: syntax::parser(),
            documents: Documents::default(),
            roots: vec![],
            test_mode: true,
            semantics: semantic::Semantics::default(),
            diagnostics: HashMap::new(),
            diagnostics_dirty: true,
            catalog: catalog::Catalog::default(),
            bridge: bridge::Bridge::default(),
            checking: checking::Checking::default(),
            observations: HashMap::new(),
            observation: 0,
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
        assert_eq!(server.documents.rejected_version(&uri), Some(5));
        assert!(!server.semantics.files.contains_key(&uri));
        // An otherwise applicable subsequent range must not run on stale text.
        assert!(server.notification(&transport, Notification::new("textDocument/didChange".into(), json!({
            "textDocument": {"uri": uri, "version": 6}, "contentChanges": [{
                "range": {"start":{"line":0,"character":21},"end":{"line":0,"character":21}}, "text":"x"
            }]
        }))).is_err());
        assert_eq!(server.documents.rejected_version(&uri), Some(6));
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
        assert!(!server.documents.has_out_of_sync());
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
        assert_eq!(server.documents.rejected_version(&uri), Some(8));
        assert_withdrawal();
        server.notification(&transport, Notification::new("textDocument/didOpen".into(), json!({
            "textDocument":{"uri":uri,"version":1,"languageId":"denotate","text":"module example; sort Reopened;"}
        }))).unwrap();
        assert!(!server.documents.has_out_of_sync());
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
            documents: Documents::default(),
            roots: vec![],
            test_mode: false,
            semantics: semantic::Semantics::default(),
            diagnostics: HashMap::new(),
            diagnostics_dirty: true,
            catalog: catalog::Catalog::default(),
            bridge: bridge::Bridge::default(),
            checking: checking::Checking::default(),
            observations: HashMap::new(),
            observation: 0,
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
        server
            .semantics
            .memberships(&[denotate_ir_text::ProgramMembership::single(
                "explicit-test-root",
                [program.to_string(), library.to_string()],
            )]);
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

#[cfg(test)]
mod publication_tests;
