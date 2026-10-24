//! Authoritative origin snapshots come only from an opted-in editor client.
use crate::syntax::Document;
use denotate_editor::transport::{send, Result};
use denotate_ir_text::origins::content_hash;
use lsp_server::{Connection, Message, Request, Response};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
#[derive(Clone, Default)]
pub struct Bridge {
    pub enabled: bool,
    known: BTreeMap<String, BTreeSet<String>>,
    files: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
    epochs: BTreeMap<String, u64>,
    pending: BTreeMap<String, (String, u64)>,
    snapshots: BTreeMap<String, Value>,
    serial: u64,
}
impl Bridge {
    pub fn observe(&mut self, uri: &str, doc: &Document) {
        fn visit(
            node: tree_sitter::Node,
            text: &str,
            known: &mut BTreeMap<String, BTreeSet<String>>,
        ) {
            if node.kind() == "source_location" {
                let value = |field| {
                    node.child_by_field_name(field)
                        .and_then(|n| serde_json::from_str::<String>(&text[n.byte_range()]).ok())
                };
                if let (Some(uri), Some(hash)) = (value("uri"), value("hash")) {
                    known.entry(uri).or_default().insert(hash);
                }
            }
            for child in node.named_children(&mut node.walk()) {
                visit(child, text, known);
            }
        }
        let mut known = BTreeMap::new();
        visit(doc.tree.root_node(), &doc.text, &mut known);
        self.files.insert(uri.into(), known);
    }
    pub fn remove(&mut self, uri: &str) {
        self.files.remove(uri);
    }
    pub fn update(&mut self, connection: &Connection) -> Result<()> {
        let mut known: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for file in self.files.values() {
            for (uri, hashes) in file {
                known
                    .entry(uri.clone())
                    .or_default()
                    .extend(hashes.iter().cloned());
            }
        }
        if known == self.known {
            return Ok(());
        }
        self.known = known;
        self.snapshots.retain(|u, _| self.known.contains_key(u));
        self.pending.retain(|_, (u, _)| self.known.contains_key(u));
        send(
            connection,
            "denotate/originSubscriptions",
            json!({"uris":self.known.keys().collect::<Vec<_>>()}),
        )?;
        for uri in self.known.keys().cloned().collect::<Vec<_>>() {
            self.fetch(connection, &uri)?;
        }
        Ok(())
    }
    fn fetch(&mut self, connection: &Connection, uri: &str) -> Result<()> {
        self.snapshots.remove(uri);
        if !self.enabled {
            return Ok(());
        }
        self.serial += 1;
        let id = format!("origin-{}", self.serial);
        let epoch = self.epochs.entry(uri.into()).or_default();
        *epoch += 1;
        let epoch = *epoch;
        self.pending.insert(id.clone(), (uri.into(), epoch));
        connection.sender.send(Message::Request(Request::new(
            id.into(),
            "denotate/originSnapshot".into(),
            json!({"uri":uri}),
        )))?;
        Ok(())
    }
    pub fn invalidate(&mut self, connection: &Connection, params: &Value) -> Result<()> {
        if let Some(uri) = params["uri"]
            .as_str()
            .filter(|u| self.known.contains_key(*u))
        {
            *self.epochs.entry(uri.into()).or_default() += 1;
            self.fetch(connection, uri)?;
        }
        Ok(())
    }
    pub fn response(&mut self, response: Response) {
        let Some(id) = serde_json::to_value(response.id)
            .ok()
            .and_then(|v| v.as_str().map(str::to_owned))
        else {
            return;
        };
        let Some((uri, epoch)) = self.pending.remove(&id) else {
            return;
        };
        if self.epochs.get(&uri).copied().unwrap_or_default() != epoch
            || !self.known.contains_key(&uri)
        {
            return;
        }
        let snapshot = response.result.filter(|v| {
            v["uri"] == uri
                && v["text"].is_string()
                && v["open"].is_boolean()
                && v["dirty"].is_boolean()
                && v["generation"].is_number()
        });
        if let Some(mut snapshot) = snapshot {
            snapshot["hash"] = json!(content_hash(snapshot["text"].as_str().unwrap()));
            self.snapshots.insert(uri, snapshot);
        }
    }
    pub fn snapshot_key(&self, members: &[String]) -> Value {
        let uris = members
            .iter()
            .filter_map(|u| self.files.get(u))
            .flat_map(|f| f.keys())
            .collect::<BTreeSet<_>>();
        json!(uris
            .into_iter()
            .map(|u| (u, (self.epochs.get(u), self.snapshots.get(u))))
            .collect::<BTreeMap<_, _>>())
    }
    pub fn settled(&self) -> bool {
        !self
            .pending
            .values()
            .any(|(u, e)| self.epochs.get(u) == Some(e))
    }
    pub fn status(&self, uri: &str) -> Value {
        let Some(expected) = self.known.get(uri) else {
            return json!({"state":"unknown"});
        };
        let Some(snapshot) = self.snapshots.get(uri) else {
            return json!({"state":"unavailable","reason":if self.enabled {"No authoritative snapshot"} else {"Client does not support the origin snapshot bridge"}});
        };
        json!({"state":if expected.contains(snapshot["hash"].as_str().unwrap()) {"matching"} else {"hash-mismatch"},"snapshot":snapshot,"expectedHashes":expected})
    }
}
impl denotate_ir_text::origins::OriginResolver for &Bridge {
    fn resolve(
        &mut self,
        source: &denotate_ir_text::origins::SourceIdentity,
    ) -> std::result::Result<std::sync::Arc<str>, denotate_ir_text::origins::Unavailable> {
        use denotate_ir_text::origins::Unavailable;
        let snapshot = self
            .snapshots
            .get(&source.uri)
            .ok_or(Unavailable::NoResolver)?;
        if snapshot["hash"] != source.hash {
            return Err(Unavailable::HashMismatch);
        }
        Ok(snapshot["text"].as_str().unwrap().into())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stale_responses_and_failed_lookups_never_restore_disk_authority() {
        let (server, client) = Connection::memory();
        let mut b = Bridge {
            enabled: true,
            ..Bridge::default()
        };
        b.known.insert(
            "file:///origin.dsl".into(),
            BTreeSet::from([content_hash("saved")]),
        );
        b.fetch(&server, "file:///origin.dsl").unwrap();
        let Message::Request(first) = client.receiver.recv().unwrap() else {
            panic!()
        };
        b.invalidate(&server, &json!({"uri":"file:///origin.dsl"}))
            .unwrap();
        let Message::Request(second) = client.receiver.recv().unwrap() else {
            panic!()
        };
        let snapshot = |text| json!({"uri":"file:///origin.dsl","text":text,"open":true,"dirty":true,"generation":2});
        b.response(Response::new_ok(second.id, snapshot("dirty")));
        b.response(Response::new_ok(first.id, snapshot("saved")));
        assert_eq!(b.status("file:///origin.dsl")["state"], "hash-mismatch");
        b.invalidate(&server, &json!({"uri":"file:///origin.dsl"}))
            .unwrap();
        let Message::Request(third) = client.receiver.recv().unwrap() else {
            panic!()
        };
        b.response(Response::new_err(
            third.id,
            -32603,
            "client unavailable".into(),
        ));
        assert_eq!(b.status("file:///origin.dsl")["state"], "unavailable");
        b.fetch(&server, "file:///origin.dsl").unwrap();
        let Message::Request(fourth) = client.receiver.recv().unwrap() else {
            panic!()
        };
        b.response(Response::new_ok(fourth.id, snapshot("saved")));
        assert_eq!(b.status("file:///origin.dsl")["state"], "matching"); // dirty alone is not a mismatch
        let mut resolver = &b;
        let source = denotate_ir_text::origins::SourceIdentity {
            uri: "file:///origin.dsl".into(),
            view: "dsl".into(),
            hash: content_hash("saved"),
        };
        assert_eq!(
            &*denotate_ir_text::origins::OriginResolver::resolve(&mut resolver, &source).unwrap(),
            "saved"
        );
    }
}
