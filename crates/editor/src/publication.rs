//! Versioned diagnostic publication and withdrawal on lost synchronization.
//! Diagnostic content and dependent-file republication belong to the frontend.
use crate::{
    transport::{send, Result},
    Documents,
};
use lsp_server::Connection;
use lsp_types::{Diagnostic, Url};
use serde_json::json;

pub const OUT_OF_SYNC: &str = "Document out of sync; reopen or send full text";

pub fn publish(
    connection: &Connection,
    uri: &Url,
    version: Option<i32>,
    diagnostics: Vec<Diagnostic>,
) -> Result<()> {
    let mut params = json!({"uri": uri, "diagnostics": diagnostics});
    if let Some(version) = version {
        params["version"] = json!(version);
    }
    send(connection, "textDocument/publishDiagnostics", params)
}
pub fn withdraw(connection: &Connection, uri: &Url) -> Result<()> {
    publish(connection, uri, None, vec![])
}
/// Withdraw only on the first sync failure. Repeated failures advance the
/// rejected version without publishing an unverified version or ready barrier.
pub fn lose_sync<D>(
    connection: &Connection,
    documents: &mut Documents<D>,
    uri: &Url,
    version: i32,
) -> Result<()> {
    if documents.lose_sync(uri, version) {
        withdraw(connection, uri)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_server::Message;
    #[test]
    fn lost_sync_withdraws_once_without_a_version_and_advances_recovery_version() {
        let (server, client) = Connection::memory();
        let uri = Url::parse("file:///source").unwrap();
        let mut documents: Documents<()> = Documents::default();
        documents.insert(uri.clone(), ());
        lose_sync(&server, &mut documents, &uri, 4).unwrap();
        lose_sync(&server, &mut documents, &uri, 7).unwrap();
        let Message::Notification(n) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(n.method, "textDocument/publishDiagnostics");
        assert_eq!(n.params, json!({"uri":uri,"diagnostics":[]}));
        assert_eq!(documents.rejected_version(&uri), Some(7));
        assert!(client.receiver.try_recv().is_err());
        documents.insert(uri.clone(), ());
        publish(&server, &uri, Some(8), vec![]).unwrap();
        let Message::Notification(n) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(n.params["version"], 8);
        assert!(!documents.has_out_of_sync());
    }
}
