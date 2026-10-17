//! Test-only wire protocol shared by frontend servers. Call only in test mode.
//! The caller owns readiness: validated follows a fresh full publication (even
//! when unchanged), and idle is answered only after prior work is handled. B is
//! serial; a future worker-based frontend must wait without blocking its loop.
use crate::transport::{send, Result};
use lsp_server::Connection;
use lsp_types::Url;
use serde_json::json;

pub const IDLE: &str = "denotate/test/idle";
pub const VALIDATED: &str = "denotate/test/validated";

pub fn validated(connection: &Connection, uri: &Url, version: i32) -> Result<()> {
    send(
        connection,
        VALIDATED,
        json!({"uri": uri, "version": version}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_server::Message;

    #[test]
    fn barrier_keeps_the_existing_method_payload_and_publication_order() {
        let (server, client) = Connection::memory();
        let uri = Url::parse("file:///anything.inputmapping").unwrap();
        send(
            &server,
            "textDocument/publishDiagnostics",
            json!({
                "uri": uri, "version": 7, "diagnostics": []
            }),
        )
        .unwrap();
        validated(&server, &uri, 7).unwrap();
        let Message::Notification(publication) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(publication.method, "textDocument/publishDiagnostics");
        let Message::Notification(barrier) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(barrier.method, "denotate/test/validated");
        assert_eq!(barrier.params, json!({"uri": uri, "version": 7}));
        assert_eq!(IDLE, "denotate/test/idle");
        assert!(client.receiver.try_recv().is_err());
    }
}
