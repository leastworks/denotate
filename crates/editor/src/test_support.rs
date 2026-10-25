//! Test-only wire protocol shared by frontend servers. Call only in test mode.
//! The caller owns readiness: validated follows a fresh full publication (even
//! when unchanged). Checking-idle additionally waits for the scheduler and any
//! frontend readiness gate, without blocking incoming messages.
use crate::transport::{send, Result};
use lsp_server::Connection;
use lsp_types::Url;
use serde_json::json;

pub const CHECKING_IDLE: &str = "denotate/test/checkingIdle";
pub const HOLD: &str = "denotate/test/hold";
pub const RELEASE: &str = "denotate/test/release";
pub const RESET_CHECKS: &str = "denotate/test/resetChecks";
pub const CHECKING_STATS: &str = "denotate/test/checkingStats";
pub const CHECKPOINT: &str = "denotate/test/checkpoint";
pub const CHECKED: &str = "denotate/test/checked";

/// Only populated in test mode. Record payloads belong to the frontend.
#[derive(Default)]
pub struct CheckingHooks {
    pub started: Vec<serde_json::Value>,
    pub finished: Vec<serde_json::Value>,
    pub(crate) idle: Vec<lsp_server::RequestId>,
}
impl CheckingHooks {
    pub(crate) fn cancel_idle(
        &mut self,
        connection: &Connection,
        id: &serde_json::Value,
    ) -> Result<()> {
        if let Some(i) = self.idle.iter().position(|pending| json!(pending) == *id) {
            connection.sender.send(lsp_server::Message::Response(
                lsp_server::Response::new_err(
                    self.idle.remove(i),
                    -32800,
                    "Request cancelled".into(),
                ),
            ))?;
        }
        Ok(())
    }
    pub(crate) fn answer_idle(&mut self, connection: &Connection) -> Result<()> {
        for id in self.idle.drain(..) {
            connection
                .sender
                .send(lsp_server::Message::Response(lsp_server::Response::new_ok(
                    id,
                    serde_json::Value::Null,
                )))?;
        }
        Ok(())
    }
}

pub const IDLE: &str = "denotate/test/idle";
pub const VALIDATED: &str = "denotate/test/validated";
pub const FRONTEND_READY: &str = "denotate/test/frontendReady";

/// Async frontends send this after withdrawing old semantic findings. It does
/// not replace validated, which follows the final publication for the snapshot.
pub fn frontend_ready(connection: &Connection, uri: &Url, version: i32) -> Result<()> {
    send(
        connection,
        FRONTEND_READY,
        json!({"uri": uri, "version": version}),
    )
}

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

    #[test]
    fn async_frontend_ready_is_a_distinct_versioned_barrier() {
        let (server, client) = Connection::memory();
        let uri = Url::parse("file:///example.inputmapping").unwrap();
        frontend_ready(&server, &uri, 4).unwrap();
        let Message::Notification(n) = client.receiver.try_recv().unwrap() else {
            panic!()
        };
        assert_eq!(n.method, FRONTEND_READY);
        assert_ne!(n.method, VALIDATED);
        assert_eq!(n.params, json!({"uri": uri, "version": 4}));
    }
}
