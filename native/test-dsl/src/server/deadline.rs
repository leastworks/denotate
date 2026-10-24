//! Exercise real worker interruption and editor publication without waiting 10 s.
use super::*;
use lsp_types::{DiagnosticSeverity, PublishDiagnosticsParams};
use std::time::Duration;

fn server() -> Server {
    Server {
        documents: Documents::default(),
        lowering: BTreeMap::new(),
        parser: syntax::parser().unwrap(),
        worker: worker::spawn().unwrap(),
        idle: vec![],
        tests: true,
        hooks: TestHooks::default(),
        shutdown: false,
        backend: denotate_check::BackendIdentity::bdd(),
    }
}
fn install(server: &mut Server, connection: &Connection, uri: &Url, version: i32) {
    let document = Document::new(
        &mut server.parser,
        "input i, j; slot a; a <- i; a <- j;".into(),
        version,
        true,
    );
    server.install(connection, uri.clone(), document).unwrap();
}
fn completed(server: &mut Server) -> Event {
    server.start_next().unwrap();
    server
        .worker
        .events()
        .recv_timeout(Duration::from_secs(5))
        .unwrap()
}
fn publications(client: &Connection) -> Vec<PublishDiagnosticsParams> {
    client
        .receiver
        .try_iter()
        .filter_map(|m| match m {
            Message::Notification(n) if n.method == "textDocument/publishDiagnostics" => {
                Some(serde_json::from_value(n.params).unwrap())
            }
            _ => None,
        })
        .collect()
}
fn stop(mut server: Server) {
    server.stop();
}

#[test]
fn deadline_publishes_an_operational_notice_and_success_clears_it() {
    let (connection, client) = Connection::memory();
    let mut server = server();
    let uri = Url::parse("file:///deadline.inputmapping").unwrap();
    install(&mut server, &connection, &uri, 1);
    publications(&client);
    server.worker.pending_limits_mut(&uri).unwrap().timeout = Duration::ZERO;
    let event = completed(&mut server);
    assert!(matches!(
        &event,
        Event::Finished(_, (Err(Failure::Deadline), _))
    ));
    server.completed(&connection, event).unwrap();
    let published = publications(&client);
    assert_eq!(published.len(), 1);
    assert_eq!(published[0].uri, uri);
    assert_eq!(published[0].version, Some(1));
    assert_eq!(published[0].diagnostics, vec![analysis::deadline_notice()]);
    assert_eq!(
        published[0].diagnostics[0].severity,
        Some(DiagnosticSeverity::INFORMATION)
    );
    assert!(
        published[0].diagnostics[0]
            .message
            .contains("results are incomplete")
    );
    assert_eq!(server.hooks.finished.last().unwrap()["status"], "deadline");
    assert!(server.hooks.finished.last().unwrap()["key_computation_ns"].is_null());

    install(&mut server, &connection, &uri, 2);
    publications(&client);
    server.worker.pending_limits_mut(&uri).unwrap().timeout = Duration::from_secs(60);
    let event = completed(&mut server);
    assert!(matches!(&event, Event::Finished(_, (Ok(_), _))));
    server.completed(&connection, event).unwrap();
    let published = publications(&client);
    assert_eq!(published.len(), 1);
    assert_eq!(published[0].version, Some(2));
    assert_eq!(published[0].diagnostics.len(), 2);
    assert!(published[0].diagnostics.iter().all(|d| d.code
        == Some(lsp_types::NumberOrString::String(
            "OverlappingMappings".into()
        ))));
    stop(server);
}

#[test]
fn stale_deadline_never_publishes_over_a_newer_document() {
    let (connection, client) = Connection::memory();
    let mut server = server();
    let uri = Url::parse("file:///deadline.inputmapping").unwrap();
    install(&mut server, &connection, &uri, 1);
    server.worker.pending_limits_mut(&uri).unwrap().timeout = Duration::ZERO;
    let event = completed(&mut server);
    assert!(matches!(
        &event,
        Event::Finished(_, (Err(Failure::Deadline), _))
    ));
    install(&mut server, &connection, &uri, 2);
    publications(&client);
    server.completed(&connection, event).unwrap();
    assert!(publications(&client).is_empty());
    assert_eq!(server.hooks.finished.last().unwrap()["status"], "discarded");
    stop(server);
}
