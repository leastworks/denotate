//! Bounded owner loop around the shared checking scheduler. Language handlers
//! own snapshots, freshness, diagnostic content and any external readiness gate.
use crate::{
    checking::{Event, HoldStage, Scheduler, Ticket},
    test_support::{self, CheckingHooks},
    transport::{self, Handler, Result},
};
use lsp_server::{Connection, Message, Request, Response};
use serde_json::{json, Value};
use std::collections::VecDeque;

pub trait CheckingHandler: Handler {
    type Key: Ord + Clone + Send + 'static;
    type Payload: Send + 'static;
    type Output: Send + 'static;
    type Metadata: Clone + Send + 'static;
    fn scheduler(
        &mut self,
    ) -> &mut Scheduler<Self::Key, Self::Payload, Self::Output, Self::Metadata>;
    fn hooks(&mut self) -> &mut CheckingHooks;
    fn test_mode(&self) -> bool;
    fn identity(ticket: &Ticket<Self::Key, Self::Metadata>) -> Value;
    fn completed(
        &mut self,
        connection: &Connection,
        event: Event<Self::Key, Self::Output, Self::Metadata>,
    ) -> Result<()>;
    fn before_start(&mut self, _connection: &Connection) -> Result<()> {
        Ok(())
    }
    fn started(&mut self, _ticket: &Ticket<Self::Key, Self::Metadata>) {}
    fn settled(&self) -> bool {
        true
    }
    fn reset_checks(&mut self, _connection: &Connection) -> Result<()> {
        Ok(())
    }
    fn extra_stats(&self) -> Value {
        json!({})
    }
    fn notification_error(
        &mut self,
        _connection: &Connection,
        error: Box<dyn std::error::Error>,
    ) -> Result<()> {
        eprintln!("notification rejected: {error}");
        Ok(())
    }
}

pub fn start_next<H: CheckingHandler>(handler: &mut H) -> Result<()> {
    if let Some(ticket) = handler.scheduler().start()? {
        if handler.test_mode() {
            let identity = H::identity(&ticket);
            handler.hooks().started.push(identity);
        }
        handler.started(&ticket);
    }
    Ok(())
}

fn test_request<H: CheckingHandler>(
    handler: &mut H,
    connection: &Connection,
    request: &Request,
) -> Result<bool> {
    if !handler.test_mode() {
        return Ok(false);
    }
    let result = match request.method.as_str() {
        test_support::CHECKING_IDLE => {
            handler.hooks().idle.push(request.id.clone());
            return Ok(true);
        }
        test_support::HOLD => match request.params.get("phase").and_then(Value::as_str) {
            None | Some("beforeResult") => {
                handler.scheduler().hold_next(HoldStage::BeforeResult);
                Ok(Value::Null)
            }
            Some("duringCheck") => {
                handler.scheduler().hold_next(HoldStage::DuringCheck);
                Ok(Value::Null)
            }
            _ => Err("Expected duringCheck or beforeResult"),
        },
        test_support::RELEASE => {
            if request.params["revision"]
                .as_u64()
                .is_some_and(|r| handler.scheduler().release(r))
            {
                Ok(Value::Null)
            } else {
                Err("No held result")
            }
        }
        test_support::RESET_CHECKS => {
            if !handler.scheduler().is_idle() {
                Err("Wait for checkingIdle before resetting sessions")
            } else {
                handler.scheduler().reset_sessions()?;
                handler.reset_checks(connection)?;
                Ok(Value::Null)
            }
        }
        test_support::CHECKING_STATS => {
            let pending = handler
                .scheduler()
                .pending()
                .map(|j| H::identity(&j.ticket))
                .collect::<Vec<_>>();
            let mut stats = handler.extra_stats();
            let hooks = handler.hooks();
            stats["started"] = json!(hooks.started);
            stats["finished"] = json!(hooks.finished);
            stats["pending"] = json!(pending);
            Ok(stats)
        }
        _ => return Ok(false),
    };
    connection.sender.send(Message::Response(match result {
        Ok(value) => Response::new_ok(request.id.clone(), value),
        Err(message) => Response::new_err(request.id.clone(), -32602, message.into()),
    }))?;
    Ok(true)
}

/// Stop/join on every exit path, including transport errors. Shutdown releases
/// held workers before the LSP shutdown/exit handshake waits for the client.
pub fn run(handler: &mut impl CheckingHandler, connection: &Connection) -> Result<()> {
    let result = run_inner(handler, connection);
    handler.scheduler().stop();
    result
}
fn run_inner<H: CheckingHandler>(handler: &mut H, connection: &Connection) -> Result<()> {
    let events = handler.scheduler().events().clone();
    let mut pending = VecDeque::new();
    handler.before_start(connection)?;
    loop {
        transport::receive_ready(connection, &mut pending);
        if pending.is_empty() {
            crossbeam_channel::select_biased! {
                recv(connection.receiver) -> m => match m { Ok(m) => pending.push_back(m), Err(_) => break },
                recv(events) -> e => handler.completed(connection, e.map_err(|_| "Checking worker stopped")?)?,
            }
        }
        for _ in 0..256 {
            let Some(message) = pending.pop_front() else {
                break;
            };
            match message {
                Message::Request(request) => {
                    if request.method == "shutdown" {
                        handler.scheduler().stop();
                    }
                    if connection.handle_shutdown(&request)? {
                        return Ok(());
                    }
                    if !test_request(handler, connection, &request)? {
                        transport::dispatch_request(handler, request, connection, &mut pending)?;
                    }
                }
                Message::Notification(n) if n.method == "exit" => return Ok(()),
                Message::Notification(n) => {
                    if n.method == "$/cancelRequest" {
                        handler.hooks().cancel_idle(connection, &n.params["id"])?;
                    }
                    if let Err(error) = handler.notification(connection, n) {
                        handler.notification_error(connection, error)?;
                    }
                }
                Message::Response(response) => handler.response(connection, response)?,
            }
        }
        // A bounded edit batch precedes completion, even under continuous traffic.
        if let Ok(event) = events.try_recv() {
            handler.completed(connection, event)?;
        }
        handler.before_start(connection)?;
        start_next(handler)?;
        if handler.scheduler().is_idle() && handler.settled() {
            handler.hooks().answer_idle(connection)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checking::Job;
    use denotate_check::Limits;
    use lsp_server::{Notification, ResponseError};
    use std::time::Duration;

    struct Owner {
        worker: Scheduler<String, (), ()>,
        hooks: CheckingHooks,
        edits: usize,
        completed_after: Vec<usize>,
    }
    impl Owner {
        fn new() -> Self {
            Self {
                worker: Scheduler::spawn("loop-test", |_, _, checkpoint| checkpoint()).unwrap(),
                hooks: CheckingHooks::default(),
                edits: 0,
                completed_after: vec![],
            }
        }
        fn enqueue(&mut self) {
            let ticket = self.worker.ticket("context".into(), ());
            self.worker.enqueue(Job {
                ticket,
                payload: (),
                limits: Limits::default(),
            });
        }
    }
    impl Handler for Owner {
        fn supports_request(&self, _: &str) -> bool {
            false
        }
        fn request(&mut self, _: &Request) -> std::result::Result<Value, ResponseError> {
            unreachable!()
        }
        fn notification(&mut self, _: &Connection, n: Notification) -> Result<()> {
            if n.method == "enqueue" {
                self.enqueue();
            } else {
                self.edits += 1;
            }
            Ok(())
        }
    }
    impl CheckingHandler for Owner {
        type Key = String;
        type Payload = ();
        type Output = ();
        type Metadata = ();
        fn scheduler(&mut self) -> &mut Scheduler<String, (), ()> {
            &mut self.worker
        }
        fn hooks(&mut self) -> &mut CheckingHooks {
            &mut self.hooks
        }
        fn test_mode(&self) -> bool {
            true
        }
        fn identity(ticket: &Ticket<String>) -> Value {
            json!({"revision":ticket.revision})
        }
        fn completed(&mut self, connection: &Connection, event: Event<String, ()>) -> Result<()> {
            match event {
                Event::Checkpoint(ticket) => transport::send(
                    connection,
                    test_support::CHECKPOINT,
                    Self::identity(&ticket),
                )?,
                Event::Finished(ticket, ()) => {
                    let edits = self.edits;
                    let current = self.worker.complete(&ticket, || edits == 0);
                    self.completed_after.push(edits);
                    self.hooks.finished.push(json!({"current":current}));
                }
            }
            Ok(())
        }
    }
    fn request(client: &Connection, id: i32, method: &str, params: Value) {
        client
            .sender
            .send(Message::Request(Request::new(
                id.into(),
                method.into(),
                params,
            )))
            .unwrap();
    }
    fn receive(client: &Connection) -> Message {
        client
            .receiver
            .recv_timeout(Duration::from_secs(5))
            .unwrap()
    }
    fn response(client: &Connection, id: i32) -> Response {
        let Message::Response(response) = receive(client) else {
            panic!("expected response")
        };
        assert_eq!(response.id, id.into());
        response
    }
    #[test]
    fn queued_edits_precede_results_but_a_full_batch_cannot_starve_completion() {
        let (server, client) = Connection::memory();
        let mut owner = Owner::new();
        owner.enqueue();
        start_next(&mut owner).unwrap();
        // Wait until a result is queued without consuming it.
        let mut select = crossbeam_channel::Select::new();
        select.recv(owner.worker.events());
        select.ready_timeout(Duration::from_secs(5)).unwrap();
        drop(select);
        for _ in 0..300 {
            client
                .sender
                .send(Message::Notification(Notification::new(
                    "edit".into(),
                    Value::Null,
                )))
                .unwrap();
        }
        client
            .sender
            .send(Message::Notification(Notification::new(
                "exit".into(),
                Value::Null,
            )))
            .unwrap();
        run(&mut owner, &server).unwrap();
        assert_eq!(owner.edits, 300);
        assert_eq!(owner.completed_after, [256]);
        assert_eq!(owner.hooks.finished, [json!({"current":false})]);
    }
    #[test]
    fn holds_idle_cancellation_reset_and_shutdown_share_one_protocol() {
        let (server, client) = Connection::memory();
        let thread = std::thread::spawn(move || {
            let mut owner = Owner::new();
            run(&mut owner, &server).unwrap();
            owner
        });
        for (base, phase) in [(10, "duringCheck"), (20, "beforeResult")] {
            request(&client, base, test_support::HOLD, json!({"phase":phase}));
            assert!(response(&client, base).error.is_none());
            client
                .sender
                .send(Message::Notification(Notification::new(
                    "enqueue".into(),
                    Value::Null,
                )))
                .unwrap();
            let Message::Notification(checkpoint) = receive(&client) else {
                panic!("expected checkpoint")
            };
            assert_eq!(checkpoint.method, test_support::CHECKPOINT);
            request(&client, base + 1, test_support::CHECKING_IDLE, Value::Null);
            request(&client, base + 2, test_support::RESET_CHECKS, Value::Null);
            assert_eq!(response(&client, base + 2).error.unwrap().code, -32602);
            client
                .sender
                .send(Message::Notification(Notification::new(
                    "$/cancelRequest".into(),
                    json!({"id":base+1}),
                )))
                .unwrap();
            assert_eq!(response(&client, base + 1).error.unwrap().code, -32800);
            request(&client, base + 3, test_support::RELEASE, checkpoint.params);
            assert!(response(&client, base + 3).error.is_none());
            request(&client, base + 4, test_support::CHECKING_IDLE, Value::Null);
            assert!(response(&client, base + 4).error.is_none());
            request(&client, base + 5, test_support::RESET_CHECKS, Value::Null);
            assert!(response(&client, base + 5).error.is_none());
        }
        request(&client, 30, test_support::HOLD, Value::Null);
        response(&client, 30);
        client
            .sender
            .send(Message::Notification(Notification::new(
                "enqueue".into(),
                Value::Null,
            )))
            .unwrap();
        assert!(matches!(receive(&client), Message::Notification(_)));
        request(&client, 31, "shutdown", Value::Null);
        assert!(response(&client, 31).error.is_none());
        client
            .sender
            .send(Message::Notification(Notification::new(
                "exit".into(),
                Value::Null,
            )))
            .unwrap();
        let owner = thread.join().unwrap();
        assert_eq!(owner.hooks.started.len(), 3);
        assert_eq!(owner.hooks.finished.len(), 2);
    }
}
