//! Serial LSP dispatch and cancellation checkpoints. No grammar, capabilities,
//! workspace indexing or diagnostic scheduling policy is imposed here.
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response, ResponseError};
use serde_json::{json, Value};
use std::{collections::VecDeque, error::Error};

pub type Result<T> = std::result::Result<T, Box<dyn Error>>;

pub fn send(connection: &Connection, method: &str, params: Value) -> Result<()> {
    connection
        .sender
        .send(Message::Notification(Notification::new(
            method.into(),
            params,
        )))?;
    Ok(())
}

/// Frontends retain request routing, error policy and notification side effects.
pub trait Handler {
    fn supports_request(&self, method: &str) -> bool;
    fn unsupported_request(&self, request: &Request) -> ResponseError {
        ResponseError {
            code: -32601,
            message: format!("Unsupported request: {}", request.method),
            data: None,
        }
    }
    fn request(&mut self, request: &Request) -> std::result::Result<Value, ResponseError>;
    fn notification(&mut self, connection: &Connection, notification: Notification) -> Result<()>;
    fn response(&mut self, _connection: &Connection, _response: Response) -> Result<()> {
        Ok(())
    }
}

// Bounded draining prevents an endless stream from monopolizing dispatch.
// These are checkpoints, not preemption of parsing or synchronous analysis.
pub fn receive_ready(connection: &Connection, pending: &mut VecDeque<Message>) {
    pending.extend(connection.receiver.try_iter().take(256));
}

pub fn take_cancellation(pending: &mut VecDeque<Message>, id: &RequestId) -> bool {
    let mut cancelled = false;
    pending.retain(|message| {
        let matches = matches!(message, Message::Notification(n)
            if n.method == "$/cancelRequest" && n.params.get("id") == Some(&json!(id)));
        cancelled |= matches;
        !matches
    });
    cancelled
}

pub fn dispatch_request(
    handler: &mut impl Handler,
    request: Request,
    connection: &Connection,
    pending: &mut VecDeque<Message>,
) -> Result<()> {
    let supported = handler.supports_request(&request.method);
    let mut response = if take_cancellation(pending, &request.id) {
        Response::new_err(request.id.clone(), -32800, "Request cancelled".into())
    } else if !supported {
        Response {
            id: request.id.clone(),
            result: None,
            error: Some(handler.unsupported_request(&request)),
        }
    } else {
        match handler.request(&request) {
            Ok(value) => Response::new_ok(request.id.clone(), value),
            Err(error) => Response {
                id: request.id.clone(),
                result: None,
                error: Some(error),
            },
        }
    };
    receive_ready(connection, pending);
    if take_cancellation(pending, &request.id) {
        response = Response::new_err(request.id, -32800, "Request cancelled".into());
    }
    connection.sender.send(Message::Response(response))?;
    Ok(())
}

/// B's serial owner loop. A frontend with a worker can use the dispatch helpers
/// in its own event loop; this function does not claim asynchronous scheduling.
pub fn run(connection: &Connection, handler: &mut impl Handler) -> Result<()> {
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
                dispatch_request(handler, request, connection, &mut pending)?;
            }
            Message::Notification(notification) => {
                if notification.method == "exit" {
                    break;
                }
                if let Err(error) = handler.notification(connection, notification) {
                    eprintln!("notification rejected: {error}");
                }
            }
            Message::Response(response) => handler.response(connection, response)?,
        }
    }
    Ok(())
}

pub fn stdio(serve: impl FnOnce(&Connection) -> Result<()>) -> Result<()> {
    let (connection, threads) = Connection::stdio();
    let result = serve(&connection);
    drop(connection);
    threads.join()?;
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Language {
        notifications: Vec<String>,
    }

    impl Handler for Language {
        fn supports_request(&self, method: &str) -> bool {
            matches!(method, "echo" | "refuse")
        }
        fn request(&mut self, request: &Request) -> std::result::Result<Value, ResponseError> {
            if request.method == "refuse" {
                Err(ResponseError {
                    code: -32801,
                    message: "language policy".into(),
                    data: Some(json!(7)),
                })
            } else {
                Ok(request.params.clone())
            }
        }
        fn notification(&mut self, _: &Connection, notification: Notification) -> Result<()> {
            self.notifications.push(notification.method);
            Ok(())
        }
    }

    #[test]
    fn serial_loop_preserves_language_routing_errors_and_shutdown() {
        let (server, client) = Connection::memory();
        let owner = std::thread::spawn(move || {
            let mut language = Language::default();
            run(&server, &mut language).unwrap();
            language
        });
        client
            .sender
            .send(Message::Notification(Notification::new(
                "changed".into(),
                Value::Null,
            )))
            .unwrap();
        for (id, method) in [(1, "echo"), (2, "unknown"), (3, "refuse"), (4, "shutdown")] {
            client
                .sender
                .send(Message::Request(Request::new(
                    id.into(),
                    method.into(),
                    json!({"value": 9}),
                )))
                .unwrap();
        }
        let replies: Vec<Response> = (0..4)
            .map(|_| {
                let message = client
                    .receiver
                    .recv_timeout(std::time::Duration::from_secs(5))
                    .unwrap();
                let Message::Response(response) = message else {
                    panic!("response expected")
                };
                response
            })
            .collect();
        // Like the real harness, wait for shutdown's response before exit.
        client
            .sender
            .send(Message::Notification(Notification::new(
                "exit".into(),
                Value::Null,
            )))
            .unwrap();
        assert_eq!(owner.join().unwrap().notifications, ["changed"]);
        assert_eq!(replies.len(), 4);
        assert_eq!(replies[0].result, Some(json!({"value": 9})));
        assert_eq!(replies[1].error.as_ref().unwrap().code, -32601);
        assert_eq!(replies[2].error.as_ref().unwrap().code, -32801);
        assert_eq!(
            replies[2].error.as_ref().unwrap().message,
            "language policy"
        );
        assert_eq!(replies[2].error.as_ref().unwrap().data, Some(json!(7)));
        assert_eq!(replies[3].result, Some(Value::Null));
    }
}
