//! Best-effort JSONL observations. Flush bounded batches, including while idle.
use serde_json::Value;
use std::{
    fs::File,
    io::{BufWriter, Write},
    sync::{Arc, Mutex, mpsc},
    thread::JoinHandle,
    time::Duration,
};

const RECORDS: usize = 256;
const INTERVAL: Duration = Duration::from_millis(250);

pub struct Writer<W: Write> {
    output: BufWriter<W>,
    pending: usize,
}
impl<W: Write> Writer<W> {
    fn new(output: W) -> Self {
        Self {
            output: BufWriter::with_capacity(64 * 1024, output),
            pending: 0,
        }
    }
    fn flush(&mut self) {
        let _ = self.output.flush();
        self.pending = 0;
    }
    fn record(&mut self, event: Value) {
        let boundary = event["type"] == "completion-preparation-sizes"
            || event["type"] == "run-end"
            || event["type"] == "profile"
            || (event["type"] == "progress"
                && event["detail"].get("phase").is_some()
                && [
                    "admission",
                    "checking",
                    "remainingComponent",
                    "satProbe",
                    "candidateProbe",
                ]
                .iter()
                .all(|key| event["detail"].get(key).is_none()));
        let _ = writeln!(self.output, "{event}");
        self.pending += 1;
        if boundary || self.pending >= RECORDS {
            self.flush();
        }
    }
}

pub type Shared = Arc<Mutex<Writer<File>>>;
pub struct FlushGuard {
    stop: mpsc::Sender<()>,
    worker: Option<JoinHandle<()>>,
}
impl FlushGuard {
    pub fn new(file: File) -> (Shared, Self) {
        let shared = Arc::new(Mutex::new(Writer::new(file)));
        let output = shared.clone();
        let (stop, stopped) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            loop {
                let done = !matches!(
                    stopped.recv_timeout(INTERVAL),
                    Err(mpsc::RecvTimeoutError::Timeout)
                );
                output.lock().unwrap().flush();
                #[cfg(unix)]
                if let Some(signal) = signals::pending() {
                    // No IO or locks in the signal handler. Restore and re-raise
                    // here so the runner still sees termination by signal.
                    signals::terminate(signal);
                }
                if done {
                    break;
                }
            }
        });
        (
            shared,
            Self {
                stop,
                worker: Some(worker),
            },
        )
    }
}
impl Drop for FlushGuard {
    fn drop(&mut self) {
        let _ = self.stop.send(());
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}
pub fn record(file: &Option<Shared>, event: Value) {
    if let Some(file) = file {
        file.lock().unwrap().record(event);
    }
}

#[cfg(unix)]
pub mod signals {
    use std::sync::atomic::{AtomicI32, Ordering};
    static SIGNAL: AtomicI32 = AtomicI32::new(0);
    extern "C" fn receive(signal: libc::c_int) {
        SIGNAL.store(signal, Ordering::Relaxed);
    }
    pub fn install() {
        // Only the CLI main installs handlers, never library/test invocations.
        unsafe {
            libc::signal(libc::SIGINT, receive as *const () as libc::sighandler_t);
            libc::signal(libc::SIGTERM, receive as *const () as libc::sighandler_t);
        }
    }
    pub fn pending() -> Option<i32> {
        match SIGNAL.load(Ordering::Relaxed) {
            0 => None,
            s => Some(s),
        }
    }
    pub fn terminate(signal: i32) -> ! {
        unsafe {
            libc::signal(signal, libc::SIG_DFL);
            libc::raise(signal);
        }
        std::process::exit(128 + signal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn dropping_the_guard_flushes_pending_records() {
        let path =
            std::env::temp_dir().join(format!("den-profile-flush-{}.jsonl", std::process::id()));
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        let (shared, guard) = FlushGuard::new(file);
        record(
            &Some(shared.clone()),
            serde_json::json!({"type":"progress", "detail":{"phase":"admission", "admission":{"round":1}}}),
        );
        drop(guard);
        drop(shared);
        let text = std::fs::read_to_string(&path).unwrap();
        assert_eq!(
            serde_json::from_str::<Value>(&text).unwrap()["detail"]["admission"]["round"],
            1
        );
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn records_are_batched_and_boundaries_flush_complete_json_lines() {
        let mut writer = Writer::new(Vec::new());
        for i in 0..RECORDS - 1 {
            writer.record(serde_json::json!({"type":"progress", "detail":{"phase":"admission","admission":{"round":1}}, "i":i}));
        }
        assert!(writer.output.get_ref().is_empty());
        writer.record(serde_json::json!({"type":"progress", "i":RECORDS-1}));
        assert_eq!(
            writer.output.get_ref().split(|b| *b == b'\n').count() - 1,
            RECORDS
        );
        writer.record(serde_json::json!({"type":"progress", "detail":{"phase":"checking"}}));
        writer.record(serde_json::json!({"type":"run-end", "exitCode":2}));
        let lines = String::from_utf8(writer.output.into_inner().unwrap()).unwrap();
        assert_eq!(lines.lines().count(), RECORDS + 2);
        for line in lines.lines() {
            serde_json::from_str::<Value>(line).unwrap();
        }
    }
}
