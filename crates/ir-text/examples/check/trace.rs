//! CLI layout for shared phase events. Progress is best-effort and never alters
//! a checking result when the diagnostic stream cannot be written.
use serde_json::Value;
use std::{
    io::Write,
    sync::{Arc, Mutex},
    time::Instant,
};

#[derive(Clone)]
pub struct Trace {
    output: Arc<Mutex<Box<dyn Write + Send>>>,
    enabled: bool,
    started: Instant,
    phase: Arc<Mutex<Option<(String, Instant)>>>,
}
impl Trace {
    pub fn new(output: impl Write + Send + 'static, enabled: bool) -> Self {
        Self {
            output: Arc::new(Mutex::new(Box::new(output))),
            enabled,
            started: Instant::now(),
            phase: Arc::new(Mutex::new(None)),
        }
    }
    pub fn message(&self, message: impl std::fmt::Display) {
        if self.enabled {
            let mut output = self.output.lock().unwrap();
            let _ = writeln!(
                output,
                "[check +{:.3}s] {message}",
                self.started.elapsed().as_secs_f64()
            );
            let _ = output.flush();
        }
    }
    fn end_phase(&self) {
        if let Some((name, start)) = self.phase.lock().unwrap().take() {
            self.message(format_args!(
                "{name}: phase time {:.3}s",
                start.elapsed().as_secs_f64()
            ));
        }
    }
    pub fn phase(&self, detail: Value) {
        if !self.enabled {
            return;
        }
        self.end_phase();
        let phase = detail["phase"].as_str().unwrap();
        let label = if let Some(name) = detail["verification"].as_str() {
            format!(
                "{phase}: verification {}/{} {name}",
                detail["verificationIndex"], detail["verificationTotal"]
            )
        } else {
            phase.into()
        };
        self.message(format_args!("Starting {label}"));
        self.memory();
        *self.phase.lock().unwrap() = Some((label, Instant::now()));
        if let Some(files) = detail.get("files") {
            self.message(format_args!("Source files: {files}"));
        }
        // Later phases repeat the context; print it once, where it first appears.
        if phase == "preparation" && detail["verification"].is_string() {
            self.message(format_args!(
                "Selected: {} assumptions, {} obligations, {} notices",
                detail["assumptions"], detail["obligations"], detail["notices"]
            ));
        }
        if let Some(g) = detail.get("ground").filter(|_| phase == "admission") {
            self.message(format_args!("Prepared size (before admission): {} inputs, {} atoms, {} rule instances, {} components; largest component {} atoms",
                g["inputAtoms"], g["atoms"], g["ruleInstances"], g["components"], g["largestComponentAtoms"]));
        }
        if let Some(fold) = detail.get("fold").filter(|_| phase == "admission") {
            self.message(format_args!("Fixed facts and retained evidence: {fold}"));
        }
    }
    pub fn finish(&self, outcome: impl std::fmt::Display) {
        self.end_phase();
        self.memory();
        self.message(outcome);
    }
    fn memory(&self) {
        if self.enabled {
            self.message(format_args!(
                "Process memory (bytes; peaks are lifetime): {}",
                serde_json::to_value(denotate_check_session::profiling::process_memory()).unwrap()
            ));
        }
    }
}
