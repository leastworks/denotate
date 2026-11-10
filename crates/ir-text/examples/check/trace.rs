//! CLI layout for shared phase events. Progress is best-effort and never alters
//! a checking result when the diagnostic stream cannot be written.
use serde_json::Value;
use std::{cell::RefCell, io::Write, time::Instant};

pub struct Trace<'a> {
    output: RefCell<&'a mut dyn Write>,
    enabled: bool,
    started: Instant,
    phase: RefCell<Option<(String, Instant)>>,
}
impl<'a> Trace<'a> {
    pub fn new(output: &'a mut dyn Write, enabled: bool) -> Self {
        Self {
            output: RefCell::new(output),
            enabled,
            started: Instant::now(),
            phase: RefCell::new(None),
        }
    }
    pub fn message(&self, message: impl std::fmt::Display) {
        if self.enabled {
            let mut output = self.output.borrow_mut();
            let _ = writeln!(
                output,
                "[check +{:.3}s] {message}",
                self.started.elapsed().as_secs_f64()
            );
            let _ = output.flush();
        }
    }
    fn end_phase(&self) {
        if let Some((name, start)) = self.phase.borrow_mut().take() {
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
        *self.phase.borrow_mut() = Some((label, Instant::now()));
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
    }
    pub fn finish(&self, outcome: impl std::fmt::Display) {
        self.end_phase();
        self.message(outcome);
    }
}
