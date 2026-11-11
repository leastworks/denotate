//! Invocation-local observations, never semantic inputs or cached values.
use crate::*;
use denotate_ir::{NoticeId, ObligationId};
use std::{
    fmt,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

#[derive(Debug, Clone)]
pub enum CheckingTarget {
    Obligation(ObligationId),
    Notice(NoticeId),
    Component(AdmissionComponent),
}
#[derive(Debug, Clone)]
pub struct CheckingEvent {
    pub stage: &'static str,
    pub state: &'static str,
    pub target: Option<CheckingTarget>,
    pub failure: Option<CheckError>,
    /// Continue other work in this verification after a recoverable exhaustion.
    pub continues: bool,
}
#[derive(Clone)]
struct Frame {
    stage: &'static str,
    target: Option<CheckingTarget>,
    continues: bool,
    private_runtime: bool,
    deadline_recovers: bool,
    failure: Option<CheckError>,
}
impl Default for Frame {
    fn default() -> Self {
        Self {
            stage: "checking",
            target: None,
            continues: false,
            private_runtime: false,
            deadline_recovers: false,
            failure: None,
        }
    }
}
struct State {
    send: Box<dyn Fn(CheckingEvent) + Send + Sync>,
    current: Mutex<Frame>,
    last: Mutex<(Option<Instant>, std::collections::BTreeSet<&'static str>)>,
}
#[derive(Clone, Default)]
pub struct CheckingProgress(Option<Arc<State>>);
impl fmt::Debug for CheckingProgress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CheckingProgress")
            .field(&self.enabled())
            .finish()
    }
}
impl CheckingProgress {
    pub fn new(send: impl Fn(CheckingEvent) + Send + Sync + 'static) -> Self {
        Self(Some(Arc::new(State {
            send: Box::new(send),
            current: Mutex::new(Frame::default()),
            last: Mutex::new((None, Default::default())),
        })))
    }
    pub fn enabled(&self) -> bool {
        self.0.is_some()
    }
    pub fn scope(
        &self,
        stage: &'static str,
        target: Option<CheckingTarget>,
        continues: bool,
    ) -> CheckingScope {
        self.enter(stage, target, continues, true, false)
    }
    /// Notices and optional diagnostic attribution recover even from a deadline.
    pub(crate) fn advisory(&self, stage: &'static str, target: CheckingTarget) -> CheckingScope {
        let scope = self.enter(stage, Some(target), true, false, false);
        if let Some(s) = &self.0 {
            s.current.lock().unwrap().deadline_recovers = true;
        }
        scope
    }
    pub(crate) fn sampled(
        &self,
        stage: &'static str,
        partial: bool,
        target: impl FnOnce() -> CheckingTarget,
    ) -> CheckingScope {
        let Some(s) = &self.0 else {
            return CheckingScope::default();
        };
        let current = s.current.lock().unwrap().clone();
        let target = if current.private_runtime {
            None
        } else {
            Some(target())
        };
        self.enter(stage, target, partial || current.continues, false, false)
    }
    pub(crate) fn nested(&self, stage: &'static str) -> CheckingScope {
        let continues = self
            .0
            .as_ref()
            .is_some_and(|s| s.current.lock().unwrap().continues);
        self.enter(stage, None, continues, false, false)
    }
    pub(crate) fn private_scope(&self, stage: &'static str) -> CheckingScope {
        self.enter(stage, None, true, false, true)
    }
    fn enter(
        &self,
        stage: &'static str,
        target: Option<CheckingTarget>,
        continues: bool,
        force: bool,
        private: bool,
    ) -> CheckingScope {
        let Some(s) = &self.0 else {
            return CheckingScope::default();
        };
        let mut frame = s.current.lock().unwrap();
        let next = Frame {
            stage,
            target: if frame.private_runtime {
                frame.target.clone()
            } else {
                target.or_else(|| frame.target.clone())
            },
            continues,
            private_runtime: private || frame.private_runtime,
            deadline_recovers: frame.deadline_recovers,
            failure: None,
        };
        let previous = std::mem::replace(&mut *frame, next);
        drop(frame);
        self.emit("started", force);
        CheckingScope {
            progress: self.clone(),
            previous: Some(previous),
            force,
        }
    }
    pub fn failure(&self, error: &CheckError) {
        if !matches!(
            error,
            CheckError::LimitExceeded { .. } | CheckError::Deadline { .. }
        ) {
            return;
        }
        let Some(s) = &self.0 else {
            return;
        };
        let mut frame = s.current.lock().unwrap();
        if frame.failure.as_ref() == Some(error) {
            return;
        }
        frame.failure = Some(error.clone());
        drop(frame);
        self.emit("exhausted", true);
    }
    fn emit(&self, state: &'static str, force: bool) {
        let Some(s) = &self.0 else {
            return;
        };
        let f = s.current.lock().unwrap().clone();
        let mut last = s.last.lock().unwrap();
        let first_stage = state == "started" && last.1.insert(f.stage);
        if !force
            && !first_stage
            && last
                .0
                .is_some_and(|t| t.elapsed() < Duration::from_millis(250))
        {
            return;
        }
        last.0 = Some(Instant::now());
        drop(last);
        (s.send)(CheckingEvent {
            stage: f.stage,
            state,
            target: f.target,
            continues: f.continues
                && (f.deadline_recovers || !matches!(f.failure, Some(CheckError::Deadline { .. }))),
            failure: f.failure,
        });
    }
}
#[derive(Default)]
pub struct CheckingScope {
    progress: CheckingProgress,
    previous: Option<Frame>,
    force: bool,
}
impl Drop for CheckingScope {
    fn drop(&mut self) {
        if let (Some(s), Some(previous)) = (&self.progress.0, self.previous.take()) {
            self.progress.emit("finished", self.force);
            *s.current.lock().unwrap() = previous;
        }
    }
}
impl GroundProgram {
    /// Compact existing graph metadata; no semantic key or dependency expansion.
    pub fn progress_component(&self, id: ComponentId) -> Option<AdmissionComponent> {
        let c = self.component(id)?;
        let first = c.cycle.as_ref().and_then(|c| c.edges.first());
        let rule = first.and_then(|e| self.rule(e.rule)).or_else(|| {
            self.component_rules
                .get(id.index)?
                .first()
                .and_then(|i| self.rules.get(*i))
        });
        Some(AdmissionComponent {
            index: id.index + 1,
            atoms: c.atoms.len(),
            rules: self.component_rules.get(id.index).map_or(0, Vec::len),
            representative: first
                .map(|e| &e.consumer)
                .or_else(|| c.atoms.first())?
                .clone(),
            source: rule.map(|r| r.source),
        })
    }
}
