//! Explicit process observations owned by drivers, never by a semantic query.
//! Unavailable OS metrics are None. Samples include all work in this process.
use denotate_check::{Profile, ProfileEvent};
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex, mpsc},
    thread,
    time::Duration,
};

#[derive(Debug, Default, Clone, Copy, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProcessMemory {
    pub rss_bytes: Option<u64>,
    /// Process lifetime high water, not the peak of the latest phase.
    pub peak_rss_bytes: Option<u64>,
    pub footprint_bytes: Option<u64>,
    pub peak_footprint_bytes: Option<u64>,
}
impl ProcessMemory {
    fn include(&mut self, other: Self) {
        self.rss_bytes = self.rss_bytes.max(other.rss_bytes);
        self.peak_rss_bytes = self.peak_rss_bytes.max(other.peak_rss_bytes);
        self.footprint_bytes = self.footprint_bytes.max(other.footprint_bytes);
        self.peak_footprint_bytes = self.peak_footprint_bytes.max(other.peak_footprint_bytes);
    }
}

/// Best-effort OS reading. Failure cannot change a checking outcome.
pub fn process_memory() -> ProcessMemory {
    #[cfg(target_os = "macos")]
    {
        let mut result = ProcessMemory::default();
        // SAFETY: correctly sized initialized C structs, current process only.
        unsafe {
            let mut info: libc::rusage_info_v4 = std::mem::zeroed();
            if libc::proc_pid_rusage(
                libc::getpid(),
                libc::RUSAGE_INFO_V4,
                (&mut info as *mut libc::rusage_info_v4).cast(),
            ) == 0
            {
                result.rss_bytes = Some(info.ri_resident_size);
                result.footprint_bytes = Some(info.ri_phys_footprint);
                result.peak_footprint_bytes = Some(info.ri_lifetime_max_phys_footprint);
            }
            let mut usage: libc::rusage = std::mem::zeroed();
            if libc::getrusage(libc::RUSAGE_SELF, &mut usage) == 0 {
                result.peak_rss_bytes = u64::try_from(usage.ru_maxrss).ok();
            }
        }
        result
    }
    #[cfg(target_os = "linux")]
    {
        linux_memory(&std::fs::read_to_string("/proc/self/status").unwrap_or_default())
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        ProcessMemory::default()
    }
}

#[cfg(any(target_os = "linux", test))]
fn linux_memory(status: &str) -> ProcessMemory {
    let kb = |name| {
        status.lines().find_map(|line| {
            let value = line.strip_prefix(name)?.split_whitespace().next()?;
            value.parse::<u64>().ok()?.checked_mul(1024)
        })
    };
    ProcessMemory {
        rss_bytes: kb("VmRSS:"),
        peak_rss_bytes: kb("VmHWM:"),
        ..Default::default()
    }
}

pub struct MemoryEvent {
    pub event: ProfileEvent,
    pub memory: ProcessMemory,
    /// Maximum of boundary and periodic samples while this span was active.
    /// A lower bound on the true phase peak; lifetime peaks remain separate.
    pub sampled_peak: ProcessMemory,
}
impl MemoryEvent {
    pub fn data(&self) -> serde_json::Value {
        let p = &self.event;
        serde_json::json!({"type":"profile","stage":p.stage,"span":p.id,"round":p.round,
            "event":if p.finished {"end"} else {"start"},"elapsedMs":p.elapsed.as_secs_f64()*1000.,
            "memory":self.memory,"sampledPeak":self.sampled_peak,"sampleIntervalMs":MemoryProfiler::INTERVAL.as_millis(),
            "peakAccountedConditionNodes":p.peak_accounted_condition_nodes,
            "bddResults":p.bdd_results,"bddResultNodes":p.bdd_result_nodes,"bddResultNodeBytes":p.bdd_result_node_bytes,
            "retainedBdd":p.retained.map(|s|serde_json::json!({"references":s.references,"distinctArrays":s.distinct_arrays,"nodes":s.nodes,"nodeBytes":s.node_bytes}))})
    }
}

/// Samples process memory while explicitly profiled spans are active. Start/end
/// callbacks stream immediately, including when a later phase cannot finish.
pub struct MemoryProfiler {
    pub profile: Profile,
    stop: mpsc::Sender<()>,
    worker: Option<thread::JoinHandle<()>>,
}
impl MemoryProfiler {
    pub const INTERVAL: Duration = Duration::from_millis(20);
    pub fn new(send: impl Fn(MemoryEvent) + Send + Sync + 'static) -> Self {
        let active = Arc::new(Mutex::new(BTreeMap::<u64, ProcessMemory>::new()));
        let (stop, receive) = mpsc::channel();
        let samples = active.clone();
        let worker = thread::spawn(move || {
            while receive.recv_timeout(Self::INTERVAL) == Err(mpsc::RecvTimeoutError::Timeout) {
                let mut samples = samples.lock().unwrap();
                if !samples.is_empty() {
                    let memory = process_memory();
                    for peak in samples.values_mut() {
                        peak.include(memory);
                    }
                }
            }
        });
        let profile = Profile::new(move |event| {
            let memory = process_memory();
            let sampled_peak = {
                let mut active = active.lock().unwrap();
                // Nested span boundaries are also samples for their parents.
                for peak in active.values_mut() {
                    peak.include(memory);
                }
                if event.finished {
                    active.remove(&event.id).unwrap_or(memory)
                } else {
                    active.insert(event.id, memory);
                    memory
                }
            };
            send(MemoryEvent {
                event,
                memory,
                sampled_peak,
            });
        });
        Self {
            profile,
            stop,
            worker: Some(worker),
        }
    }
}
impl Drop for MemoryProfiler {
    fn drop(&mut self) {
        let _ = self.stop.send(());
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn linux_units_and_unavailable_metrics_are_explicit() {
        let m = linux_memory("VmRSS:\t12 kB\nVmHWM:\t34 kB\n");
        assert_eq!(m.rss_bytes, Some(12 * 1024));
        assert_eq!(m.peak_rss_bytes, Some(34 * 1024));
        assert_eq!(m.footprint_bytes, None);
        assert_eq!(linux_memory("VmRSS: nope kB").rss_bytes, None);
    }
    #[test]
    fn nested_spans_stream_and_release_without_waiting_for_poll() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let out = events.clone();
        let monitor = MemoryProfiler::new(move |e| out.lock().unwrap().push(e));
        {
            let _a = monitor.profile.span("outer", None);
            let _b = monitor.profile.span("inner", Some(1));
        }
        drop(monitor);
        let events = events.lock().unwrap();
        assert_eq!(
            events
                .iter()
                .map(|e| (e.event.stage, e.event.finished))
                .collect::<Vec<_>>(),
            [
                ("outer", false),
                ("inner", false),
                ("inner", true),
                ("outer", true)
            ]
        );
    }
}
