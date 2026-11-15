//! Borrowed diagnostic snapshots. Observers must bound their own work and storage;
//! they cannot modify admission and are never retained in a session.
use crate::*;
use denotate_ir::OccurrenceId;

pub struct AdmissionDump<'a> {
    /// Invocation-local graph revision, not a persistent identity.
    pub snapshot: u64,
    pub program: &'a GroundProgram,
    pub event: AdmissionDumpEvent<'a>,
}

pub enum AdmissionDumpEvent<'a> {
    /// The last committed graph, including on cancellation or deadline failure.
    Graph {
        state: &'static str,
        error: Option<&'a CheckError>,
    },
    /// The final guard and cone actually passed to bounds, never a ranking preview.
    Guarded {
        candidate: &'a ProducerSummary,
        literal: &'a GroundLiteral,
        cone: &'a GuardedCone<&'a ProducerSummary>,
        implied: Option<&'a ImpliedGuardProof>,
        before_atoms: Option<usize>,
        before_rules: Option<usize>,
        pruning: Option<&'static str>,
    },
    GuardedOutcome {
        rule: GroundRuleId,
        occurrence: OccurrenceId,
        stage: &'static str,
        state: &'static str,
        reason: Option<Inconclusive>,
    },
}

/// Delivery is synchronous and excluded from the admission deadline. An observer
/// must handle its own exhaustion/IO failures without returning a checker error.
pub type AdmissionDumpObserver<'a> = dyn Fn(AdmissionDump<'_>) + 'a;

impl GroundProgram {
    pub(crate) fn dump(
        &self,
        observer: Option<&AdmissionDumpObserver<'_>>,
        event: AdmissionDumpEvent<'_>,
    ) {
        if let Some(observer) = observer {
            observer(AdmissionDump {
                snapshot: self.graph_revision,
                program: self,
                event,
            });
        }
    }
    /// Indexed access to a residual component's current producers. Fixed components
    /// have no residual producers. Unlike `rules()`,
    /// this does not scan the fixed evidence graph or unrelated components.
    pub fn residual_component_producers(
        &self,
        id: ComponentId,
    ) -> impl Iterator<Item = &GroundRule> {
        self.component_rules
            .get(id.index)
            .into_iter()
            .flatten()
            .filter(move |_| id.preparation == self.graph_revision)
            .map(|i| &self.rules[*i])
            .filter(|r| !self.rewrites.dropped.contains(&r.id))
    }
    /// Residual SCCs only; fixed facts cannot contain an unresolved cycle.
    pub fn residual_components(&self) -> impl ExactSizeIterator<Item = &Component> {
        self.components.iter()
    }
}
