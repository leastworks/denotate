//! Explicit retained-payload accounting, not allocator/RSS measurement. Count
//! occupied collection payloads plus fixed headers, and shared Arc payloads once
//! within each entry part. Across entries/parts we conservatively count sharing
//! again. Pointers only identify allocation sharing here, never semantic identity.
use denotate_check::*;
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    mem::size_of,
    sync::Arc,
};

#[derive(Default)]
pub(crate) struct Payload {
    bytes: usize,
    shared: HashSet<usize>,
}
impl Payload {
    fn add(&mut self, n: usize) {
        self.bytes = self.bytes.saturating_add(n);
    }
    fn allocation(&mut self, ptr: usize, bytes: usize) -> bool {
        if self.shared.insert(ptr) {
            self.add(bytes.saturating_add(2 * size_of::<usize>()));
            true
        } else {
            false
        }
    }
}
pub(crate) trait Retained {
    fn heap(&self, p: &mut Payload);
}
pub(crate) fn bytes<T: Retained>(value: &T) -> usize {
    let mut p = Payload::default();
    p.add(size_of::<T>());
    value.heap(&mut p);
    p.bytes
}
macro_rules! flat {($($t:ty),*)=>{$(impl Retained for $t {fn heap(&self,_:&mut Payload){}})*};}
flat!(
    usize,
    u8,
    bool,
    DeterministicLimits,
    Inconclusive,
    RequestScope
);
impl Retained for String {
    fn heap(&self, p: &mut Payload) {
        p.add(self.capacity());
    }
}
impl<T: Retained> Retained for Vec<T> {
    fn heap(&self, p: &mut Payload) {
        p.add(self.capacity().saturating_mul(size_of::<T>()));
        for v in self {
            v.heap(p);
        }
    }
}
impl<T: Retained> Retained for Option<T> {
    fn heap(&self, p: &mut Payload) {
        if let Some(v) = self {
            v.heap(p);
        }
    }
}
impl<A: Retained, B: Retained> Retained for (A, B) {
    fn heap(&self, p: &mut Payload) {
        self.0.heap(p);
        self.1.heap(p);
    }
}
impl<A: Retained, B: Retained, C: Retained> Retained for (A, B, C) {
    fn heap(&self, p: &mut Payload) {
        self.0.heap(p);
        self.1.heap(p);
        self.2.heap(p);
    }
}
impl<K: Retained, V: Retained> Retained for BTreeMap<K, V> {
    fn heap(&self, p: &mut Payload) {
        p.add(
            self.len()
                .saturating_mul(size_of::<(K, V)>().saturating_add(48)),
        );
        for (k, v) in self {
            k.heap(p);
            v.heap(p);
        }
    }
}
impl<T: Retained> Retained for BTreeSet<T> {
    fn heap(&self, p: &mut Payload) {
        p.add(self.len().saturating_mul(size_of::<T>().saturating_add(48)));
        for v in self {
            v.heap(p);
        }
    }
}
impl<T: Retained> Retained for Arc<T> {
    fn heap(&self, p: &mut Payload) {
        if p.allocation(Arc::as_ptr(self) as usize, size_of::<T>()) {
            self.as_ref().heap(p);
        }
    }
}
impl<T: Retained> Retained for Arc<[T]> {
    fn heap(&self, p: &mut Payload) {
        slice(self, p);
    }
}
impl Retained for Arc<str> {
    fn heap(&self, p: &mut Payload) {
        p.allocation(self.as_ptr() as usize, self.len());
    }
}
fn slice<T: Retained>(s: &[T], p: &mut Payload) {
    if p.allocation(s.as_ptr() as usize, s.len().saturating_mul(size_of::<T>())) {
        for v in s {
            v.heap(p);
        }
    }
}
macro_rules! fields {($t:ty {$($f:ident),* $(,)?})=>{impl Retained for $t {fn heap(&self,p:&mut Payload){let Self{$($f),*}=self;$($f.heap(p);)*}}};}
macro_rules! wrapped {($($t:ty),*)=>{$(impl Retained for $t {fn heap(&self,p:&mut Payload){self.0.heap(p);}})*};}
wrapped!(
    SortKey,
    ObligationKey,
    AssumptionKey,
    VerificationKey,
    ComponentKey,
    GroundingKey
);
impl Retained for OwnerKey {
    fn heap(&self, p: &mut Payload) {
        p.allocation(self.namespace().as_ptr() as usize, self.namespace().len());
        p.allocation(self.value().as_ptr() as usize, self.value().len());
    }
}
fields!(QualifiedKey { namespace, name });
fields!(ConstantKey { sort, name });
fields!(VariableKey { sort, name });
impl Retained for RelationKey {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Named(k) => k.heap(p),
            Self::Generated { owner, local: _ } => owner.heap(p),
        }
    }
}
impl Retained for RuleKey {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Library(k) => k.heap(p),
            Self::Installed { owner, local: _ } => owner.heap(p),
        }
    }
}
impl Retained for OccurrenceKey {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Sort(k) => k.heap(p),
            Self::Constant(k) => k.heap(p),
            Self::Relation(k) => k.heap(p),
            Self::Rule(k) => k.heap(p),
            Self::Obligation(k) => k.heap(p),
            Self::Assumption(k) => k.heap(p),
            Self::Verification(k) => k.heap(p),
            Self::Installed { owner, local: _ } => owner.heap(p),
            Self::Library {
                rule,
                atom: _,
                argument: _,
            } => rule.heap(p),
        }
    }
}
impl Retained for TermKey {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Constant(k) => k.heap(p),
            Self::Variable(k) => k.heap(p),
        }
    }
}
fields!(AtomSchema {
    relation,
    occurrence,
    arguments
});
fields!(RuleSchema { head, body });
fields!(AtomKey {
    relation,
    arguments
});
fields!(InstanceKey { rule, substitution });
fields!(GroupKey { obligation, tuple });
fields!(KeyedGroundOccurrence {
    atom,
    occurrence,
    arguments
});
fields!(GroundInstance { schema, head, body });
impl Retained for KeyedRewriteKind {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Discharge(k) => k.heap(p),
            Self::RedundantProducer => {}
        }
    }
}
fields!(RewriteEvidenceKey {
    candidate,
    kind,
    producers
});
impl Retained for InputConstraint {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::AtMostOne { relation, group_by } => {
                relation.heap(p);
                group_by.heap(p);
            }
        }
    }
}
fields!(BackendIdentity {
    backend,
    configuration
});
fields!(ResourceReason { phase, resource });
fields!(Candidate { present, absent });
fields!(EvidenceKeys {
    instances,
    occurrences,
    providers,
    rewrites
});
impl Retained for UnsupportedReason {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::UnsettledNegativeCycle => {}
            Self::DependsOnUnsettled(k) => k.heap(p),
        }
    }
}
impl Retained for RegionCompletion {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::NoContradiction => {}
            Self::NoMeaning {
                candidate,
                evidence,
            } => {
                candidate.heap(p);
                evidence.heap(p);
            }
            Self::Deferred(k) => k.heap(p),
            Self::Inconclusive(r) => r.heap(p),
        }
    }
}
impl Retained for LocalScope {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Group(k) => k.heap(p),
            Self::Region(k) => k.heap(p),
        }
    }
}
fields!(LocalObligation {
    relation,
    group_by,
    domains
});
fields!(LocalComponent {
    recursive,
    blocked_by
});
fields!(LocalInput {
    completion_context,
    scope,
    roots,
    obligation,
    facts,
    possible,
    inputs,
    components,
    rules,
    original_dependencies,
    rewrites,
    domains,
    constraints,
    input_groups,
    request_scope,
    backend,
    limits,
    admission_limit
});
fields!(LocalCompletionContext {
    inputs,
    input_groups,
    proofs
});
fields!(LocalEvaluation {
    permitted,
    conditions,
    incomplete
});
impl Retained for OwnedCondition {
    fn heap(&self, p: &mut Payload) {
        slice(self.inputs(), p);
        p.add(
            self.retained_node_capacity()
                .saturating_mul(size_of::<(usize, usize, usize)>()),
        );
    }
}
impl Retained for LocalVerdict {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Proved => {}
            Self::Overlap(c) => c.heap(p),
            Self::Unsupported(r) => r.heap(p),
            Self::Inconclusive(r) => r.heap(p),
        }
    }
}
impl Retained for LocalAnswer {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Group(v) => v.heap(p),
            Self::Completion {
                outcome,
                bad_input,
                boundary,
            } => {
                outcome.heap(p);
                bad_input.heap(p);
                boundary.heap(p);
            }
        }
    }
}
fields!(LocalMemo {
    evaluation,
    answer,
    failure,
    evaluation_receipt,
    answer_receipt
});
fields!(ResourceKey { phase, resource });
fields!(WorkCharges {
    work,
    by_phase,
    resource_peaks,
    rejected_work,
    exhausted
});
fields!(WorkReceipt {
    allowance,
    own,
    dependencies
});
impl Retained for QueryKey {
    fn heap(&self, p: &mut Payload) {
        match self {
            Self::Preparation
            | Self::Admission
            | Self::CoverageMeaning
            | Self::Symbolic
            | Self::ConeIndex
            | Self::FindingContext => {}
            Self::Grounding(k) => k.heap(p),
            Self::Coverage(k) => k.heap(p),
            Self::ConeDiscovery(k)
            | Self::ConeEvaluation(k)
            | Self::FindingConversion(k)
            | Self::Property(k)
            | Self::Witness(k)
            | Self::Certification(k) => k.heap(p),
            Self::RegionDiscovery(k) | Self::RegionEvaluation(k) | Self::Completion(k) => k.heap(p),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn payload_counts_shared_owners_once_and_bdd_nodes_by_capacity() {
        let owner = OwnerKey::new("frontend", vec![7u8; 10000]);
        let shared = vec![owner.clone(); 100];
        let distinct = (0..100)
            .map(|_| OwnerKey::new("frontend", vec![7u8; 10000]))
            .collect::<Vec<_>>();
        assert_eq!(shared, distinct);
        assert!(bytes(&distinct) > bytes(&shared) * 10);
        assert!(bytes(&shared) >= 10000 + 100 * size_of::<OwnerKey>());
    }
}

fields!(JoinPlanSchema {
    positions,
    positives
});
fields!(PivotPlan {
    columns,
    steps,
    columns_work,
    steps_work
});
fields!(OwnedJoinPlan {
    schema,
    initialization_work,
    pivots
});

impl<T: Retained> Retained for &T {
    fn heap(&self, p: &mut Payload) {
        T::heap(*self, p);
    }
}
fields!(OwnedEvaluation {
    value,
    failure,
    receipt
});
fields!(OwnedAnswer {
    value,
    failure,
    receipt
});

impl Retained for WorkReceipts {
    fn heap(&self, p: &mut Payload) {
        for (key, value) in self.entries() {
            p.add(size_of::<(QueryKey, WorkReceipt)>() + 48);
            key.heap(p);
            value.heap(p);
        }
    }
}

fields!(RelationSchema { input, parameters });
fields!(GroundingInput {
    key,
    providers,
    relations,
    domains,
    rules,
    plans,
    limits
});
fields!(GroundingValue {
    possible,
    instances
});
fields!(GroundingResult {
    value,
    failure,
    receipt
});
