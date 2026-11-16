use super::*;
use crate::guarded_bounds::DeadReason;

/// One original component snapshot, shared by every replacement in its atomic
/// batch. It is not a collection of independently installable edge proofs.
#[derive(Debug, Clone)]
pub struct JointCertificate {
    pub snapshot: u64,
    pub component: ComponentId,
    pub producers: Vec<Arc<ProducerSummary>>,
    pub tree: GuardedCertificate,
    // Immutable shared storage: do not traverse it once per replaced occurrence.
    pub(crate) retained_nodes: usize,
}
impl JointCertificate {
    pub(crate) fn nodes(&self) -> usize {
        self.retained_nodes
    }
}

/// A candidate tree proves one premise; a joint component tree proves all atoms
/// together. Splits use globally settled atoms; graph scores are not evidence.
#[derive(Debug, Clone)]
pub enum GuardedCertificate {
    Joint(Arc<JointCertificate>),
    /// Topological evaluation of the original, unrelaxed graph. Dead producers
    /// and their reasons remain evidence even though their edges were dropped.
    Acyclic {
        domain: Condition,
        steps: Vec<GuardedSettlementStep>,
        values: BTreeMap<GroundAtom, Condition>,
        pruning: BTreeMap<GroundRuleId, DeadReason>,
    },
    Leaf {
        bounds: Arc<GuardedBounds>,
        steps: Vec<GuardedSettlementStep>,
    },
    Split {
        atom: GroundAtom,
        when_true: Box<Self>,
        when_false: Box<Self>,
    },
    /// No permitted world reaches this branch, so no atom certificate is needed.
    Empty {
        domain: Condition,
    },
}
impl GuardedCertificate {
    pub fn walk(&self) -> impl Iterator<Item = &Self> {
        let mut pending = vec![self];
        std::iter::from_fn(move || {
            let node = pending.pop()?;
            if let Self::Joint(joint) = node {
                pending.push(&joint.tree);
            }
            if let Self::Split {
                when_true,
                when_false,
                ..
            } = node
            {
                pending.push(when_false);
                pending.push(when_true);
            }
            Some(node)
        })
    }
    pub fn bounds(&self) -> impl Iterator<Item = &GuardedBounds> {
        self.walk().filter_map(|node| match node {
            Self::Leaf { bounds, .. } => Some(bounds.as_ref()),
            _ => None,
        })
    }
    pub(crate) fn summaries(&self) -> impl Iterator<Item = &ProducerSummary> {
        self.bounds()
            .flat_map(|b| b.cone.summaries())
            .chain(self.walk().flat_map(|c| {
                match c {
                    Self::Joint(j) => Some(j.producers.iter().map(AsRef::as_ref)),
                    _ => None,
                }
                .into_iter()
                .flatten()
            }))
    }
    pub(crate) fn nodes(&self) -> usize {
        if let Self::Joint(joint) = self {
            return 2 + joint.nodes();
        }
        self.walk()
            .map(|node| match node {
                Self::Leaf { bounds, .. } => bounds.nodes(),
                Self::Joint(j) => 4 + j.producers.iter().map(|p| p.nodes()).sum::<usize>(),
                Self::Acyclic {
                    domain,
                    steps,
                    values,
                    pruning,
                } => {
                    domain.node_count()
                        + values.values().map(Condition::node_count).sum::<usize>()
                        + steps
                            .iter()
                            .map(|s| 2 + s.expression.nodes() + s.producers.len())
                            .sum::<usize>()
                        + pruning
                            .values()
                            .map(|r| {
                                3 + match r {
                                    DeadReason::Negative {
                                        exact_producers, ..
                                    } => exact_producers.len(),
                                    _ => 0,
                                }
                            })
                            .sum::<usize>()
                }
                Self::Split { .. } => 3,
                Self::Empty { domain } => 1 + domain.node_count(),
            })
            .sum()
    }
    pub(crate) fn expression_nodes(&self) -> usize {
        self.walk()
            .map(|node| match node {
                Self::Leaf { steps, .. } | Self::Acyclic { steps, .. } => {
                    steps.iter().map(|s| s.expression.nodes()).sum()
                }
                _ => 1,
            })
            .sum()
    }
    pub(crate) fn domains(&self) -> impl Iterator<Item = &Condition> {
        self.walk().filter_map(|node| match node {
            Self::Leaf { bounds, .. } => Some(&bounds.cone.domain),
            Self::Acyclic { domain, .. } => Some(domain),
            Self::Empty { domain } => Some(domain),
            _ => None,
        })
    }
    pub(crate) fn values(&self) -> impl Iterator<Item = &Condition> {
        self.walk().flat_map(|node| {
            match node {
                Self::Acyclic { values, .. } => Some(values.values()),
                _ => None,
            }
            .into_iter()
            .flatten()
        })
    }
}

/// Unsigned meaning of the target atom on the certificate's domain. Temporary
/// marks are gone; only this owned certificate and condition remain charged.
pub(super) struct Settlement {
    pub expression: Expr,
    pub truth: Condition,
    pub certificate: GuardedCertificate,
}
impl Settlement {
    pub fn nodes(&self) -> usize {
        self.certificate.nodes() + self.truth.node_count()
    }
}
