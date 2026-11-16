use super::*;

/// Each leaf proves the same premise in its own restricted domain. Splits are
/// over globally settled atoms; graph scores are deliberately absent here.
#[derive(Debug, Clone)]
pub enum GuardedCertificate {
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
    Empty { domain: Condition },
}
impl GuardedCertificate {
    pub fn walk(&self) -> impl Iterator<Item = &Self> {
        let mut pending = vec![self];
        std::iter::from_fn(move || {
            let node = pending.pop()?;
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
        self.bounds().flat_map(|b| b.cone.summaries())
    }
    pub(crate) fn nodes(&self) -> usize {
        self.walk()
            .map(|node| match node {
                Self::Leaf { bounds, .. } => bounds.nodes(),
                Self::Split { .. } => 3,
                Self::Empty { domain } => 1 + domain.node_count(),
            })
            .sum()
    }
    pub(crate) fn expression_nodes(&self) -> usize {
        self.walk()
            .map(|node| match node {
                Self::Leaf { steps, .. } => steps.iter().map(|s| s.expression.nodes()).sum(),
                _ => 1,
            })
            .sum()
    }
    pub(crate) fn domains(&self) -> impl Iterator<Item = &Condition> {
        self.walk().filter_map(|node| match node {
            Self::Leaf { bounds, .. } => Some(&bounds.cone.domain),
            Self::Empty { domain } => Some(domain),
            _ => None,
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
