//! Lowerer-supplied scheduling metadata; it adds no relational truth.
use super::*;
use denotate_check::{CheckError, GroundAtom};
use denotate_ir::{Corpus, QualifiedKey, RelationRole, SemanticKeys};

/// One pure, one-shot computation. Its results are declared input atoms in the
/// relational model, but are not entry inputs of the executable plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Task {
    pub key: QualifiedKey,
    /// None means unconditional. False skips the callback and supplies false for
    /// every result. The resulting complete observation must satisfy selected W.
    pub when: Option<GroundAtom>,
    /// Ordered Boolean arguments (finite value encodings are ordinary atoms).
    pub arguments: Vec<GroundAtom>,
    pub results: Vec<GroundAtom>,
    pub sources: BTreeSet<RuleKey>,
}
/// Semantic-key form embedded in a plan. No arena IDs escape the builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    pub task: QualifiedKey,
    pub when: Option<AtomKey>,
    pub arguments: Vec<AtomKey>,
    pub results: BTreeSet<AtomKey>,
}
impl Call {
    pub(super) fn dependencies(&self, inactive: bool) -> BTreeSet<AtomKey> {
        self.when
            .iter()
            .cloned()
            .chain(self.arguments.iter().filter(|_| !inactive).cloned())
            .collect()
    }
}
/// Actual callback invocation. It receives only declared arguments, never a
/// complete input snapshot or future results. Pure deterministic callbacks required.
#[derive(Debug)]
pub struct Invocation {
    pub task: QualifiedKey,
    pub arguments: Vec<(AtomKey, bool)>,
    pub results: BTreeSet<AtomKey>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaskEvent {
    pub task: QualifiedKey,
    pub invoked: bool,
    pub results: BTreeMap<AtomKey, bool>,
}
#[derive(Default)]
pub(super) struct Tasks {
    pub by_result: BTreeMap<AtomKey, Call>,
    pub sources: BTreeMap<AtomKey, BTreeSet<RuleKey>>,
    pub atoms: BTreeMap<AtomKey, GroundAtom>,
    pub edges: BTreeMap<GroundAtom, Vec<GroundAtom>>,
}
impl Tasks {
    pub fn prepare(
        corpus: &Corpus,
        keys: &SemanticKeys,
        tasks: &[Task],
        budget: &mut crate::build::Work<'_>,
    ) -> Result<Self, CheckError> {
        let mut out = Self::default();
        let mut names = BTreeSet::new();
        for t in tasks {
            budget.tick(t.arguments.len() + t.results.len() + t.sources.len() + 1)?;
            if !names.insert(t.key.clone()) || t.results.is_empty() {
                return Err(CheckError::InvalidRequest(
                    "task needs a unique key and nonempty results",
                ));
            }
            for source in &t.sources {
                keys.bindings()
                    .resolve(&denotate_ir::OccurrenceKey::Rule(source.clone()))?;
            }
            let mut results = BTreeSet::new();
            for a in &t.results {
                if corpus
                    .relation(a.relation)
                    .is_none_or(|r| r.role != RelationRole::Input)
                {
                    return Err(CheckError::InvalidRequest(
                        "task results must be input atoms",
                    ));
                }
                if !results.insert(AtomKey::from_atom(keys, a)?) {
                    return Err(CheckError::InvalidRequest("duplicate task result"));
                }
            }
            let call = Call {
                task: t.key.clone(),
                when: t
                    .when
                    .as_ref()
                    .map(|a| AtomKey::from_atom(keys, a))
                    .transpose()?,
                arguments: t
                    .arguments
                    .iter()
                    .map(|a| AtomKey::from_atom(keys, a))
                    .collect::<Result<_, _>>()?,
                results,
            };
            for a in t.arguments.iter().chain(t.when.iter()).chain(&t.results) {
                out.atoms.insert(AtomKey::from_atom(keys, a)?, a.clone());
            }
            for a in &t.results {
                budget.tick(t.arguments.len() + t.results.len() + t.sources.len() + 1)?;
                let k = AtomKey::from_atom(keys, a)?;
                if out.by_result.insert(k.clone(), call.clone()).is_some() {
                    return Err(CheckError::InvalidRequest(
                        "input atom has multiple task producers",
                    ));
                }
                out.sources.insert(k, t.sources.clone());
                out.edges.insert(
                    a.clone(),
                    t.arguments
                        .iter()
                        .chain(t.when.iter())
                        .chain(&t.results)
                        .cloned()
                        .collect(),
                );
            }
        }
        Ok(out)
    }
}
