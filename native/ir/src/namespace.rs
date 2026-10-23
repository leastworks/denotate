use crate::ConstructionError;
use std::sync::Arc;

/// An IR namespace path, independent of files, source origins and helper labels.
/// Segments are decoded names: `["a", "b"]` differs from `["a::b"]`.
/// The empty path is the global namespace. Text parsing/escaping belongs to the
/// frontend; this type never splits a string on `::`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Namespace(Arc<[String]>);

impl Namespace {
    pub fn new(
        segments: impl IntoIterator<Item = impl Into<String>>,
    ) -> Result<Self, ConstructionError> {
        let segments: Vec<String> = segments.into_iter().map(Into::into).collect();
        if segments.iter().any(String::is_empty) {
            return Err(ConstructionError::EmptyName("namespace segment"));
        }
        Ok(Self(segments.into()))
    }

    pub fn segments(&self) -> &[String] {
        &self.0
    }

    pub fn is_global(&self) -> bool {
        self.0.is_empty()
    }
}

impl From<&Namespace> for Namespace {
    fn from(namespace: &Namespace) -> Self {
        namespace.clone()
    }
}
