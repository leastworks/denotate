//! Copy-on-write prepared arrays. Branches share rules and atom metadata; only
//! explicitly edited solver views detach them.
use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};
#[derive(Clone, Debug)]
pub(super) struct Shared<T>(Arc<Vec<T>>);
impl<T> From<Vec<T>> for Shared<T> {
    fn from(v: Vec<T>) -> Self {
        Self(Arc::new(v))
    }
}
impl<T> FromIterator<T> for Shared<T> {
    fn from_iter<I: IntoIterator<Item = T>>(i: I) -> Self {
        Vec::from_iter(i).into()
    }
}
impl<T> Deref for Shared<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Vec<T> {
        &self.0
    }
}
impl<T: Clone> DerefMut for Shared<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        Arc::make_mut(&mut self.0)
    }
}
impl<'a, T> IntoIterator for &'a Shared<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
