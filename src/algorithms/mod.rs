use std::collections::BTreeSet;

use crate::FormalContext;

pub mod next_closure;

impl<T> FormalContext<T> {
    pub fn index_concepts<'a>(
        &'a self,
    ) -> impl Iterator<Item = (BTreeSet<usize>, BTreeSet<usize>)> + 'a {
        next_closure::concepts(&self)
    }
}
