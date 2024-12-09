use bit_set::BitSet;

use crate::FormalContext;

pub mod next_closure;

pub mod fcbo;

pub mod canonical_basis;

impl<T> FormalContext<T> {
    pub fn index_concepts<'a>(
        &'a self,
    ) -> impl Iterator<Item = (BitSet, BitSet)> + 'a {
        next_closure::concepts(&self)
    }
}

impl<T> FormalContext<T> {
    pub fn fcbo_index_concepts<'a>(
        &'a self,
    ) -> impl Iterator<Item = (BitSet, BitSet)> + 'a {
        fcbo::fcbo_concepts(&self)
    }
}

impl<T> FormalContext<T> {
    pub fn canonical_basis<'a>(
        &'a self,
    ) -> Vec<(BitSet, BitSet)> {
        canonical_basis::canonical_basis(&self)
    }
}