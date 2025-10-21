extern crate creusot_contracts;
use creusot_contracts::prelude::*;

// The standard minimal two-phase borrow example
#[ensures((^v)[v@.len()]@ == v@.len())]
pub fn test(v: &mut Vec<usize>) {
    v.push(v.len());
}

// A more involved example from issue #668 which resulted in ill-typed code
pub struct VacantEntry<'a, K> {
    map: &'a mut Vec<K>,
    key: K,
    index: usize,
}

impl<K> VacantEntry<'_, K>
where
    K: Clone,
{
    pub fn insert(&mut self) {
        self.map.insert(self.index, self.key.clone())
    }
}
