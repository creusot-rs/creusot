use indexmap::IndexMap;
use std::hash::Hash;

// A simple finite bijection between K and V
pub struct BiMap<K, V> {
    left: IndexMap<K, V>,
    right: IndexMap<V, K>,
}

impl<K: Clone + Hash + Eq, V: Clone + Hash + Eq> BiMap<K, V> {
    pub fn new() -> Self {
        BiMap { left: Default::default(), right: Default::default() }
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        let old_v = self.left.insert(k.clone(), v.clone());
        let old_k = self.right.insert(v, k);

        match (old_k, old_v) {
            (Some(k), Some(v)) => Some((k, v)),
            (None, None) => None,
            _ => unreachable!(""),
        }
    }

    pub fn remove_left(&mut self, k: &K) -> Option<(K, V)> {
        let old_v = self.left.remove(k)?;
        let old_k = self.right.remove(&old_v)?;

        Some((old_k, old_v))
    }

    #[allow(dead_code)]
    pub fn remove_right(&mut self, v: &V) -> Option<(K, V)> {
        let old_k = self.right.remove(v)?;
        let old_v = self.left.remove(&old_k)?;

        Some((old_k, old_v))
    }

    #[allow(dead_code)]
    pub fn lookup_left(&self, k: &K) -> Option<&V> {
        self.left.get(k)
    }

    pub fn lookup_right(&self, v: &V) -> Option<&K> {
        self.right.get(v)
    }
}
