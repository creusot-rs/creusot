extern crate creusot_contracts;

pub struct VecMap<K, V>
where
    K: Eq + Ord,
{
    pub v: Vec<(K, V)>,
}

impl<K: Ord + Eq, V> ::std::default::Default for VecMap<K, V> {
    fn default() -> Self {
        Self { v: Vec::new() }
    }
}
