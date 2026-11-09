extern crate creusot_std;
use creusot_std::prelude::*;
use std::collections::BTreeMap;

// Inserting a fresh key adds exactly that binding
#[requires(!m@.contains(&k@))]
#[ensures((^m)@.lookup(k@) == Some(v))]
#[ensures(forall<k2: Int> k2 != k@ ==> (^m)@.lookup(k2) == m@.lookup(k2))]
#[ensures((^m)@.len() == m@.len() + 1)]
pub fn insert_fresh(m: &mut BTreeMap<u64, u32>, k: u64, v: u32) {
    let old = m.insert(k, v);
    assert!(old.is_none());
}

// Inserting an existing key replaces its value, returns the old one, and keeps the length
#[requires(m@.contains(&k@))]
#[ensures(result == m@[k@])]
#[ensures((^m)@.lookup(k@) == Some(v))]
#[ensures(forall<k2: Int> k2 != k@ ==> (^m)@.lookup(k2) == m@.lookup(k2))]
#[ensures((^m)@.len() == m@.len())]
pub fn replace(m: &mut BTreeMap<u64, u32>, k: u64, v: u32) -> u32 {
    match m.insert(k, v) {
        Some(old) => old,
        None => unreachable!(),
    }
}

// A value can be looked up right after it is inserted, by `get`, `contains_key` and indexing
pub fn insert_then_lookup(m: &mut BTreeMap<u64, u32>, k: u64, v: u32) {
    m.insert(k, v);
    assert!(m.get(&k) == Some(&v));
    assert!(m.contains_key(&k));
    assert!(m[&k] == v);
}

// Inserting a key does not change the bindings of other keys
#[requires(k1 != k2)]
pub fn insert_preserves_others(m: &mut BTreeMap<u64, u32>, k1: u64, k2: u64, v: u32) {
    let before = m.get(&k2).copied();
    m.insert(k1, v);
    assert!(m.get(&k2).copied() == before);
}

// `get` agrees with the model, both for present and absent keys
#[ensures(match result {
    Some(v) => m@.lookup(k@) == Some(v),
    None => !m@.contains(&k@),
})]
pub fn lookup(m: &BTreeMap<u64, u32>, k: u64) -> Option<u32> {
    m.get(&k).copied()
}

// Indexing returns the bound value
#[requires(m@.contains(&k@))]
#[ensures(result == m@[k@])]
pub fn index(m: &BTreeMap<u64, u32>, k: u64) -> u32 {
    m[&k]
}

// Updating through `get_mut` is the same as inserting
#[requires(m@.contains(&k@))]
#[ensures((^m)@ == m@.add(k@, v))]
pub fn update_via_get_mut(m: &mut BTreeMap<u64, u32>, k: u64, v: u32) {
    match m.get_mut(&k) {
        Some(r) => *r = v,
        None => unreachable!(),
    }
}

// Removing returns the binding and erases it
#[ensures(result == m@.lookup(k@))]
#[ensures(!(^m)@.contains(&k@))]
#[ensures(forall<k2: Int> k2 != k@ ==> (^m)@.lookup(k2) == m@.lookup(k2))]
pub fn remove(m: &mut BTreeMap<u64, u32>, k: u64) -> Option<u32> {
    m.remove(&k)
}

// Insertion is generic over any key type with an `Ord` implementation
#[ensures((^m)@.lookup(k.deep_model()) == Some(v))]
#[ensures(result == m@.lookup(k.deep_model()))]
pub fn insert_generic<K: Ord + DeepModel, V>(m: &mut BTreeMap<K, V>, k: K, v: V) -> Option<V> {
    m.insert(k, v)
}
