extern crate creusot_std;
use creusot_std::prelude::*;
use std::collections::{BTreeMap, btree_map};

// Basic operations: `insert`, `get`, `get_mut`, `remove`, `contains_key`, `len`, indexing
pub fn basic() {
    let mut m: BTreeMap<u32, u32> = BTreeMap::new();
    assert!(m.is_empty());
    assert!(m.insert(2, 20).is_none());
    assert!(m.insert(1, 10).is_none());
    assert!(m.insert(3, 30).is_none());
    assert!(m.insert(2, 21) == Some(20));
    assert!(m.len() == 3);
    assert!(m.get(&2) == Some(&21));
    assert!(m.get(&4).is_none());
    assert!(m[&3] == 30);

    if let Some(v) = m.get_mut(&1) {
        *v += 1;
    }
    assert!(m.get(&1) == Some(&11));

    assert!(m.remove(&3) == Some(30));
    assert!(!m.contains_key(&3));
    assert!(m.len() == 2);

    m.clear();
    assert!(m.is_empty());
}

// `first_key_value`, `last_key_value`, `pop_first` and `pop_last`
pub fn first_last() {
    let mut m: BTreeMap<u32, u32> = BTreeMap::new();
    m.insert(5, 50);
    m.insert(1, 10);
    m.insert(3, 30);
    assert!(m.first_key_value() == Some((&1, &10)));
    assert!(m.last_key_value() == Some((&5, &50)));
    assert!(m.pop_first() == Some((1, 10)));
    assert!(m.pop_last() == Some((5, 50)));
    assert!(m.len() == 1);
    assert!(m.pop_first() == Some((3, 30)));
    assert!(m.pop_last().is_none());
}

// Iteration happens in increasing key order
#[requires(m@.len() > 0)]
#[ensures(m@.contains(&result@))]
#[ensures(forall<k: Int> m@.contains(&k) ==> k <= result@)]
pub fn max_by_iteration(m: &BTreeMap<u64, u32>) -> u64 {
    let mut res = 0;
    let it = m.iter();
    let it0 = snapshot!(it);
    #[invariant(produced.len() > 0 ==> res@ == produced[produced.len() - 1].0@)]
    for (k, _) in it {
        res = *k;
    }
    proof_assert!(it0@.len() > 0 && res@ == it0@[it0@.len() - 1].0@);
    res
}

// `pop_first` drains a map in increasing key order
#[ensures(forall<i, j> 0 <= i && i < j && j < result@.len() ==> result[i]@ < result[j]@)]
pub fn drain_sorted(mut m: BTreeMap<u64, ()>) -> Vec<u64> {
    let mut res: Vec<u64> = Vec::new();
    #[invariant(forall<i, j> 0 <= i && i < j && j < res@.len() ==> res[i]@ < res[j]@)]
    #[invariant(forall<i, k: Int> 0 <= i && i < res@.len() && m@.contains(&k) ==> res[i]@ < k)]
    loop {
        match m.pop_first() {
            Some((k, ())) => res.push(k),
            None => break,
        }
    }
    res
}

// `iter_mut` updates every value
#[ensures(forall<k: Int> m@.contains(&k) == (^m)@.contains(&k))]
#[ensures(forall<k: Int> m@.contains(&k) ==> (^m)@[k]@ == 0)]
pub fn reset(m: &mut BTreeMap<u64, u32>) {
    let it = m.iter_mut();
    let it0 = snapshot!(it);
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> ^produced[i].1 == 0u32)]
    for (_, v) in it {
        *v = 0;
    }
    proof_assert!(forall<i> 0 <= i && i < it0@.len() ==> ^it0@[i].1 == 0u32);
}

// `range` only yields keys in the range, in increasing order
#[ensures(forall<i> 0 <= i && i < result@.len() ==> m@.contains(&result[i]@) && 10 <= result[i]@ && result[i]@ < 20)]
#[ensures(forall<i, j> 0 <= i && i < j && j < result@.len() ==> result[i]@ < result[j]@)]
pub fn range_keys(m: &BTreeMap<u64, u32>) -> Vec<u64> {
    let mut res: Vec<u64> = Vec::new();
    let it = m.range(10..20);
    let it0 = snapshot!(it);
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i] == it0@[i])]
    #[invariant(res@.len() == produced.len())]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> res[i] == *produced[i].0)]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==>
        m@.contains(&produced[i].0@) && 10 <= produced[i].0@ && produced[i].0@ < 20)]
    #[invariant(forall<i, j> 0 <= i && i < j && j < produced.len() ==> produced[i].0@ < produced[j].0@)]
    for (k, _) in it {
        res.push(*k);
    }
    res
}

#[ensures(result@ == xs@)]
pub fn roundtrip_into_iter(xs: BTreeMap<u64, u32>) -> BTreeMap<u64, u32> {
    let xs_snap = snapshot!(xs);
    let it = xs.into_iter();
    let it0 = snapshot!(it);
    let r: BTreeMap<u64, u32> = it.collect();
    proof_assert! {
        exists<prod: Seq<(u64, u32)>, it1: &mut btree_map::IntoIter<u64, u32>>
            it1.completed() && it0.produces(prod, *it1)
            && prod.len() == it0@.len() && (forall<i> 0 <= i && i < prod.len() ==> prod[i] == it0@[i]) &&
            forall<k: Int, v: u32> (r@.lookup(k) == Some(v))
                == exists<k1: u64> k1@ == k && prod.contains((k1, v))
    };
    proof_assert! { forall<k: Int> r@.contains(&k) == xs_snap@.contains(&k) };
    proof_assert! { forall<k: Int> r@[k] == xs_snap@[k] };
    proof_assert! { r@.ext_eq(xs_snap@) };
    r
}
