extern crate creusot_std;
use creusot_std::prelude::*;
use std::{
    collections::{HashMap, HashSet, hash_map},
    hash::Hash,
};

#[logic(opaque)]
pub fn any<T>() -> T {
    dead
}

#[ensures(result@ == xs@)]
pub fn roundtrip_hashmap_into_iter<K: Eq + Hash + DeepModel, V>(
    xs: HashMap<K, V>,
) -> HashMap<K, V> {
    let xs_snap = snapshot!(xs);
    let it = xs.into_iter();
    let it0 = snapshot! { it };
    let r: HashMap<K, V> = it.collect();
    proof_assert! {
        exists<prod: Seq<(K, V)>, it1: &mut hash_map::IntoIter<K, V>>
            it1.completed() && it0.produces(prod, *it1) &&
            forall<k: K::DeepModelTy, v: V> (r@.get(k) == Some(v))
                == exists<k1: K> k1.deep_model() == k && prod.contains((k1, v))
    };
    proof_assert! { forall<k: K::DeepModelTy> r@.contains(k) == (*xs_snap)@.contains(k) };
    proof_assert! { forall<k: K::DeepModelTy> r@[k] == (*xs_snap)@[k] };
    proof_assert! { r@.ext_eq(xs_snap@) };
    r
}

#[ensures(forall<k: K::DeepModelTy, v: &V> (result@.get(k) == Some(v)) == (xs@.get(k) == Some(*v)))]
pub fn roundtrip_hashmap_iter<K: Eq + Hash + DeepModel, V>(xs: &HashMap<K, V>) -> HashMap<&K, &V> {
    let it = xs.iter();
    let it0 = snapshot! { it };
    let r: HashMap<&K, &V> = it.collect();

    proof_assert! {
    exists<prod: Seq<(&K, &V)>, it1: &mut hash_map::Iter<K,V>>
        it1.completed() && it0.produces(prod, *it1)
        && forall<k: K::DeepModelTy, v: &V> (r@.get(k) == Some(v))
            == exists<k1: &K> k1.deep_model() == k && prod.contains((k1, v)) };
    r
}

#[ensures(forall<k: K::DeepModelTy, v: &mut V> result@.get(k) == Some(v) ==> xs@.get(k) == Some(*v) && (^xs)@.get(k) == Some(^v))]
#[ensures(forall<k: K::DeepModelTy, v: V> xs@.get(k) == Some(v) ==> result@.contains(k) && *result@[k] == v)]
#[ensures(forall<k: K::DeepModelTy, v: V> (^xs)@.get(k) == Some(v) ==> result@.contains(k) && ^result@[k] == v)]
pub fn roundtrip_hashmap_iter_mut<K: Eq + Hash + DeepModel, V>(
    xs: &mut HashMap<K, V>,
) -> HashMap<&K, &mut V> {
    let it = xs.iter_mut();
    let it0 = snapshot! { it };
    let r: HashMap<&K, &mut V> = it.collect();
    proof_assert! {
        exists<prod: Seq<(&K, &mut V)>, it1: &mut hash_map::IterMut<K, V>>
            it1.completed() && it0.produces(prod, *it1)
            && forall<k: K::DeepModelTy, v: &mut V> (r@.get(k) == Some(v))
                == exists<k1: &K> k1.deep_model() == k && prod.contains((k1, v))
    };
    r
}

#[ensures(result@ == xs@)]
pub fn roundtrip_hashset_into_iter<T: Eq + Hash + DeepModel>(xs: HashSet<T>) -> HashSet<T> {
    xs.into_iter().collect()
}

#[ensures(result@ == xs@)]
pub fn roundtrip_hashset_iter<T: Eq + Hash + DeepModel>(xs: &HashSet<T>) -> HashSet<&T> {
    xs.iter().collect()
}

#[ensures(result@ == xs@.intersection(ys@))]
pub fn hashset_intersection<T: Eq + Hash + Copy + DeepModel>(
    xs: &HashSet<T>,
    ys: &HashSet<T>,
) -> HashSet<T> {
    xs.intersection(ys).copied().collect()
}

#[ensures(result@ == xs@.difference(ys@))]
pub fn hashset_difference<T: Eq + Hash + Copy + DeepModel>(
    xs: &HashSet<T>,
    ys: &HashSet<T>,
) -> HashSet<T> {
    xs.difference(ys).copied().collect()
}
