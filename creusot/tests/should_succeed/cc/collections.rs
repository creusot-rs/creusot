extern crate creusot_contracts;
use creusot_contracts::*;
use std::{
    collections::{hash_map, HashMap, HashSet},
    hash::Hash,
};

#[trusted]
#[logic]
pub fn any<T>() -> T {
    dead
}

#[ensures(result@ == xs@)]
pub fn roundtrip_hashmap_into_iter<K: Eq + Hash + DeepModel, V>(
    xs: HashMap<K, V>,
) -> HashMap<K, V> {
    let it = xs.into_iter();
    let it0 = snapshot! { it };
    let r: HashMap<K, V> = it.collect();
    /*
    let x = snapshot! { such_that(|x: (Seq<(K,V)>, &mut hash_map::IntoIter<K, V>)| {
        let (prod, it1) = x;
        it1.completed()
            && it0.produces(prod, *it1)
    })}; */

    // epsilon
    let prod = snapshot! { any::<Seq<(K,V)>>() };
    let it1 = snapshot! { any::<&mut hash_map::IntoIter<K,V>>() };
    proof_assert! { it1.completed() };
    proof_assert! { it0.produces(prod.inner(), *it1.inner()) };

    proof_assert! { forall<k: K::DeepModelTy, v: V> r@.get(k) == Some(v) ==> exists<k1: K> k1.deep_model() == k && prod.inner().contains((k1, v))};
    proof_assert! { forall<k: K::DeepModelTy> xs@.contains(k) == r@.contains(k) };
    proof_assert! { forall<k: K::DeepModelTy> xs@.contains(k) ==> xs@[k] == r@[k] };
    r
}

#[ensures(forall<k: K::DeepModelTy, v: &V> (result@.get(k) == Some(v)) == (xs@.get(k) == Some(*v)))]
pub fn roundtrip_hashmap_iter<K: Eq + Hash + DeepModel, V>(xs: &HashMap<K, V>) -> HashMap<&K, &V> {
    let it = xs.iter();
    let it0 = snapshot! { it };
    let r: HashMap<&K, &V> = it.collect();

    // epsilon
    let prod = snapshot! { any::<Seq<(&K, &V)>>() };
    let it1 = snapshot! { any::<&mut hash_map::Iter<K,V>>() };
    proof_assert! { it1.completed() };
    proof_assert! { it0.produces(prod.inner(), *it1.inner()) };

    proof_assert! { forall<k: K::DeepModelTy, v: &V> r@.get(k) == Some(v) ==> exists<k1: &K> k1.deep_model() == k && prod.inner().contains((k1, v)) };
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

    // epsilon
    let prod = snapshot! { any::<Seq<(&K, &mut V)>>() };
    let it1 = snapshot! { any::<&mut hash_map::IterMut<K, V>>() };
    proof_assert! { it1.completed() };
    proof_assert! { it0.produces(prod.inner(), *it1.inner()) };

    proof_assert! { forall<k: K::DeepModelTy, v: &mut V> r@.get(k) == Some(v) ==> exists<k1: &K> k1.deep_model() == k && prod.inner().contains((k1, v)) };
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
