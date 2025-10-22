extern crate creusot_contracts;
use creusot_contracts::{
    logic::{FSet, Mapping},
    prelude::*,
};

#[ensures(forall<xs: FSet<T>, f: Mapping<T, U>, y: U> xs.map(f).contains(y) == exists<x: T> xs.contains(x) && f.get(x) == y)]
pub fn map_spec<T, U>() {}

#[ensures(forall<xs: FSet<T>, f: Mapping<T, bool>, x: T> xs.filter(f).contains(x) == (xs.contains(x) && f.get(x)))]
pub fn filter_spec<T>() {}

#[ensures(forall<i, j, k> FSet::interval(i, j).contains(k) == (i <= k && k < j))]
pub fn interval_spec() {}
