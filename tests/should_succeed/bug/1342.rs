extern crate creusot_std;
use creusot_std::{logic::FSet, prelude::*};

#[logic(open)]
#[variant(fset.len())]
pub fn bar<T>(fset: FSet<T>) -> FSet<T> {
    if fset.is_empty() { FSet::empty() } else { bar(FSet::empty()) }
}
