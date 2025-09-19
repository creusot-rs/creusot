extern crate creusot_contracts;
use creusot_contracts::{logic::FSet, *};

#[logic(open)]
#[variant(fset.len())]
pub fn bar<T>(fset: FSet<T>) -> FSet<T> {
    if fset.is_empty() { FSet::empty() } else { bar(FSet::empty()) }
}
