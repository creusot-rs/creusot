extern crate creusot_contracts;

use creusot_contracts::*;

trait Assoc {
    type Ty;
}

#[logic]
#[trusted]
fn from_ty<T: Assoc>(x: T::Ty) -> T {
    std::process::abort()
}

#[logic]
#[trusted]
fn to_ty<T: Assoc>(x: T) -> T::Ty {
    std::process::abort()
}

#[trusted]
#[ensures(a === from_ty(to_ty(a)))]
fn test<T: Assoc>(a: T) {}
