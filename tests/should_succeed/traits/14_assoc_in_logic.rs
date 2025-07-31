extern crate creusot_contracts;

use creusot_contracts::*;

pub trait Assoc {
    type Ty;
}

#[logic]
#[trusted]
pub fn from_ty<T: Assoc>(_x: T::Ty) -> T {
    dead
}

#[logic]
#[trusted]
pub fn to_ty<T: Assoc>(_x: T) -> T::Ty {
    dead
}

#[trusted]
#[ensures(_a == from_ty(to_ty(_a)))]
pub fn test<T: Assoc>(_a: T) {}
