extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Assoc {
    type Ty;
}

#[logic(opaque)]
pub fn from_ty<T: Assoc>(_x: T::Ty) -> T {
    dead
}

#[logic(opaque)]
pub fn to_ty<T: Assoc>(_x: T) -> T::Ty {
    dead
}

#[trusted]
#[ensures(_a == from_ty(to_ty(_a)))]
pub fn test<T: Assoc>(_a: T) {}
