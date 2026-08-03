#![allow(unused)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[hybrid]
#[requires(x@ < i64::MAX@ - 1)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: i64) -> i64 {
    x + 1i64
}

#[requires(x@ < i64::MAX@ - 2)]
#[ensures(result == add_one(add_one(x)))]
pub fn add_two(x: i64) -> i64 {
    add_one(x) + 1
}

pub trait IsZero {
    #[hybrid]
    fn is_zero(&self) -> bool;
}

impl IsZero for i32 {
    #[hybrid]
    fn is_zero(&self) -> bool {
        *self == 0i32
    }
}

impl IsZero for i64 {
    #[hybrid]
    fn is_zero(&self) -> bool {
        *self == 0i64
    }
}

#[ensures(result == x.is_zero() || y.is_zero())]
pub fn are_zeros(x: i32, y: i64) -> bool {
    x.is_zero() || y.is_zero()
}

#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> elems@[i].is_zero())]
pub fn all_zeros<T: IsZero>(elems: &[T]) -> bool {
    let mut i = 0;

    while i < elems.len() {
        if !elems[i].is_zero() {
            return false;
        }
    }

    true
}

#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> !elems@[i].is_zero())]
pub fn no_zeros<T: IsZero>(elems: &[T]) -> bool {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> !produced[i].is_zero())]
    for elem in elems {
        if elem.is_zero() {
            return false;
        }
    }

    true
}

trait IsOne
where
    Self: View<ViewTy = Int>,
{
    #[hybrid]
    #[ensures(result == (self@ == 1))]
    fn is_one(&self) -> bool;
}

macro_rules! impl_is_one {
    ($t:ty, $one:expr) => {
        impl IsOne for $t {
            #[hybrid]
            #[ensures(result == (self@ == 1))]
            fn is_one(&self) -> bool {
                *self == $one
            }
        }
    };
}

impl_is_one!(i8, 1i8);
impl_is_one!(i16, 1i16);
impl_is_one!(i32, 1i32);
impl_is_one!(i64, 1i64);

impl_is_one!(u8, 1u8);
impl_is_one!(u16, 1u16);
impl_is_one!(u32, 1u32);
impl_is_one!(u64, 1u64);

#[ensures(result == forall<i> 0 <= i && i < elems@.len() ==> elems@[i].is_one())]
fn all_ones<T: View<ViewTy = Int> + IsOne>(elems: &[T]) -> bool {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i].is_one())]
    for elem in elems {
        if !elem.is_one() {
            return false;
        }
    }

    true
}

macro_rules! check_trait_select {
    ($name:ident, $from:ty, $to:ty) => {
        #[requires(forall<i> 0 <= i && i < elems@.len() ==> elems@[i].is_one())]
        #[ensures(forall<i> 0 <= i && i < result@.len() ==> result@[i].is_one())]
        fn $name(elems: &[$from]) -> Vec<$to> {
            elems.iter().map(|i| *i as $to).collect()
        }
    };
}

check_trait_select!(dummy_cast1, u8, i8);
check_trait_select!(dummy_cast2, u16, i16);
check_trait_select!(dummy_cast3, u32, i32);
check_trait_select!(dummy_cast4, u8, i64);
check_trait_select!(dummy_cast5, u8, i32);
