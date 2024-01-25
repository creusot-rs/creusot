#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn deref1<'a, T>(x: Box<&'a T>) -> &'a T {
    *x
}

#[open]
#[logic]
pub fn deref2<'a, T>(x: &'a Box<&'a Box<T>>) -> Box<T> {
    ***x
}

#[trusted]
#[open]
#[logic()]
pub fn deref3<T>() -> Box<T> {
    absurd
}

pub trait MkRef {
    #[open]
    #[logic]
    fn mk_ref(&self) -> &Self {
        self
    }
}

impl<T> MkRef for T {}

#[open]
#[logic]
pub fn deref4<'a, 'b, T>(x: &'a Box<&'b Box<T>>) -> &'b T {
    (***x).mk_ref()
}

#[after_expiry('a, **x == 0u32)]
pub fn deref5<'a>(x: &'static Box<u32>, y: &'a u32) -> &'a u32 {
    x
}

#[open]
#[logic]
pub fn deref7<'a, 'b, T>(x: &'a &'b mut T) -> &'a T {
    x.mk_ref()
}

pub struct X(u32, u32);

#[ensures(result == *old(x.0.mk_ref()))]
pub fn project_ref<'a>(x: &'a X) -> u32 {
    x.0
}

#[ensures(result == *old(x.0.mk_ref()))]
pub fn project_tuple_ref<'a>(x: &'a (u32, u32)) -> u32 {
    x.0
}

#[ensures(result == old(x.0))]
pub fn project_tuple_box<'a>(x: Box<(u32, u32)>) -> u32 {
    (*x).0
}

#[open]
#[logic]
pub fn let_ref<'a>(x: &'a (u32, u32)) -> &'a u32 {
    let (x, _) = x;
    x
}
