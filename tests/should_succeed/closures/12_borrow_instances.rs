extern crate creusot_contracts;
use creusot_contracts::{prelude::*, std::ops::*};

#[logic(open)]
#[ensures(FnExt::postcondition(x, n, r) == FnExt::postcondition(*x, n, r))]
#[ensures(forall<xx: &F> FnMutExt::postcondition_mut(x, n, xx, r) == (FnExt::postcondition(*x, n, r) && x == xx))]
#[ensures(FnOnceExt::postcondition_once(x, n, r) == FnExt::postcondition(*x, n, r))]
pub fn test1<F: Fn(u32) -> bool>(x: &F, n: (u32,), r: bool) {}

#[logic(open)]
#[ensures(forall<xx: &mut F> FnMutExt::postcondition_mut(x, n, xx, r) == (FnMutExt::postcondition_mut(*x, n, *xx, r) && ^x == ^xx))]
#[ensures(FnOnceExt::postcondition_once(x, n, r) == FnMutExt::postcondition_mut(*x, n, ^x, r))]
pub fn test2<F: FnMut(u32) -> bool>(x: &mut F, n: (u32,), r: bool) {}
