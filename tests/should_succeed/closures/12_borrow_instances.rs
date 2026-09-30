extern crate creusot_std;
use creusot_std::{mode::Mode, prelude::*, std::ops::*};

#[logic(open)]
#[ensures(FnExt::postcondition(x, n, r, mode) == FnExt::postcondition(*x, n, r, mode))]
#[ensures(forall<xx: &F> FnMutExt::postcondition_mut(x, n, xx, r, mode) == (FnExt::postcondition(*x, n, r, mode) && x == xx))]
#[ensures(FnOnceExt::postcondition_once(x, n, r, mode) == FnExt::postcondition(*x, n, r, mode))]
pub fn test1<F: Fn(u32) -> bool>(x: &F, n: (u32,), r: bool, mode: Mode) {}

#[logic(open)]
#[ensures(forall<xx: &mut F> FnMutExt::postcondition_mut(x, n, xx, r, mode) == (FnMutExt::postcondition_mut(*x, n, *xx, r, mode) && ^x == ^xx))]
#[ensures(FnOnceExt::postcondition_once(x, n, r, mode) == FnMutExt::postcondition_mut(*x, n, ^x, r, mode))]
pub fn test2<F: FnMut(u32) -> bool>(x: &mut F, n: (u32,), r: bool, mode: Mode) {}
