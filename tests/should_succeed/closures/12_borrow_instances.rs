extern crate creusot_std;
use creusot_std::{prelude::*, std::ops::*};

#[logic(open)]
#[ensures(|_, mode| FnExt::postcondition(x, n, r, mode) == FnExt::postcondition(*x, n, r, mode))]
#[ensures(|_, mode| forall<xx: &F> FnMutExt::postcondition_mut(x, n, xx, r, mode) == (FnExt::postcondition(*x, n, r, mode) && x == xx))]
#[ensures(|_, mode| FnOnceExt::postcondition_once(x, n, r, mode) == FnExt::postcondition(*x, n, r, mode))]
pub fn test1<F: Fn(u32) -> bool>(x: &F, n: (u32,), r: bool) {}

#[logic(open)]
#[ensures(|_, mode| forall<xx: &mut F> FnMutExt::postcondition_mut(x, n, xx, r, mode) == (FnMutExt::postcondition_mut(*x, n, *xx, r, mode) && ^x == ^xx))]
#[ensures(|_, mode| FnOnceExt::postcondition_once(x, n, r, mode) == FnMutExt::postcondition_mut(*x, n, ^x, r, mode))]
pub fn test2<F: FnMut(u32) -> bool>(x: &mut F, n: (u32,), r: bool) {}
