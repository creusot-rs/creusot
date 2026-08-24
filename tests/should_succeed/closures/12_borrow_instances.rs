extern crate creusot_std;
use creusot_std::{prelude::*, std::ops::*};

#[logic(open)]
#[ensures(|_, mode| FnExt::postcondition(x, mode, n, r) == FnExt::postcondition(*x, mode, n, r))]
#[ensures(|_, mode| forall<xx: &F> FnMutExt::postcondition_mut(x, mode, n, xx, r) == (FnExt::postcondition(*x, mode, n, r) && x == xx))]
#[ensures(|_, mode| FnOnceExt::postcondition_once(x, mode, n, r) == FnExt::postcondition(*x, mode, n, r))]
pub fn test1<F: Fn(u32) -> bool>(x: &F, n: (u32,), r: bool) {}

#[logic(open)]
#[ensures(|_, mode| forall<xx: &mut F> FnMutExt::postcondition_mut(x, mode, n, xx, r) == (FnMutExt::postcondition_mut(*x, mode, n, *xx, r) && ^x == ^xx))]
#[ensures(|_, mode| FnOnceExt::postcondition_once(x, mode, n, r) == FnMutExt::postcondition_mut(*x, mode, n, ^x, r))]
pub fn test2<F: FnMut(u32) -> bool>(x: &mut F, n: (u32,), r: bool) {}
