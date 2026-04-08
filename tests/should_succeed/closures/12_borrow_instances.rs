extern crate creusot_std;
use creusot_std::{mode::Mode, prelude::*, std::ops::*};

#[logic(open)]
#[ensures(forall<mode: Mode> FnExt::postcondition(x, mode, n, r) == FnExt::postcondition(*x, mode, n, r))]
#[ensures(forall<mode: Mode> forall<xx: &F> FnMutExt::postcondition_mut(x, mode, n, xx, r) == (FnExt::postcondition(*x, mode, n, r) && x == xx))]
#[ensures(forall<mode: Mode> FnOnceExt::postcondition_once(x, mode, n, r) == FnExt::postcondition(*x, mode, n, r))]
pub fn test1<F: Fn(u32) -> bool>(x: &F, n: (u32,), r: bool) {}

#[logic(open)]
#[ensures(forall<mode: Mode> forall<xx: &mut F> FnMutExt::postcondition_mut(x, mode, n, xx, r) == (FnMutExt::postcondition_mut(*x, mode, n, *xx, r) && ^x == ^xx))]
#[ensures(forall<mode: Mode> FnOnceExt::postcondition_once(x, mode, n, r) == FnMutExt::postcondition_mut(*x, mode, n, ^x, r))]
pub fn test2<F: FnMut(u32) -> bool>(x: &mut F, n: (u32,), r: bool) {}
