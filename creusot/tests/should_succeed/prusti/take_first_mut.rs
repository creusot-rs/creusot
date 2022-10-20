extern crate creusot_contracts;
use creusot_contracts::prusti::*;
use ::std::mem;

#[requires((@**s).len() > 0)]
#[ensures(*result == old((@**s)[0]))]
#[ensures(@**s == old((@**s).subsequence(1, (@**s).len())))]
//#[after_expiry<'i>(@*old(*s) == before_expiry(Seq::singleton(*result).concat(@*curr(*s))))]  // Note this needs new syntax `curr`
pub fn take_first_mut<'i, 'o, T>(s: &'o mut &'i mut [T]) -> &'i mut T {
    let (first, rem) = mem::take(s).split_first_mut().unwrap();
    *s = rem;
    first
}