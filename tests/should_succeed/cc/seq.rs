extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(*result == 1usize)]
pub fn f() -> Ghost<usize> {
    ghost! {
        let mut x = 0;
        let mut s = Seq::new().into_inner();
        s.push_front_ghost(&mut x);
        **s.get_mut_ghost(*Int::new(0)).unwrap() = 1;
        x
    }
}

#[requires(s.len() >= 1)]
#[ensures(s[0..1].len() == 1)]
#[ensures(s[0..=0].len() == 1)]
#[ensures(s[0..] == s)]
#[ensures(s[..0].len() == 0)]
#[ensures(s[..=0].len() == 1)]
#[ensures(s[..] == s)]
pub fn g(s: Seq<Int>) {}
