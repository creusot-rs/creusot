extern crate creusot_contracts;
use creusot_contracts::*;

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
