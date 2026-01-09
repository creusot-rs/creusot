extern crate creusot_std;

// Previously crashed creusot in the termination check, because of the missing `le` and `idemp` in the impl block.

use creusot_std::prelude::*;

pub trait RA: Sized {
    #[logic]
    fn op(self, other: Self) -> Option<Self>;

    #[logic]
    #[ensures(
        (forall<b: Self> ! (b.le(a) && b.idemp())) ||
        (exists<b: Self> b.le(a) && b.idemp() &&
           forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(a: Self);

    #[logic]
    fn le(self, other: Self) -> bool;

    #[logic]
    fn idemp(self) -> bool;
}

impl<T, U> RA for (T, U)
where
    T: RA,
    U: RA,
{
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        pearlite! {
            self.0.op(other.0).and_then_logic(|x:T| {
                self.1.op(other.1).and_then_logic(|y:U| {
                    Some((x, y))
                })
            })
        }
    }

    #[logic(open(self))]
    #[ensures(
        (forall<b: Self> ! (b.le(a) && b.idemp())) ||
        (exists<b: Self> b.le(a) && b.idemp() &&
           forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(a: Self) {}
}
