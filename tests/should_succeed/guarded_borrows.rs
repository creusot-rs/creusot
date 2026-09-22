extern crate creusot_std;
use creusot_std::{invariant::Guarded, prelude::*};

#[ensures(^bor == 0i32)]
fn breaks_inv(bor: &mut i32) {
    *bor = 0;
}

#[ensures(guarded.guard()[guarded.inner])]
#[check(ghost)]
fn takes_guarded(guarded: Guarded<&mut i32>) {}

#[ensures(result == 1i32)]
pub fn example() -> i32 {
    let mut x = 1i32;
    let bor = &mut x;

    let guarded = Guarded::new(bor, snapshot!(|x| x == 1i32));

    breaks_inv(guarded.inner);

    *guarded.inner = 1i32;

    takes_guarded(guarded);

    x
}

#[ensures(^bor == 0i32)]
fn breaks_inv_ghost(mut bor: Ghost<&mut i32>) {
    ghost! { **bor = 0 };
}

#[ensures(*result == 1i32)]
pub fn ghostified() -> Ghost<i32> {
    let mut x = ghost!(1i32);
    let bor = ghost!(&mut *x);

    let mut guarded = ghost!(Guarded::new(bor.into_inner(), snapshot!(|x| x == 1i32)));
    ghost_let!(mut borrow = &mut *guarded.inner);

    breaks_inv_ghost(ghost!(&mut **borrow));

    // do some program step here...

    ghost! { **borrow = 1i32 }; // the guard _has_ to be restored through the reborrow

    ghost! { takes_guarded(guarded.into_inner()) };

    x
}

pub struct SumSmaller10 {
    pub a: u32,
    pub b: u32,
}

impl Invariant for SumSmaller10 {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ <= 10 }
    }
}

impl SumSmaller10 {
    #[ensures(result.guard() == |a: &mut u32| a@ + self.b@ <= 10)]
    #[ensures(*result.inner == self.a)]
    #[ensures((^self).b == (*self).b)]
    #[ensures((^self).a == ^result.inner)]
    pub fn get_a_mut(&mut self) -> Guarded<&mut u32> {
        let g = snapshot!(|a: u32| a@ + self.b@ <= 10);
        Guarded::new(&mut self.a, g)
    }

    #[requires(self.a@ + self.b@ <= 5)]
    #[ensures(result.guard() == |a: &mut u32| a@ + self.b@ <= 5)]
    #[ensures(*result.inner == self.a)]
    #[ensures((^self).b == (*self).b)]
    #[ensures((^self).a == ^result.inner)]
    pub fn get_a_mut_5(&mut self) -> Guarded<&mut u32> {
        let g = snapshot!(|a: u32| a@ + self.b@ <= 5);
        let a = self.get_a_mut(); // We refine the Guarded returned by `get_a_mut`.
        Guarded::new(&mut *a.inner, g)
    }

    #[requires(self.a@ + self.b@ <= 5)]
    #[ensures((^self).a@ + (^self).b@ == 5)]
    #[ensures((^self).b == (*self).b)]
    pub fn eq_5(&mut self) {
        let b = self.b;
        let a = &mut *self.get_a_mut_5().inner;
        *a = 42;
        *a = 5 - b;
    }
}
