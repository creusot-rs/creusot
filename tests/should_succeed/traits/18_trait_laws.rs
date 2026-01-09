extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Symmetric {
    // Hack: return type must be sized for `a.op(b) == b.op(a)` to typecheck
    #[logic]
    fn op(self, _: Self) -> &'static Self;

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn reflexive(a: Self, b: Self);
}

#[logic(open)]
#[ensures(result == true)]
pub fn uses_op<T: Symmetric>(x: T, y: T) -> bool {
    pearlite! { x.op(y) == y.op(x) }
}

impl Symmetric for () {
    #[logic(open)]
    fn op(self, _: Self) -> &'static Self {
        &()
    }

    #[logic(open, law)]
    #[ensures(a.op(b) == b.op(a))]
    fn reflexive(a: Self, b: Self) {}
}

#[logic(open)]
#[ensures(result == true)]
pub fn impl_laws() -> bool {
    pearlite! { ().op(()) == ().op(()) }
}
