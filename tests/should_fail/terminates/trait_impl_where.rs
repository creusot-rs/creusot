// Similar to `trait_where.rs` but the where clause is only in the impl.
extern crate creusot_std;
use creusot_std::prelude::*;

// This trait is fine
pub trait Tr {
    #[logic]
    #[ensures(false)]
    fn f(&self);
}

impl Tr for i32 {
    // A too naive termination checker might accept this definition
    // because it just calls a parameter, the `f` provided by `i32: Tr`.
    // To prevent this, the termination checker resolves the call in the
    // typing context of the original function declaration (where there is no bound).
    #[logic]
    #[ensures(false)]
    fn f(&self)
    where
        i32: Tr,
    {
        self.f()
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    1i32.f()
}
