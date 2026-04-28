// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod p {
    use creusot_std::prelude::*;

    pub struct S(u64);

    impl Invariant for S {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                self.0@ != 0
            }
        }
    }

    // Must fail to prove the invariant
    pub const C: S = S(0);
}

// Don't translate non-visible constructor of S:
// replace with an opaque constant and emit a warning.
pub const D: p::S = p::C;

#[ensures(result == D)]
pub fn f() -> p::S {
    D
}
