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

    // Error: exposes constructor
    pub const C: S = S(0);
}
