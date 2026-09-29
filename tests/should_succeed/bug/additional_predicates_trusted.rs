extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
pub mod m {
    pub struct S;

    impl Iterator for S {
        type Item = ();

        fn next(&mut self) -> Option<()> {
            None
        }
    }
}
