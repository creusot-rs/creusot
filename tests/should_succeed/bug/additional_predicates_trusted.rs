extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
pub mod m {
    use creusot_std::prelude::ensures;
    pub struct S;

    impl Iterator for S {
        type Item = ();

        #[ensures(true)] // FIXME handle additional predicates in inherited specs
        fn next(&mut self) -> Option<()> {
            None
        }
    }
}
