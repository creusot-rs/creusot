extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S();

impl Iterator for S {
    type Item = ();
    #[requires(true)]
    fn next(&mut self) -> Option<()> {
        None
    }
}
