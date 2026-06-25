extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

impl Clone for S {
    #[check(terminates)]
    fn clone(&self) -> Self {
        (S,).clone().0
    }
}
