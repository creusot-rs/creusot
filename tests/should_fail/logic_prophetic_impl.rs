extern crate creusot_contracts;
use creusot_contracts::*;

pub trait T {
    #[logic]
    fn f();
}

impl T for () {
    #[logic(prophetic)]
    #[open(self)]
    fn f() {
        ()
    }
}
