extern crate creusot_contracts;
use creusot_contracts::*;

trait T {
    #[logic]
    fn f();
}

impl T for () {
    #[logic(prophetic)]
    fn f() {
        ()
    }
}
