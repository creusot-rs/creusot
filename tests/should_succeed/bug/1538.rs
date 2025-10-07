extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Foo {
    bar: (),
}

#[logic]
#[ensures(result == true)]
pub fn baz(foo: Foo) -> bool {
    pearlite! {
        forall<_x: ()> foo.bar == ()
    }
}
