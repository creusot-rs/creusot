extern crate creusot_std;
use creusot_std::prelude::*;

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
