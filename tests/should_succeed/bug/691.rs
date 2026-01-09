extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Foo {
    bar: u32,
}

pub fn example() {
    let c = Foo { bar: 2u32 };
    let _ = #[requires (c.bar == 2u32)]
    || ();
}
