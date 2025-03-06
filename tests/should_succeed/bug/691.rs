extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Foo {
    bar: u32,
}

pub fn example() {
    let c = Foo { bar: 2u32 };
    let _ = #[requires (c.bar == 2u32)]
    || ();
}
