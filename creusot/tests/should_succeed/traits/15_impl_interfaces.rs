extern crate creusot_contracts;
use creusot_contracts::*;

// Verifies that instances are properly cloned as interfaces in
// the interfaces of functions. Also ensures that we don't attempt
// refine associated types of instances.

pub trait Tr {
    type A;
}

impl Tr for () {
    type A = ();
}

#[trusted]
#[ghost]
fn x<T: Tr>(_x: T) -> T::A {
    absurd
}

#[requires(x(a) == ())]
pub fn calls(a: ()) -> <() as Tr>::A {}

// // This call used to break
// #[ensures(x(a) == ())]
// fn breaks(a: ()) {
//     calls(a)
// }
