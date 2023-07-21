extern crate creusot_contracts;
use creusot_contracts::{logic::Mapping, *};

#[logic]
fn f(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[ghost]
fn g(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[logic]
fn h(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}

#[ghost]
fn i(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}
