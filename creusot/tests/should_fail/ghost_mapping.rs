extern crate creusot_contracts;
use creusot_contracts::{logic::Mapping, *};

#[logic(prophetic)]
fn f(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[logic]
fn g(x: &mut i32) -> Mapping<(), i32> {
    pearlite! { |_| ^x }
}

#[logic(prophetic)]
fn h(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}

#[logic]
fn i(y: &mut i32) -> bool {
    pearlite! { forall<_x:Int> ^y == 1i32 }
}
