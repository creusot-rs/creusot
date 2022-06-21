extern crate creusot_contracts;
use creusot_contracts::*;

// Tests that we can use field access syntax in pearlite.

pub struct A {
    a: bool,
}

#[trusted]
#[ensures(x.a == x.a)]
pub fn solver(x: A) {}

#[ensures(x == A { a : false })]
pub fn struct_in_pearlite(x: A) {}

pub struct B {
    pub field1: bool,
    pub field2: u32,
}

#[ensures(x == B { field2: 0u32, field1: false })]
pub fn struct_order(x: B) {}

#[predicate]
#[allow(unreachable_patterns)]
fn field1_is_true(x: B) -> bool {
    pearlite! {
        match x {
            B { field1: true, .. } => true,
            B { field2, field1: _f } => @field2 == 0,
            _ => false
        }
    }
}
