// NO_REPLAY

extern crate creusot_std;
use creusot_std::{logic::Mapping, prelude::*};

// Test postfix model operator

#[logic(open)]
#[requires(v@.len() == 3)]
pub fn has_len_3(v: &[u32]) -> bool {
    pearlite! { v@.len() == 3 }
}

// Tests that we can use field access syntax in pearlite.

pub struct A {
    pub a: bool,
}

#[trusted]
#[ensures(x.a == x.a)]
pub fn solver(x: A) {}

#[ensures(x == A { a: false })]
pub fn struct_in_pearlite(x: A) {}

pub struct B {
    pub field1: bool,
    pub field2: u32,
}

#[ensures(x == B { field2: 0u32, field1: false })]
pub fn struct_order(x: B) {}

#[logic(open)]
#[allow(unreachable_patterns)]
pub fn field1_is_true(x: B) -> bool {
    pearlite! {
        use crate::B; // verify that imports work properly
        match x {
            B { field1: true, .. } => true,
            B { field2, field1: _f } => field2@ == 0,
            _ => false
        }
    }
}

pub fn ghost_closure() {
    let _x = snapshot! { |a: u32| a };
}

pub fn pearlite_closure(_x: Snapshot<Mapping<u32, bool>>) {}

pub fn caller() {
    pearlite_closure(snapshot! { |_a| true });
}

// Implicit logical reborrows

pub struct S {}

impl S {
    #[logic(open)]
    pub fn x(&mut self) -> bool {
        true
    }
}

#[logic(open)]
pub fn proj(x: &mut (S, S)) -> bool {
    x.0.x()
}

#[logic(open)]
pub fn proj2(x: &mut &mut (S, S)) -> bool {
    x.0.x()
}

// Unnesting through an index projection

#[logic(open(self))]
pub fn reborrow_index_projection<'a, 'b, T>(a: &'a mut &'b mut [T]) -> &'a mut T {
    &mut a[0]
}

#[logic(open(self))]
pub fn reborrow_index_projection2<'a, 'b, T>(a: &'a &'b [T]) -> &'a T {
    &a[0]
}

#[logic(open(self))]
pub fn test3<'a, T>(a: Snapshot<&'a mut [T]>) -> &'a mut T {
    &mut a[0]
}

#[logic(open(self))]
pub fn test4<'a, T>(a: &'a mut Snapshot<[T]>) -> &'a mut T {
    &mut a[0]
}

#[logic(open(self))]
pub fn test5<'a, T>(a: &'a mut &mut &mut [T]) -> &'a mut T {
    &mut a[0]
}

#[logic(open(self))]
pub fn test6<'a>(a: &'a mut &&mut u32) -> &'a mut u32 {
    &mut ***a
}

// Left out until I understand the semantics of `Deref` patterns.
// #[logic]
// pub fn proj_opt(x: &mut Option<S>)  -> bool {
//     match x {
//         Some(a) => a.x(),
//         None => true,
//     }
// }
