extern crate creusot_contracts;
use creusot_contracts::{logic::Mapping, *};

// Test postfix model operator

#[open]
#[predicate]
#[requires(v@.len() == 3)]
pub fn has_len_3(v: &[u32]) -> bool {
    pearlite! { v@.len() == 3 }
}

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

#[open]
#[predicate]
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
    let _x = ghost! { pearlite! { |a : u32| a  } };
}

pub fn pearlite_closure(_x: Ghost<Mapping<u32, bool>>) {}

pub fn caller() {
    pearlite_closure(ghost! { pearlite! { |_a| true }});
}

// Implicit logical reborrows

pub struct S {}

impl S {
    #[open]
    #[logic]
    pub fn x(&mut self) -> bool {
        true
    }
}

#[open]
#[logic]
pub fn proj(x: &mut (S, S)) -> bool {
    x.0.x()
}

#[open]
#[logic]
pub fn proj2(x: &mut &mut (S, S)) -> bool {
    x.0.x()
}

// Unnesting through an index projection

#[open(self)]
#[creusot::decl::logic]
pub fn reborrow_index_projection<'a, 'b, T>(a: &'a mut &'b mut [T]) -> &'a mut T {
    &mut a[0]
}

// Left out until I understand the semantics of `Deref` patterns.
// #[logic]
// pub fn proj_opt(x : &mut Option<S>)  -> bool {
//     match x {
//         Some(a) => a.x(),
//         None => true,
//     }
// }
