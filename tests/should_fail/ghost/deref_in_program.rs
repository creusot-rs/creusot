extern crate creusot_std;
use creusot_std::prelude::*;

pub fn deref_ghost_in_program() {
    let g = ghost!(2);
    let _: &i32 = &*g;
}

pub fn deref_mut_ghost_in_program() {
    let mut g = ghost!(2);
    let _: &mut i32 = &mut *g;
}

pub fn into_inner_ghost_in_program() {
    let g = ghost!(2);
    let _: i32 = g.into_inner();
}
