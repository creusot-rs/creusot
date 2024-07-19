extern crate creusot_contracts;
use creusot_contracts::*;

pub fn deref_ghost_in_program() {
    let g = gh!(2);
    let _: i32 = *g;
}
