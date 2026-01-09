extern crate creusot_std;
use creusot_std::prelude::*;

pub fn mutate_ghost_in_program() {
    let mut g = ghost!(2);
    *g = 3;
}
