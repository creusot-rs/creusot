extern crate creusot_contracts;
use creusot_contracts::*;

pub fn mutate_ghost_in_program() {
    let mut g = gh!(2);
    *g = 3;
}
