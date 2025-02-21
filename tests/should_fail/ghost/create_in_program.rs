extern crate creusot_contracts;
use creusot_contracts::*;

pub fn create_ghost_in_program() {
    let _g = GhostBox::new(1);
}
