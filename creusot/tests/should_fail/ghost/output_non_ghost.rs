extern crate creusot_contracts;
use creusot_contracts::*;

pub fn output_non_ghost() {
    let _ = ghost!(1);
}
