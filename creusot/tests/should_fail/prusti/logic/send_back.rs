extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
fn move_state<'x, T: Copy>(t: T) -> T {
    t
}
