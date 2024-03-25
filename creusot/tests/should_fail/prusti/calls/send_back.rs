extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
fn move_state<'x, T: Copy>(t: T) -> T {
    move_state2(at::<'x>(t))
}

#[logic('x where 'now: 'x)]
fn move_state2<'x, T: Copy>(t: T) -> T {
    t
}
