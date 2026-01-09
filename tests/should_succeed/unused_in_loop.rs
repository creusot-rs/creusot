extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 10u32)]
pub fn unused_in_loop(b: bool) -> u32 {
    let x = 10;
    #[invariant(true)]
    loop {
        if b {
            break;
        }
    }
    x
}
