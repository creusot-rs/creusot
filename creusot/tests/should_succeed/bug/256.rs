extern crate creusot_contracts;

use creusot_contracts::*;

fn u8_safe(u: u8) {
    u + 0;
}
// `String` includes `u8` internally.
//
fn bug_256(x: String) {}
