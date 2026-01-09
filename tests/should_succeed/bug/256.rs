extern crate creusot_std;

pub fn u8_safe(u: u8) {
    let _ = u + 0;
}
// `String` includes `u8` internally.
//
pub fn bug_256(_x: String) {}
