extern crate creusot_contracts;
use creusot_contracts::ghost_ptr::GhostPtrToken;

pub fn main() {
    let mut tok = GhostPtrToken::new();
    let b = Box::new(1);
    let p = tok.ptr_from_box(b);
    let mut r = tok.ptr_to_box(p);
    *r += 5;
}
