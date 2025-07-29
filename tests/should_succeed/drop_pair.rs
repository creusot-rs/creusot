extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(resolve(_x))]
#[ensures(^_x.0 == *_x.0)]
#[ensures(^_x.1 == *_x.1)]
pub fn drop_pair(_x: (&mut u32, &mut u32)) {}

pub fn drop_pair2(x: (&mut u32, &mut u32)) {
    let _ = x;
}

// Checks that we generate drop for x which is always init but never live *and* written to.
// However we should *not* get a drop for *y*
pub fn drop<'a>(mut _x: &'a mut u32, y: &'a mut u32) {
    _x = y;
}
