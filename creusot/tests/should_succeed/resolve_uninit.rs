extern crate creusot_contracts;
use creusot_contracts::*;

#[allow(unused_assignments)]
pub fn maybe_uninit<T: Default>(b: bool, y: T) -> T {
    let mut x: T;
    if b {
        x = T::default();
    }
    // do not resolve x here as it is maybe uninit
    x = y;
    x
}
