use crate as creusot_contracts;
use creusot_contracts_proc::*;

#[trusted]
#[ensures(^dest === src)]
#[ensures(result === *dest)]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    std::mem::replace(dest, src)
}
