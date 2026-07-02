// WHY3PROVE
use creusot_std::prelude::*;

#[allow(arithmetic_overflow)]
#[ensures(true)]
pub fn shr_full() -> u8 {
    1u8 >> 8
}
