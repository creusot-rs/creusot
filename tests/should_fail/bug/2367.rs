// WHY3PROVE
use creusot_std::prelude::*;

#[bitwise_proof]
#[ensures(false)]
pub fn leading_ones_false() {
    let _ = 0u8.leading_ones();
}

#[bitwise_proof]
#[ensures(false)]
pub fn trailing_ones_false() {
    let _ = u8::MAX.trailing_ones();
}
