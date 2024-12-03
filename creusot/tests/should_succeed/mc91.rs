extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(x <= 100u32 ==> result@ == 91 &&
    x > 100u32 ==> result@ == x@ - 10)]
pub fn mc91(x: u32) -> u32 {
    if x > 100 {
        x - 10
    } else {
        mc91(mc91(x + 11))
    }
}
