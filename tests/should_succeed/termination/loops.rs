extern crate creusot_contracts;
use creusot_contracts::prelude::*;

mod custom_variant;
pub use custom_variant::CustomVariant;

#[check(terminates)]
#[ensures(result == x)]
pub fn variant_int(mut x: u32) -> u32 {
    let mut result = 0;
    let total = snapshot!(x@);
    #[variant(x)]
    #[invariant(*total == x@ + result@)]
    while x > 0 {
        x -= 1;
        result += 1
    }
    result
}

#[check(terminates)]
#[ensures(result@ == Int::min(x.0@, x.1@))]
pub fn custom_variant(mut x: CustomVariant) -> u32 {
    let mut result = 0;
    let res = snapshot!(Int::min(x.0@, x.1@));
    #[variant(x)]
    #[invariant(Int::min(x.0@, x.1@) + result@ == *res)]
    while x.0 > 0 && x.1 > 0 {
        x.0 -= 1;
        x.1 -= 1;
        result += 1;
    }
    result
}
