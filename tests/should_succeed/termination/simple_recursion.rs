extern crate creusot_contracts;
use creusot_contracts::*;

mod custom_variant;
pub use custom_variant::CustomVariant;

#[check(terminates)]
#[variant(x)]
#[ensures(result == x)]
pub fn variant_int(x: u32) -> u32 {
    if x == 0 { 0 } else { 1 + variant_int(x - 1) }
}

#[check(terminates)]
#[variant(x)]
#[ensures(result == 0u32)]
pub fn custom_variant(x: CustomVariant) -> u32 {
    if x.0 == 0 || x.1 == 0 { 0 } else { custom_variant(CustomVariant(x.0 - 1, x.1 - 1)) }
}
