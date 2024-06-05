extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == a ^ b)]
pub fn test_bit_xor_i64(a: i64, b: i64) -> i64 {
    a ^ b
}

#[ensures(result == a & b)]
pub fn test_bit_and_u16(a: u16, b: u16) -> u16 {
    a & b
}

#[ensures(result == a | b)]
pub fn test_bit_or_i32(a: i32, b: i32) -> i32 {
    a | b
}


#[ensures(result@ == a@ + b@)]
#[ensures(result == a + b)]
pub fn test_add_usize(a: usize, b: usize) -> usize {
    a + b
}


#[ensures(result@ == a@ * b@)]
#[ensures(result == a * b)]
pub fn test_mul_i8(a: i8, b: i8) -> i8 {
    a * b
}

#[ensures(result == (a <= 100))]
pub fn test_literal_i32(a: i32) -> bool {
    a <= 100
}