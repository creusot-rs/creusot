extern crate creusot_std;
use creusot_std::prelude::*;

/// Tests addition of `u8`s with some examples
pub fn test_u8_add_example() {
    assert!(5u8.checked_add(10).unwrap() == 15);
    assert!(250u8.checked_add(10).is_none());

    assert!(5u8.wrapping_add(10) == 15);
    assert!(250u8.wrapping_add(10) == 4);

    assert!(5u8.saturating_add(10) == 15);
    assert!(250u8.saturating_add(10) == 255);

    let res = 5u8.overflowing_add(10);
    assert!(res.0 == 15 && res.1 == false);
    let res = 250u8.overflowing_add(10);
    assert!(res.0 == 4 && res.1 == true);
}

/// Tests addition of `u8`s in a general overflowing case
#[requires(a@ != 0)]
pub fn test_u8_add_overflow(a: u8) {
    assert!(255u8.checked_add(a).is_none());
    assert!(255u8.wrapping_add(a) == a - 1);
    assert!(255u8.saturating_add(a) == 255);
    let res = 255u8.overflowing_add(a);
    assert!(res.0 == a - 1 && res.1 == true);
}

/// Tests that the verifier is able to deduce a stricter postcondition for wrapping addition of
/// `u8`s
#[ensures(result@ == a@ + b@ || result@ == a@ + b@ - 256)]
pub fn test_u8_wrapping_add(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

/// Tests that overflowing addition of `u8`s matches wrapping and checked addition
pub fn test_u8_overflowing_add(a: u8, b: u8) {
    assert!(a.overflowing_add(b).0 == a.wrapping_add(b));
    assert!(a.overflowing_add(b).1 == a.checked_add(b).is_none());
}

/// Tests subtraction of `u8`s with some examples
pub fn test_u8_sub_example() {
    assert!(5u8.checked_sub(10).is_none());
    assert!(250u8.checked_sub(10).unwrap() == 240);

    assert!(5u8.wrapping_sub(10) == 251);
    assert!(250u8.wrapping_sub(10) == 240);

    assert!(5u8.saturating_sub(10) == 0);
    assert!(250u8.saturating_sub(10) == 240);

    let res = 5u8.overflowing_sub(10);
    assert!(res.0 == 251 && res.1 == true);
    let res = 250u8.overflowing_sub(10);
    assert!(res.0 == 240 && res.1 == false);
}

/// Tests subtraction of `u8`s in a general overflowing case
#[requires(a@ != 0)]
pub fn test_u8_sub_overflow(a: u8) {
    assert!(0u8.checked_sub(a).is_none());
    assert!(0u8.wrapping_sub(a) == 255 - a + 1);
    assert!(0u8.saturating_sub(a) == 0);
    let res = 0u8.overflowing_sub(a);
    assert!(res.0 == 255 - a + 1 && res.1 == true);
}

/// Tests that the verifier is able to deduce a stricter postcondition for wrapping subtraction of
/// `u8`s
#[ensures(result@ == a@ - b@ || result@ == a@ - b@ + 256)]
pub fn test_u8_wrapping_sub(a: u8, b: u8) -> u8 {
    a.wrapping_sub(b)
}

/// Tests that overflowing subtraction of `u8`s matches wrapping and checked subtraction
pub fn test_u8_overflowing_sub(a: u8, b: u8) {
    assert!(a.overflowing_sub(b).0 == a.wrapping_sub(b));
    assert!(a.overflowing_sub(b).1 == a.checked_sub(b).is_none());
}

/// Tests multiplication of `u8`s with some examples
pub fn test_u8_mul_example() {
    assert!(5u8.checked_mul(10).unwrap() == 50);
    assert!(50u8.checked_mul(10).is_none());

    assert!(5u8.wrapping_mul(10) == 50);
    assert!(50u8.wrapping_mul(10) == 244);

    assert!(5u8.saturating_mul(10) == 50);
    assert!(50u8.saturating_mul(10) == 255);

    let res = 5u8.overflowing_mul(10);
    assert!(res.0 == 50 && res.1 == false);
    let res = 50u8.overflowing_mul(10);
    assert!(res.0 == 244 && res.1 == true);
}

/// Tests that multiplication of `u8`s with zero always succeeds and results in zero
pub fn test_u8_mul_zero(a: u8) {
    assert!(0u8.checked_mul(a).unwrap() == 0);
    assert!(0u8.wrapping_mul(a) == 0);
    assert!(0u8.saturating_mul(a) == 0);
    let res = 0u8.overflowing_mul(a);
    assert!(res.0 == 0 && res.1 == false);
}

/// Tests that overflowing multiplication of `u8`s matches wrapping and checked multiplication
pub fn test_u8_overflowing_mul(a: u8, b: u8) {
    assert!(a.overflowing_mul(b).0 == a.wrapping_mul(b));
    assert!(a.overflowing_mul(b).1 == a.checked_mul(b).is_none());
}

/// Tests division of `u8`s with some examples
pub fn test_u8_div_example() {
    assert!(5u8.checked_div(0).is_none());
    assert!(5u8.checked_div(2).unwrap() == 2);
    assert!(5u8.wrapping_div(2) == 2);
    assert!(5u8.saturating_div(2) == 2);
    let res = 5u8.overflowing_div(2);
    assert!(res.0 == 2 && res.1 == false);
}

/// Tests that division of `u8`s never overflows
#[requires(b@ != 0)]
pub fn test_u8_div_no_overflow(a: u8, b: u8) {
    assert!(a.checked_div(b).unwrap() == a / b);
    assert!(a.wrapping_div(b) == a / b);
    assert!(a.saturating_div(b) == a / b);
    let res = a.overflowing_div(b);
    assert!(res.0 == a / b && res.1 == false);
}

/// Tests that division of `u8`s by zero always fails
pub fn test_u8_div_zero(a: u8) {
    assert!(a.checked_div(0).is_none());
}

/// Tests addition of `i8`s with some examples
pub fn test_i8_add_example() {
    assert!(5i8.checked_add(10).unwrap() == 15);
    assert!(120i8.checked_add(10).is_none());
    assert!((-120i8).checked_add(-10).is_none());

    assert!(5i8.wrapping_add(10) == 15);
    assert!(120i8.wrapping_add(10) == -126);
    assert!((-120i8).wrapping_add(-10) == 126);

    assert!(5i8.saturating_add(10) == 15);
    assert!(120i8.saturating_add(10) == 127);
    assert!((-120i8).saturating_add(-10) == -128);

    let res = 5i8.overflowing_add(10);
    assert!(res.0 == 15 && res.1 == false);
    let res = 120i8.overflowing_add(10);
    assert!(res.0 == -126 && res.1 == true);
    let res = (-120i8).overflowing_add(-10);
    assert!(res.0 == 126 && res.1 == true);
}

/// Tests addition of `i8`s in a general overflowing case, for positive `a`
#[requires(a@ > 0)]
pub fn test_i8_add_overflow_pos(a: i8) {
    assert!(127i8.checked_add(a).is_none());
    assert!(127i8.wrapping_add(a) == a - 127 - 2);
    assert!(127i8.saturating_add(a) == 127);
    let res = 127i8.overflowing_add(a);
    assert!(res.0 == a - 127 - 2 && res.1 == true);
}

/// Tests addition of `i8`s in a general overflowing case, for negative `a`
#[requires(a@ < 0)]
pub fn test_i8_add_overflow_neg(a: i8) {
    assert!((-128i8).checked_add(a).is_none());
    assert!((-128i8).wrapping_add(a) == a + 127 + 1);
    assert!((-128i8).saturating_add(a) == -128);
    let res = (-128i8).overflowing_add(a);
    assert!(res.0 == a + 127 + 1 && res.1 == true);
}

/// Tests that the verifier is able to deduce a stricter postcondition for wrapping addition of
/// `i8`s
#[ensures(result@ == a@ + b@ || result@ == a@ + b@ - 256 || result@ == a@ + b@ + 256)]
pub fn test_i8_wrapping_add(a: i8, b: i8) -> i8 {
    a.wrapping_add(b)
}

/// Tests that overflowing addition of `i8`s matches wrapping and checked addition
pub fn test_i8_overflowing_add(a: i8, b: i8) {
    assert!(a.overflowing_add(b).0 == a.wrapping_add(b));
    assert!(a.overflowing_add(b).1 == a.checked_add(b).is_none());
}

/// Tests subtraction of `i8`s with some examples
pub fn test_i8_sub_example() {
    assert!(5i8.checked_sub(10).unwrap() == -5);
    assert!(120i8.checked_sub(10).unwrap() == 110);
    assert!((-120i8).checked_sub(10).is_none());

    assert!(5i8.wrapping_sub(10) == -5);
    assert!(120i8.wrapping_sub(10) == 110);
    assert!((-120i8).wrapping_sub(10) == 126);

    assert!(5i8.saturating_sub(10) == -5);
    assert!(120i8.saturating_sub(10) == 110);
    assert!((-120i8).saturating_sub(10) == -128);

    let res = 5i8.overflowing_sub(10);
    assert!(res.0 == -5 && res.1 == false);
    let res = 120i8.overflowing_sub(10);
    assert!(res.0 == 110 && res.1 == false);
    let res = (-120i8).overflowing_sub(10);
    assert!(res.0 == 126 && res.1 == true);
}

/// Tests subtraction of `i8`s in a general overflowing case, for positive `a`
#[requires(a@ > 0)]
pub fn test_i8_sub_overflow_pos(a: i8) {
    assert!((-128i8).checked_sub(a).is_none());
    assert!((-128i8).wrapping_sub(a) == 127 - a + 1);
    assert!((-128i8).saturating_sub(a) == -128);
    let res = (-128i8).overflowing_sub(a);
    assert!(res.0 == 127 - a + 1 && res.1 == true);
}

/// Tests subtraction of `i8`s in a general overflowing case, for negative `a`
#[requires(a@ < 0)]
pub fn test_i8_sub_overflow_neg(a: i8) {
    assert!(127i8.checked_sub(a).is_none());
    assert!(127i8.wrapping_sub(a) == -(2 + a) - 127);
    assert!(127i8.saturating_sub(a) == 127);
    let res = 127i8.overflowing_sub(a);
    assert!(res.0 == -(2 + a) - 127 && res.1 == true);
}

/// Tests that the verifier is able to deduce a stricter postcondition for wrapping subtraction of
/// `i8`s
#[ensures(result@ == a@ - b@ || result@ == a@ - b@ + 256 || result@ == a@ - b@ - 256)]
pub fn test_i8_wrapping_sub(a: i8, b: i8) -> i8 {
    a.wrapping_sub(b)
}

/// Tests that overflowing subtraction of `i8`s matches wrapping and checked subtraction
pub fn test_i8_overflowing_sub(a: i8, b: i8) {
    assert!(a.overflowing_sub(b).0 == a.wrapping_sub(b));
    assert!(a.overflowing_sub(b).1 == a.checked_sub(b).is_none());
}

/// Tests multiplication of `i8`s with some examples
pub fn test_i8_mul_example() {
    assert!(5i8.checked_mul(10).unwrap() == 50);
    assert!(50i8.checked_mul(10).is_none());
    assert!(50i8.checked_mul(-10).is_none());

    assert!(5i8.wrapping_mul(10) == 50);
    assert!(50i8.wrapping_mul(10) == -12);
    assert!(50i8.wrapping_mul(-10) == 12);

    assert!(5i8.saturating_mul(10) == 50);
    assert!(50i8.saturating_mul(10) == 127);
    assert!(50i8.saturating_mul(-10) == -128);

    let res = 5i8.overflowing_mul(10);
    assert!(res.0 == 50 && res.1 == false);
    let res = 50i8.overflowing_mul(10);
    assert!(res.0 == -12 && res.1 == true);
    let res = 50i8.overflowing_mul(-10);
    assert!(res.0 == 12 && res.1 == true);
}

/// Tests that multiplication of `i8`s with zero always succeeds and results in zero
pub fn test_i8_mul_zero(a: i8) {
    assert!(0i8.checked_mul(a).unwrap() == 0);
    assert!(0i8.wrapping_mul(a) == 0);
    assert!(0i8.saturating_mul(a) == 0);
    let res = 0i8.overflowing_mul(a);
    assert!(res.0 == 0 && res.1 == false);
}

/// Tests that overflowing multiplication of `i8`s matches wrapping and checked multiplication
pub fn test_i8_overflowing_mul(a: i8, b: i8) {
    assert!(a.overflowing_mul(b).0 == a.wrapping_mul(b));
    assert!(a.overflowing_mul(b).1 == a.checked_mul(b).is_none());
}

/// Tests division of `i8`s with some examples
pub fn test_i8_div_example() {
    assert!(5i8.checked_div(0).is_none());
    assert!(5i8.checked_div(2).unwrap() == 2);
    assert!(5i8.checked_div(-2).unwrap() == -2);
    assert!((-128i8).checked_div(-1).is_none());

    assert!(5i8.wrapping_div(2) == 2);
    assert!(5i8.wrapping_div(-2) == -2);
    assert!((-128i8).wrapping_div(-1) == -128);

    assert!(5i8.saturating_div(2) == 2);
    assert!(5i8.saturating_div(-2) == -2);
    assert!((-128i8).saturating_div(-1) == -128);

    let res = 5i8.overflowing_div(2);
    assert!(res.0 == 2 && res.1 == false);
    let res = 5i8.overflowing_div(-2);
    assert!(res.0 == -2 && res.1 == false);
    let res = (-128i8).overflowing_div(-1);
    assert!(res.0 == -128 && res.1 == true);
}

/// Tests that division of `i8`s never overflows, except for the one special case
#[requires(b@ != 0 && (a@ != -128 || b@ != -1))]
pub fn test_i8_div_no_overflow(a: i8, b: i8) {
    assert!(a.checked_div(b).unwrap() == a / b);
    assert!(a.wrapping_div(b) == a / b);
    assert!(a.saturating_div(b) == a / b);
    let res = a.overflowing_div(b);
    assert!(res.0 == a / b && res.1 == false);
}

/// Tests that division of `i8`s by zero always fails
pub fn test_i8_div_zero(a: i8) {
    assert!(a.checked_div(0).is_none());
}
