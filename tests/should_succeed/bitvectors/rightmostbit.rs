extern crate creusot_contracts;
use creusot_contracts::*;

/* Possible specifications:
 *    count(result) = 1   (from bitcount.rs ?)
 * See also
 *   https://toccata.gitlabpages.inria.fr/toccata/gallery/rightmostbittrick.en.html
 */

#[logic]
fn count8_log(n: i8) -> Int {
    (if n & 1i8 == 0i8 { 0 } else { 1 })
        + (if n & 2i8 == 0i8 { 0 } else { 1 })
        + (if n & 4i8 == 0i8 { 0 } else { 1 })
        + (if n & 8i8 == 0i8 { 0 } else { 1 })
        + (if n & 0x10i8 == 0i8 { 0 } else { 1 })
        + (if n & 0x20i8 == 0i8 { 0 } else { 1 })
        + (if n & 0x40i8 == 0i8 { 0 } else { 1 })
        + (if n & i8::MIN == 0i8 { 0 } else { 1 })
}

#[ensures(x >= 0i8 ==> 0i8 <= result && result <= x)]
#[ensures(x <= 0i8 && x > i8::MIN ==> 0i8 <= result && result@ <= -x@)]
#[ensures((x == i8::MIN) == (result == i8::MIN))]
#[ensures(forall<i> 0i8 <= i && i < result ==> i & x == 0i8)]
#[ensures(x != 0i8 ==> count8_log(result) == 1)]
#[bitwise_proof]
pub fn rightmost_bit_8(x: i8) -> i8 {
    x & x.wrapping_neg()
}

#[ensures(x >= 0i64 ==> 0i64 <= result && result <= x)]
#[ensures(x <= 0i64 && x > i64::MIN ==> 0i64 <= result && result@ <= -x@)]
#[ensures((x == i64::MIN) == (result == i64::MIN))]
#[ensures(forall<i> 0i64 <= i && i < result ==> i & x == 0i64)]
#[bitwise_proof]
pub fn rightmost_bit_64(x: i64) -> i64 {
    x & x.wrapping_neg()
}

#[trusted]
pub fn main() {
    println!("rightmost_bit_64(0) = {}", rightmost_bit_64(0));
    println!("rightmost_bit_64(1) = {}", rightmost_bit_64(1));
    println!("rightmost_bit_64(2) = {}", rightmost_bit_64(2));
    println!("rightmost_bit_64(3) = {}", rightmost_bit_64(3));
    println!("rightmost_bit_64(42) = {}", rightmost_bit_64(42));
    println!("rightmost_bit_64(254) = {}", rightmost_bit_64(254));
    println!("rightmost_bit_64(255) = {}", rightmost_bit_64(255));
    println!("rightmost_bit_64(2048) = {}", rightmost_bit_64(2048));
    println!("rightmost_bit_64(0x12345678) = {}", rightmost_bit_64(0x12345678));
    println!("rightmost_bit_64(0x89ABCDEF) = {}", rightmost_bit_64(0x89ABCDEF));
    println!("rightmost_bit_64(0xFFFFFFFF) = {}", rightmost_bit_64(0xFFFFFFFF));
    println!("rightmost_bit_64(0x8000_0000) = {}", rightmost_bit_64(0x8000_0000));
}
