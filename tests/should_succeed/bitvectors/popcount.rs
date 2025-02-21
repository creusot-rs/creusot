extern crate creusot_contracts;
use creusot_contracts::*;

/* Possible specifications:
 *  result = numof i, 0 <= i < 63, nth_bit(n,i) = 1
 * See also
 *   https://toccata.gitlabpages.inria.fr/toccata/gallery/bitcount.en.html
 *
 * Needed for specifying such code in general:
 *    - nth_bit(b:bv,n:int):bool : true when n-th bit of b is set
 *    - eq_sub(b1:bv,b2:bv,i:int,j:int):bv : b1 and b1 coincide on range i..j of their bits
 */

#[logic]
fn count8_log(n: u8) -> Int {
    (if n & 1u8 == 0u8 { 0 } else { 1 })
        + (if n & 2u8 == 0u8 { 0 } else { 1 })
        + (if n & 4u8 == 0u8 { 0 } else { 1 })
        + (if n & 8u8 == 0u8 { 0 } else { 1 })
        + (if n & 0x10u8 == 0u8 { 0 } else { 1 })
        + (if n & 0x20u8 == 0u8 { 0 } else { 1 })
        + (if n & 0x40u8 == 0u8 { 0 } else { 1 })
        + (if n & 0x80u8 == 0u8 { 0 } else { 1 })
}

#[ensures(result@ <= 8)]
#[ensures(result@ == count8_log(n))]
#[bitwise_proof]
pub fn count8(n: u8) -> u8 {
    let mut x = n;
    x = x - ((x >> 1) & 0x55);
    x = (x & 0x33) + ((x >> 2) & 0x33);
    x = (x + (x >> 4)) & 0x0F;
    x
}

#[ensures(result@ <= 16)]
#[bitwise_proof]
pub fn count16(n: u16) -> u16 {
    let mut x = n;
    x = x - ((x >> 1) & 0x5555);
    x = (x & 0x3333) + ((x >> 2) & 0x3333);
    x = (x + (x >> 4)) & 0x0F0F;
    x = x + (x >> 8);
    x & 0x1F
}

#[ensures(result@ <= 32)]
#[bitwise_proof]
pub fn count32(n: u32) -> u32 {
    let mut x = n;
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x + (x >> 4)) & 0x0F0F0F0F;
    x = x + (x >> 8);
    x = x + (x >> 16);
    x & 0x0000003F
}

#[ensures(result@ <= 64)]
#[bitwise_proof]
pub fn count64(n: u64) -> u64 {
    let mut x = n;
    x = x - ((x >> 1) & 0x5555555555555555);
    x = (x & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0F;
    x = x + (x >> 8);
    x = x + (x >> 16);
    x = x + (x >> 32);
    x & 0x7F
}

#[trusted]
pub fn main() {
    println!("count8(0) = {}", count8(0));
    println!("count8(1) = {}", count8(1));
    println!("count8(2) = {}", count8(2));
    println!("count8(3) = {}", count8(3));
    println!("count8(42) = {}", count8(42));
    println!("count8(254) = {}", count8(254));
    println!("count8(255) = {}", count8(255));

    println!("count32(0) = {}", count32(0));
    println!("count32(1) = {}", count32(1));
    println!("count32(2) = {}", count32(2));
    println!("count32(3) = {}", count32(3));
    println!("count32(42) = {}", count32(42));
    println!("count32(254) = {}", count32(254));
    println!("count32(255) = {}", count32(255));

    println!("count32(2048) = {}", count32(2048));
    println!("count32(0x12345678) = {}", count32(0x12345678));
    println!("count32(0x89ABCDEF) = {}", count32(0x89ABCDEF));
    println!("count32(0xFFFFFFFF) = {}", count32(0xFFFFFFFF));
}
