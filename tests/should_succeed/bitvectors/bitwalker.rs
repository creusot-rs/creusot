extern crate creusot_contracts;
use creusot_contracts::*;

/******
 * peek: extract some value from a stream of bytes
 ******/

#[requires(left < 8usize)]
fn peek_bit_u8(x: u8, left: usize) -> bool {
    let mask: u8 = 1u8 << (7usize - left);
    (x & mask) != 0
}

#[requires(left@ < 8 * addr@.len())]
fn peek_bit_array8(addr: &[u8], left: usize) -> bool {
    match addr.get(left / 8) {
        Some(v) => peek_bit_u8(*v, left % 8),
        None => {
            assert!(false);
            false
        }
    }
}

/* sets the bit at index [left] in [value] to the value of [flag]
 */
#[requires(left < 64usize)]
fn poke_bit_64(value: u64, left: usize, flag: bool) -> u64 {
    let mask: u64 = 1u64 << (63usize - left);
    if flag {
        return value | mask;
    } else {
        return value & !mask;
    }
}

/* returns the 64-bit value stored in array [addr]
 * read from the bits at position [start] to [start+length-1],
 * [length] being a number of bits
 */
#[requires(addr@.len() < 10000000)]
#[requires(length <= 64usize)]
#[requires(start@ + length@ <= 8 * addr@.len())]
fn peek(start: usize, length: usize, addr: &[u8]) -> u64 {
    if (start + length) > 8 * addr.len() {
        panic!()
    }
    let mut retval: u64 = 0;
    let mut i: usize = 0;
    while i < length {
        let flag = peek_bit_array8(addr, start + i);
        retval = poke_bit_64(retval, 64usize - (length - i), flag);
        i += 1;
    }
    return retval;
}

/*****
 * poke: write some value into a stream of bytes
 *****/

#[requires(left < 64usize)]
fn peek_64bit(value: u64, left: usize) -> bool {
    let mask: u64 = 1u64 << (63usize - left);
    (value & mask) != 0
}

#[requires(left < 8usize)]
fn poke_8bit(byte: u8, left: usize, flag: bool) -> u8 {
    let mask = 1u8 << (7usize - left);
    if flag {
        return byte | mask;
    } else {
        return byte & !mask;
    }
}

#[requires(left@ < 8 * addr@.len())]
#[ensures((^addr)@.len() == addr@.len())]
fn poke_8bit_array(addr: &mut [u8], left: usize, flag: bool) {
    let i: usize = left / 8;
    let k: usize = left % 8;
    addr[i] = poke_8bit(addr[i], k, flag);
}

#[requires(addr@.len() < 10000000)]
#[requires(length <= 64usize)]
#[requires(start@ + length@ <= 8 * addr@.len())]
#[ensures((^addr)@.len() == addr@.len())]
fn poke(start: usize, length: usize, addr: &mut [u8], value: u64) -> i8 {
    let ghost_len = addr.len();
    if (start + length) > 8 * addr.len() {
        return -1;
    }
    if length < 64usize && value >= (1u64 << length) {
        return -2;
    }
    let lstart: usize = 64 - length;
    let mut i: usize = 0;
    #[invariant(i <= length)]
    #[invariant(addr@.len() == ghost_len@)]
    while i < length {
        proof_assert!(i@ < length@);
        let flag = peek_64bit(value, lstart + i);
        poke_8bit_array(addr, start + i, flag);
        proof_assert!(addr@.len() == ghost_len@);
        i += 1;
    }
    return 0;
}

/****
 * peek then poke
 *****/

#[requires(addr@.len() < 10000000)]
#[requires(length <= 64usize)]
#[requires(start@ + length@ <= 8 * addr@.len())]
fn peekthenpoke(start: usize, length: usize, addr: &mut [u8]) -> i8 {
    let value = peek(start, length, addr);
    let res = poke(start, length, addr, value);
    // too hard so far assert_eq!(res,0);
    res
}

/*****
 * poke then peek
 ****/

#[requires(addr@.len() < 10000000)]
#[requires(length <= 64usize)]
#[requires(start@ + length@ <= 8 * addr@.len())]
pub fn pokethenpeek(start: usize, length: usize, addr: &mut [u8], value: u64) -> u64 {
    let _res = poke(start, length, addr, value);
    // too hard so far assert_eq!(res,0);
    let peek_result = peek(start, length, addr);
    // too hard so far assert_eq!(peek_result,value);
    peek_result
}

#[trusted]
pub fn main() {
    let mut v: [u8; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    println!("v[0] = 0x{:02x}", v[0]);
    println!("v[1] = 0x{:02x}", v[1]);
    println!("v[2] = 0x{:02x}", v[2]);
    println!("v[3] = 0x{:02x}", v[3]);
    let x: u64 = peek(11, 48, &v);
    println!("peek result : u64 = 0x{:016x}", x);
    let res = poke(11, 17, &mut v, 0xFFFF);
    println!("poke result : i8 = {}", res);
    println!("v[0] = 0x{:02x}", v[0]);
    println!("v[1] = 0x{:02x}", v[1]);
    println!("v[2] = 0x{:02x}", v[2]);
    println!("v[3] = 0x{:02x}", v[3]);
    peekthenpoke(12, 34, &mut v);
    pokethenpeek(12, 34, &mut v, 56);
}
