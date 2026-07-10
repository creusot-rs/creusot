extern crate creusot_std;
use creusot_std::prelude::*;

pub fn float_operation() -> f32 {
    let x: f32 = 0.0;

    if x + 1.0005 == 2.0 { 3.0 - 1.0 } else { 0.0 }
}

#[ensures(result@.len() == 4)]
#[ensures(result@ == seq![0x74u8, 0x65u8, 0x73u8, 0x74u8])]
pub fn bytes_literal() -> &'static [u8; 4] {
    b"test"
}

#[ensures(result@.len() == 0)]
pub fn bytes_literal_empty() -> &'static [u8; 0] {
    b""
}

#[ensures(result == 4_usize)]
pub fn bytes_literal_in_body() -> usize {
    let msg: &[u8; 4] = b"test";
    msg.len()
}

const TEST_BYTES: &[u8; 10] = b"const test";

#[ensures(result == 0x74_u8)] // 't'
pub fn bytes_literal_in_const() -> u8 {
    TEST_BYTES[9]
}

#[bitwise_proof]
#[ensures(result == 0x65_u8)] // 'e'
pub fn bytes_literal_bw() -> u8 {
    let my_bytes: &[u8; 6] = b"A test";
    my_bytes[3]
}

#[ensures(result == 0x65_u8)]
pub fn bytes_as_array() -> u8 {
    let my_bytes: [u8; 6] = [b'A', b' ', b't', b'e', b's', b't'];
    my_bytes[3]
}

#[ensures(result == 0x65_u8)]
pub fn bytes_as_array_slice() -> u8 {
    let my_bytes: &[u8; 6] = &[b'A', b' ', b't', b'e', b's', b't'];
    my_bytes[3]
}

#[ensures(result == 0_usize)]
pub fn empty_array() -> usize {
    let empty: [u32; 0] = [];
    empty.len()
}
