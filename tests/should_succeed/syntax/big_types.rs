// Check our Why3 pretty printer on large types to force line breaks
extern crate creusot_std;

pub enum BigSum {
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    A8,
    A9,
    A10,
    A11,
    A12,
    A13,
    A14,
    A15,
    A16,
    A17,
    A18,
    A19,
}

pub fn is_a1(x: BigSum) -> bool {
    match x {
        BigSum::A1 => true,
        _ => false,
    }
}

#[allow(dead_code)]
pub struct BigRecord {
    a1: u32,
    a2: u32,
    a3: u32,
    a4: u32,
    a5: u32,
    a6: u32,
    a7: u32,
    a8: u32,
    a9: u32,
    a10: u32,
    a11: u32,
    a12: u32,
    a13: u32,
    a14: u32,
    a15: u32,
    a16: u32,
    a17: u32,
    a18: u32,
}

pub fn get_a1(x: BigRecord) -> u32 {
    x.a1
}
