extern crate creusot_contracts;
use creusot_contracts::*;

pub fn bitwise_test_constant() {
    let l: u16 = 0xC;
    let r: u16 = 0xA;

    let result_and: u16 = l & r;
    let result_or: u16 = l | r;
    let result_xor: u16 = l ^ r;
    let result_not: u16 = !l;

    if result_and != 0x8 {
        assert!(false);
    }

    if result_or != 0xE {
        assert!(false);
    }

    if result_xor != 0x6 {
        assert!(false);
    }

    if result_not != 0xFFF3 {
        assert!(false);
    }
}

#[allow(arithmetic_overflow)]
pub fn bitwise_test_shift() {
    let a: u16 = 0xFFFF;

    let result_l3: u16 = a << 3u16;
    // let result_l16: u16 = a << 16u16;
    let result_r6: u16 = a >> 6u16;

    if result_l3 != 0xFFF8 {
        assert!(false);
    }

    if result_r6 != 0x3FF {
        assert!(false);
    }
}

#[requires(l@<100)]
#[requires(r@<100)]
pub fn bitwise_add(l: u16, r: u16) -> u16 {
    l + r
}

#[requires(l@<200)]
#[requires(l@>100)]
#[requires(r@<100)]
pub fn bitwise_sub(l: u16, r: u16) -> u16 {
    l - r
}

#[requires(l@<100)]
#[requires(r@<100)]
pub fn bitwise_mul(l: u16, r: u16) -> u16 {
    l * r
}

#[requires(l@<100)]
#[requires(r@<100)]
#[requires(r@ != 0)]
pub fn bitwise_div(l: u16, r: u16) -> u16 {
    l / r
}

#[requires(l@<100)]
#[requires(r@<100)]
#[requires(r@ != 0)]
pub fn bitwise_mod(l: u16, r: u16) -> u16 {
    l % r
}

// #[requires(l@<100)]
// pub fn bitwise_neg(l: u16) -> u16 {
//     let r:i32 = -l;
//     r
// }
// operateur neg

#[requires(l@<=50)]
#[requires(r@>50)]
#[ensures(l@<r@)]
pub fn bitwise_lt(l: u16, r: u16) -> bool {
    l < r
}

#[requires(l@<=50)]
#[requires(r@>=50)]
#[ensures(l@<=r@)]
pub fn bitwise_le(l: u16, r: u16) -> bool {
    l <= r
}

#[requires(l@>=50)]
#[requires(r@<50)]
#[ensures(l@>r@)]
pub fn bitwise_gt(l: u16, r: u16) -> bool {
    l > r
}

#[requires(l@>=50)]
#[requires(r@<=50)]
#[ensures(l@>=r@)]
pub fn bitwise_ge(l: u16, r: u16) -> bool {
    l >= r
}

#[ensures(result == l & r)]
pub fn bitwise_and(l: u16, r: u16) -> u16 {
    l & r
}

#[ensures(result == l << 3u16)]
pub fn bitwise_shl_3(l: u16) -> u16 {
    l << 3u16
}

// pub fn bitwise_add(l: u16, r: u16) -> u16 {
//     l + r
// }

/*
#[requires(l@<100)]
#[requires(r@<100)]
#[ensures(result == l & r)]
pub fn bitwise_and2(l: i16, r: i16) -> i16 {
    l & r
}
*/

// extern crate creusot_contracts;
// use creusot_contracts::*;
// /*
// #[ensures(result == (a@ <= 100))]
// pub fn test_literal_i32(a: i32) -> bool {
//     a <= 100
// }*/
// /*
// #[requires(l@ < 100)]
// #[requires(r@ < 100)]
// #[ensures(result == l & r)]*/
// pub fn bitwise_and(l: u16, r: u16) -> u16 {
//     l & r
// }

// /*
// #[requires(l@<100)]
// #[requires(r@<100)]
// #[ensures(result == l & r)]
// pub fn bitwise_and2(l: i16, r: i16) -> i16 {
//     l & r
// }
// */
