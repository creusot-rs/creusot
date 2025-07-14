extern crate creusot_contracts;
use creusot_contracts::*;

#[bitwise_proof]
pub fn test_bitwise_ops() {
    // bw_and
    assert_eq!(0b1111_0000u8 & 0b0011_1100u8, 0b0011_0000u8);
    assert_eq!(0b0111_0001i8 & 0b0011_1101i8, 0b0011_0001i8);
    assert_eq!(0b1010_0100_1111_0001u16 & 0b0101_0100_0011_1101u16, 0b0000_0100_0011_0001u16);
    assert_eq!(0b0011_0100_1111_0001i16 & 0b0101_0100_0011_1101i16, 0b0001_0100_0011_0001i16);
    assert_eq!(0xC0000003u32 & 0x40018002u32, 0x40000002u32);
    assert_eq!(0x4000000Fi32 & 0x40000F01i32, 0x40000001i32);
    assert_eq!(0xC000F00000000003u64 & 0x8001A80000000001u64, 0x8000A00000000001u64);
    assert_eq!(0x4000000000999990i64 & 0x4888888000888880i64, 0x4000000000888880i64);
    assert_eq!(0xF4C000F00000000003u128 & 0xA88001A80000000001u128, 0xA08000A00000000001u128);
    assert_eq!(0xF4C000F00000000003i128 & 0xA88001A80000000001i128, 0xA08000A00000000001i128);
    assert_eq!(0b1111_0000usize & 0b0011_1100usize, 0b0011_0000usize);
    assert_eq!(0b0111_0001isize & 0b0011_1101isize, 0b0011_0001isize);

    // bw_or
    assert_eq!(0b1111_0000u8 | 0b0011_1100u8, 0b1111_1100u8);
    assert_eq!(0b0111_0001i8 | 0b0011_1101i8, 0b0111_1101i8);
    assert_eq!(0b1010_0100_1111_0001u16 | 0b0101_0100_0011_1101u16, 0b1111_0100_1111_1101u16);
    assert_eq!(0b0011_0100_1111_0001i16 | 0b0101_0100_0011_1101i16, 0b0111_0100_1111_1101i16);
    assert_eq!(0xC0000003u32 | 0x40018002u32, 0xC0018003u32);
    assert_eq!(0x4000000Fi32 | 0x40000F01i32, 0x40000F0Fi32);
    assert_eq!(0xC000F00000000003u64 | 0x8001A80000000001u64, 0xC001F80000000003u64);
    assert_eq!(0x4000000000999990i64 | 0x4888888000888880i64, 0x4888888000999990i64);
    assert_eq!(0xF4C000F00000000003u128 | 0xA88001A80000000001u128, 0xFCC001F80000000003u128);
    assert_eq!(0xF4C000F00000000003i128 | 0xA88001A80000000001i128, 0xFCC001F80000000003i128);
    assert_eq!(0b1111_0000usize | 0b0011_1100usize, 0b1111_1100usize);
    assert_eq!(0b0111_0001isize | 0b0011_1101isize, 0b0111_1101isize);

    // bw_xor
    assert_eq!(0b1111_0000u8 ^ 0b0011_1100u8, 0b1100_1100u8);
    assert_eq!(0b0111_0001i8 ^ 0b0011_1101i8, 0b0100_1100i8);
    assert_eq!(0b1010_0100_1111_0001u16 ^ 0b0101_0100_0011_1101u16, 0b1111_0000_1100_1100u16);
    assert_eq!(0b0011_0100_1111_0001i16 ^ 0b0101_0100_0011_1101i16, 0b0110_0000_1100_1100i16);
    assert_eq!(0xC0000003u32 ^ 0x40018002u32, 0x80018001u32);
    assert_eq!(0x4000000Fi32 ^ 0x40000F01i32, 0xF0Ei32);
    assert_eq!(0xC000F00000000003u64 ^ 0x8001A80000000001u64, 0x4001580000000002u64);
    assert_eq!(0x4000000000999990i64 ^ 0x4888888000888880i64, 0x888888000111110i64);
    assert_eq!(0xF4C000F00000000003u128 ^ 0xA88001A80000000001u128, 0x5C4001580000000002u128);
    assert_eq!(0xF4C000F00000000003i128 ^ 0xA88001A80000000001i128, 0x5C4001580000000002i128);
    assert_eq!(0b1111_0000usize ^ 0b0011_1100usize, 0b1100_1100usize);
    assert_eq!(0b0111_0001isize ^ 0b0011_1101isize, 0b0100_1100isize);

    // bw_not
    assert_eq!(!0b1111_0000u8, 0b0000_1111u8);
    assert_eq!(!0b0111_0001i8, -114i8);
    assert_eq!(!0b1010_0100_1111_0001u16, 0b0101_1011_0000_1110u16);
    assert_eq!(!0b0011_0100_1111_0001i16, -13554i16);
    assert_eq!(!0xC0000003u32, 0x3FFFFFFCu32);
    assert_eq!(!0x4000000Fi32, -1073741840i32);
    assert_eq!(!0xC000F00000000003u64, 0x3FFF0FFFFFFFFFFCu64);
    assert_eq!(!0x4000000000999990i64, -4611686018437454225i64);
    assert_eq!(!0xF4C000F00000000003u128, 0xFFFFFFFFFFFFFF0B3FFF0FFFFFFFFFFCu128);
    assert_eq!(!0xF4C000F00000000003i128, -4514840875923203424260i128);
}

#[bitwise_proof]
pub fn test_shift_ops() {
    // left shift
    assert_eq!(0b1111_0000u8 << 2, 0b1100_0000u8);
    assert_eq!(0b0110_1001i8 << 3, 0b0100_1000i8);
    assert_eq!(0b1111_1111_1111_1111u16 << 3, 0b1111_1111_1111_1000u16);
    assert_eq!(0xC0000003u32 << 2, 0xCu32);
    assert_eq!(0xC000F00000000003u64 << 4, 0xF000000000030);
    assert_eq!(0xF4C000F00000000003u128 << 3, 0x7A60007800000000018);
    assert_eq!(0b1111_0000usize << 2, 0b11_1100_0000usize);

    // right shift
    assert_eq!(0b1111_0000u8 >> 2, 0b0011_1100u8);
    assert_eq!(0b1111_0000u8 as i8 >> 2, 0b1111_1100u8 as i8);
    assert_eq!(0b1111_1111_1111_1111u16 >> 6, 0b0000_0011_1111_1111u16);
    assert_eq!(0xC0000003u32 >> 14, 0x30000);
    assert_eq!(0xC000F00000000003u64 >> 18, 0x30003C000000);
    assert_eq!(u128::MAX >> 110, 0x3FFFF);
    assert_eq!(0b1111_0000usize >> 2, 0b0011_1100usize);
}

macro_rules! test_ops {
    ($t: ty, $three: expr) => {
        #[requires(l@ + r@ >= $t::MIN@ && l@ + r@ <= $t::MAX@)]
        #[ensures(result@ == l@ + r@)]
        pub fn test_add(l: $t, r: $t) -> $t {
            l + r
        }

        #[requires(l@ + r@ >= $t::MIN@ && l@ + r@ <= $t::MAX@)]
        #[ensures(result@ == l@ + r@)]
        #[bitwise_proof]
        pub fn test_add_bw(l: $t, r: $t) -> $t {
            l + r
        }

        #[requires(l@ - r@ >= $t::MIN@ && l@ - r@ <= $t::MAX@)]
        #[ensures(result@ == l@ - r@)]
        pub fn test_sub(l: $t, r: $t) -> $t {
            l - r
        }

        #[requires(l@ - r@ >= $t::MIN@ && l@ - r@ <= $t::MAX@)]
        #[ensures(result@ == l@ - r@)]
        #[bitwise_proof]
        pub fn test_sub_bw(l: $t, r: $t) -> $t {
            l - r
        }

        #[requires(l@ * r@ >= $t::MIN@ && l@ * r@ <= $t::MAX@)]
        #[ensures(result@ == l@ * r@)]
        pub fn test_mul(l: $t, r: $t) -> $t {
            l * r
        }

        #[requires(l@ * r@ >= $t::MIN@ && l@ * r@ <= $t::MAX@)]
        #[ensures(result@ == l@ * r@)]
        #[bitwise_proof]
        pub fn test_mul_bw(l: $t, r: $t) -> $t {
            l * r
        }

        #[requires(r@ != 0)]
        #[requires(l@ / r@ >= $t::MIN@ && l@ / r@ <= $t::MAX@)]
        #[ensures(result@ == l@ / r@)]
        pub fn test_div(l: $t, r: $t) -> $t {
            l / r
        }

        #[requires(r@ != 0)]
        #[requires(l@ / r@ >= $t::MIN@ && l@ / r@ <= $t::MAX@)]
        #[ensures(result@ == l@ / r@)]
        #[bitwise_proof]
        pub fn test_div_bw(l: $t, r: $t) -> $t {
            l / r
        }

        #[ensures(result == b as $t)]
        pub fn test_from_bool(b: bool) -> $t {
            assert_eq!(true as $t, 1);
            assert_eq!(false as $t, 0);
            b as $t
        }

        #[ensures(result == b as $t)]
        #[bitwise_proof]
        pub fn test_from_bool_bw(b: bool) -> $t {
            assert_eq!(true as $t, 1);
            assert_eq!(false as $t, 0);
            b as $t
        }

        #[ensures(result == n << $three)] // homogeneous shift
        #[ensures(result == n << 3u8)] // heterogeneous shift
        pub fn test_shl(n: $t) -> $t {
            n << 3
        }

        #[ensures(result == n << $three)]
        #[ensures(result == n << 3u8)]
        #[bitwise_proof]
        pub fn test_shl_bw(n: $t) -> $t {
            n << 3
        }

        #[ensures(result == n >> $three)]
        #[ensures(result == n >> 3u8)]
        pub fn test_shr(n: $t) -> $t {
            n >> 3
        }

        #[ensures(result == n >> $three)]
        #[ensures(result == n >> 3u8)]
        #[bitwise_proof]
        pub fn test_shr_bw(n: $t) -> $t {
            n >> 3
        }
    };
}

pub mod u8 {
    use super::*;
    test_ops!(u8, 3u8);

    pub fn test_to_char() {
        assert_eq!((0x61 as u8) as char, 'a');
    }

    #[bitwise_proof]
    pub fn test_to_char_bw() {
        assert_eq!((0xFF as u8) as char, 'ÿ');
    }
}

pub mod i8 {
    use super::*;
    test_ops!(i8, 3i8);

    #[requires(n > i8::MIN)]
    #[ensures(result == -n)]
    pub fn test_neg(n: i8) -> i8 {
        -n
    }

    #[requires(n > i8::MIN)]
    #[ensures(result == -n)]
    #[bitwise_proof]
    pub fn test_neg_bw(n: i8) -> i8 {
        -n
    }
}

pub mod u16 {
    use super::*;
    test_ops!(u16, 3u16);
}

pub mod i16 {
    use super::*;
    test_ops!(i16, 3i16);
}

pub mod u32 {
    use super::*;
    test_ops!(u32, 3u32);
}

pub mod i32 {
    use super::*;
    test_ops!(i32, 3i32);
}

pub mod u64 {
    use super::*;
    test_ops!(u64, 3u64);
}

pub mod i64 {
    use super::*;
    test_ops!(i64, 3i64);
}

pub mod u128 {
    use super::*;
    test_ops!(u128, 3u128);
}

pub mod i128 {
    use super::*;
    test_ops!(i128, 3i128);
}

pub mod usize {
    use super::*;
    test_ops!(usize, 3usize);
}

pub mod isize {
    use super::*;
    test_ops!(isize, 3isize);
}
