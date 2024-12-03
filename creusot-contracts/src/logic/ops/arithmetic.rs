//! Arithmetic operators in logic

use crate::*;

/// Trait for addition (`+`) in logic code.
pub trait AddLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn add(self, other: Rhs) -> Self::Output;
}

/// Trait for subtraction (`-`) in logic code.
pub trait SubLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn sub(self, other: Rhs) -> Self::Output;
}

/// Trait for multiplication (`*`) in logic code.
pub trait MulLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn mul(self, other: Rhs) -> Self::Output;
}

/// Trait for division (`/`) in logic code.
pub trait DivLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn div(self, other: Rhs) -> Self::Output;
}

/// Trait for remainder (`%`) in logic code.
pub trait RemLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn rem(self, other: Rhs) -> Self::Output;
}

/// Trait for negation (unary `-`) in logic code.
pub trait NegLogic {
    type Output;

    #[logic]
    fn neg(self) -> Self::Output;
}

macro_rules! logic_traits_impl {
    ($($t:ty)*) => {
    $(
        impl AddLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn add(self, other: Self) -> Int {
                pearlite! { self@ + other@ }
            }
        }

        impl SubLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn sub(self, other: Self) -> Int {
                pearlite! { self@ - other@ }
            }
        }

        impl MulLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn mul(self, other: Self) -> Int {
                pearlite! { self@ * other@ }
            }
        }

        impl DivLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn div(self, other: Self) -> Int {
                pearlite! { self@ / other@ }
            }
        }

        impl RemLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn rem(self, other: Self) -> Int {
                pearlite! { self@ % other@ }
            }
        }

        impl NegLogic for $t {
            type Output = Int;

            #[logic]
            #[open]
            fn neg(self) -> Int {
                -self.view()
            }
        }
    )*
    };
}
logic_traits_impl! { i8 i16 i32 i64 u8 u16 u32 u64 isize usize }
