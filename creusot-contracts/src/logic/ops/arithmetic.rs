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
