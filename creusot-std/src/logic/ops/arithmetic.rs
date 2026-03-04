//! Arithmetic operators in logic

use crate::prelude::*;

/// Trait for addition (`+`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot add `{Rhs}` to `{Self}` in logic",
    label = "no implementation for `{Self} + {Rhs}` in logic"
)]
pub trait AddLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn add_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for subtraction (`-`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot subtract `{Rhs}` from `{Self}` in logic",
    label = "no implementation for `{Self} - {Rhs}` in logic"
)]
pub trait SubLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn sub_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for multiplication (`*`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot multiply `{Self}` by `{Rhs}` in logic",
    label = "no implementation for `{Self} * {Rhs}` in logic"
)]
pub trait MulLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn mul_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for division (`/`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot divide `{Self}` by `{Rhs}` in logic",
    label = "no implementation for `{Self} / {Rhs}` in logic"
)]
pub trait DivLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn div_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for remainder (`%`) in logic code.
#[diagnostic::on_unimplemented(
    message = "cannot calculate the remainder of `{Self}` divided by `{Rhs}` in logic",
    label = "no implementation for `{Self} % {Rhs}` in logic"
)]
pub trait RemLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn rem_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for negation (unary `-`) in logic code.
#[diagnostic::on_unimplemented(
    message = "cannot apply unary operator `-` to type `{Self}`",
    label = "cannot apply unary operator `-` in logic"
)]
pub trait NegLogic {
    type Output;

    #[logic]
    fn neg_logic(self) -> Self::Output;
}

/// Trait for the nth bit of a bitvector in logic code.
pub trait NthBitLogic {
    /// The nth bit of a bitvector.
    /// In [`bitwise_proof`] mode, this is translated to [`nth`](https://www.why3.org/stdlib/bv.html#nth_188) in Why3.
    /// Otherwise this is an abstract function.
    #[logic]
    fn nth_bit(self, n: Int) -> bool;
}
