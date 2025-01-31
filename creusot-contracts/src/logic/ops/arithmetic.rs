//! Arithmetic operators in logic

use crate::*;

/// Trait for addition (`+`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot add `{Rhs}` to `{Self}` in logic",
    label = "no implementation for `{Self} + {Rhs}` in logic"
)]
pub trait AddLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn add(self, other: Rhs) -> Self::Output;
}

/// Trait for subtraction (`-`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot subtract `{Rhs}` from `{Self}` in logic",
    label = "no implementation for `{Self} - {Rhs}` in logic"
)]
pub trait SubLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn sub(self, other: Rhs) -> Self::Output;
}

/// Trait for multiplication (`*`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot multiply `{Self}` by `{Rhs}` in logic",
    label = "no implementation for `{Self} * {Rhs}` in logic"
)]
pub trait MulLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn mul(self, other: Rhs) -> Self::Output;
}

/// Trait for division (`/`) in logic code.
#[diagnostic::on_unimplemented(
    message = "Cannot divide `{Self}` by `{Rhs}` in logic",
    label = "no implementation for `{Self} / {Rhs}` in logic"
)]
pub trait DivLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn div(self, other: Rhs) -> Self::Output;
}

/// Trait for remainder (`%`) in logic code.
#[diagnostic::on_unimplemented(
    message = "cannot calculate the remainder of `{Self}` divided by `{Rhs}` in logic",
    label = "no implementation for `{Self} % {Rhs}` in logic"
)]
pub trait RemLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn rem(self, other: Rhs) -> Self::Output;
}

/// Trait for negation (unary `-`) in logic code.
#[diagnostic::on_unimplemented(
    message = "cannot apply unary operator `-` to type `{Self}`",
    label = "cannot apply unary operator `-` in logic"
)]
pub trait NegLogic {
    type Output;

    #[logic]
    fn neg(self) -> Self::Output;
}
