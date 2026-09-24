use crate::prelude::*;
mod arithmetic;

pub use arithmetic::{AddLogic, DivLogic, MulLogic, NegLogic, NthBitLogic, RemLogic, SubLogic};

/// Used for indexing operations (`container[index]`) in pearlite.
#[diagnostic::on_unimplemented(
    message = "the type `{Self}` cannot be indexed by `{I}` in logic",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexLogic<I: ?Sized> {
    type Item;

    /// Performs the indexing (`container[index]`) operation.
    #[logic]
    #[intrinsic("index_logic")]
    fn index_logic(self, idx: I) -> Self::Item;
}

pub trait Fin {
    type Target: ?Sized;

    /// Allows overloading of the `^` operator.
    #[logic(prophetic)]
    fn fin<'a>(self) -> &'a Self::Target;
}

impl<T: ?Sized> Fin for &mut T {
    type Target = T;

    #[logic(prophetic)]
    #[builtin("fin")]
    fn fin<'a>(self) -> &'a T {
        dead
    }
}

/// Trait for left shift (`<<`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} << {Rhs}` in logic")]
pub trait ShlLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn shl_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for right shift (`>>`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} >> {Rhs}` in logic")]
pub trait ShrLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn shr_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for bitwise AND (`&`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} & {Rhs}` in logic")]
pub trait BitAndLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn bitand_logic(self, other: Rhs) -> Self::Output;
}

impl BitAndLogic for bool {
    type Output = bool;

    #[logic(open, inline)]
    fn bitand_logic(self, other: bool) -> Self::Output {
        self && other
    }
}

/// Trait for bitwise OR (`|`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} | {Rhs}` in logic")]
pub trait BitOrLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn bitor_logic(self, other: Rhs) -> Self::Output;
}

impl BitOrLogic for bool {
    type Output = bool;

    #[logic(open, inline)]
    fn bitor_logic(self, other: bool) -> Self::Output {
        self || other
    }
}

/// Trait for bitwise XOR (`^`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} ^ {Rhs}` in logic")]
pub trait BitXorLogic<Rhs = Self> {
    type Output;

    #[logic]
    fn bitxor_logic(self, other: Rhs) -> Self::Output;
}

impl BitXorLogic for bool {
    type Output = bool;

    #[logic(open, inline)]
    fn bitxor_logic(self, other: bool) -> Self::Output {
        self != other
    }
}

/// Trait for negation operator (`!`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `!{Self}` in logic")]
pub trait NotLogic {
    type Output;

    #[logic]
    fn not_logic(self) -> Self::Output;
}

impl NotLogic for bool {
    type Output = bool;

    #[logic]
    #[builtin("bool.Bool.notb")]
    fn not_logic(self) -> Self::Output {
        dead
    }
}
