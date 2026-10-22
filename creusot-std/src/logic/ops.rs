use crate::prelude::*;
use core::ops::{Deref, DerefMut};
mod arithmetic;

pub use arithmetic::{AddLogic, DivLogic, MulLogic, NegLogic, RemLogic, SubLogic};

/// Used for indexing operations (`container[index]`) in pearlite.
#[diagnostic::on_unimplemented(
    message = "the type `{Self}` cannot be indexed by `{I}` in logic",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexLogic<I: ?Sized> {
    type Item;

    /// Performs the indexing (`container[index]`) operation.
    #[logic]
    #[requires(false)]
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
    #[requires(false)]
    fn shl_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for right shift (`>>`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} >> {Rhs}` in logic")]
pub trait ShrLogic<Rhs = Self> {
    type Output;

    #[logic]
    #[requires(false)]
    fn shr_logic(self, other: Rhs) -> Self::Output;
}

/// Trait for bitwise AND (`&`) in logic code.
#[diagnostic::on_unimplemented(message = "no implementation for `{Self} & {Rhs}` in logic")]
pub trait BitAndLogic<Rhs = Self> {
    type Output;

    #[logic]
    #[requires(false)]
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
    #[requires(false)]
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
    #[requires(false)]
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
    #[requires(false)]
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

/// Trait for dereference in logic.
///
/// Implementing this trait does _not_ automatically unlock dereference syntax
/// (`&*x`); you also need to have a _logical alias_:
/// ```
/// use creusot_std::{logic::ops::DerefLogic, prelude::*};
/// use std::ops::Deref;
///
/// struct MyInt(Int);
///
/// impl DerefLogic for MyInt {
///     #[logic]
///     fn deref_logic(&self) -> &Self::Target {
///         &self.0
///     }
/// }
///
/// impl Deref for MyInt {
///     type Target = Int;
///     #[check(ghost)]
///     #[logic_alias(self.deref_logic())]
///     fn deref(&self) -> &Self::Target {
///         &self.0
///     }
/// }
///
/// #[requires(*x == 1int)]
/// fn foo(x: MyInt) {}
/// ```
pub trait DerefLogic: Deref {
    #[logic]
    fn deref_logic(&self) -> &Self::Target;
}

/// Same as [`DerefLogic`], but for mutable borrows.
pub trait DerefMutLogic: DerefMut + DerefLogic {
    #[logic]
    fn deref_mut_logic(&mut self) -> &mut Self::Target;
}
