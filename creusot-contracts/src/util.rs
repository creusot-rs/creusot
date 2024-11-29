//! Some useful logical items

use crate::*;

/// A wrapper around `T` that makes it safe.
///
/// This type is indented to be used in logic code.
pub type SizedW<T> = Box<T>;

/// Helper trait to turn a `T` into a [`SizedW<T>`]
pub trait MakeSized {
    /// Turn a `T` into a [`SizedW<T>`]
    #[logic]
    #[why3::attr = "inline:trivial"]
    fn make_sized(&self) -> SizedW<Self>;
}

impl<T: ?Sized> MakeSized for T {
    #[trusted]
    #[logic]
    #[ensures(*result == *self)]
    fn make_sized(&self) -> SizedW<Self> {
        dead
    }
}

/// Indicates unreachable code.
///
/// This function indicate a logical branch that should be impossible to reach.
#[trusted]
#[allow(unconditional_recursion)]
#[logic]
#[requires(false)]
#[ensures(false)]
#[variant(0)]
pub fn unreachable<T>() -> T {
    unreachable()
}

/// Returns the inner value of an [`Option`], given that it is not `None`
#[logic]
#[open(self)]
#[requires(op != None)]
#[ensures(Some(result) == op)]
pub fn unwrap<T>(op: Option<T>) -> T {
    match op {
        Some(t) => t,
        None => unreachable(),
    }
}
