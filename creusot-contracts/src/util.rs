//! Some useful logical items

use crate::*;

/// Creates a logical value satisfying the property given by `p`.
///
/// This is also called the "epsilon operator": its goal is not extract from `∃x. P(x)`
/// a `x` satisfying `P`.
#[trusted]
#[logic]
#[requires(exists<x: T> p[x])]
#[ensures(p[result])]
pub fn such_that<T>(p: crate::logic::Mapping<T, bool>) -> T {
    dead
}

/// Indicates unreachable code.
///
/// This function indicates a logical branch that should be impossible to reach.
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
#[requires(op != None)]
#[ensures(Some(result) == op)]
pub fn unwrap<T>(op: Option<T>) -> T {
    match op {
        Some(t) => t,
        None => unreachable(),
    }
}
