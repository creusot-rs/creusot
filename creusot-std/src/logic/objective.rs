use crate::prelude::*;

/// An assertion whose meaning is independent of this thread's view.
///
/// Since `Objective` refers to ghost objects whose memory is objective, Rust's
/// `Unique<T>` (and therefore `Box<T>`, `Vec<T>`, ...) are therefore objective.
#[cfg(creusot)]
#[trusted]
pub auto trait Objective {}

/// A guard for potentially subjective types
///
/// Some types, such as `Perm`, could hold a permission to access a value that
/// depends on the view.
///
/// This negative implementation primarily targets `Perm<PermCell<T>>` and
/// `Perm<*const T>`.
pub(crate) struct NotObjective {}

#[cfg(creusot)]
#[trusted]
impl !Objective for NotObjective {}
