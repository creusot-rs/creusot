//! Definition of [`IndexLogic`]

use crate::*;
#[cfg(feature = "nightly")]
use ::std::alloc::Allocator;

/// Used for indexing operations (`container[index]`) in pearlite.
#[diagnostic::on_unimplemented(
    message = "the type `{Self}` cannot be indexed by `{I}` in logic",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexLogic<I> {
    type Item;

    /// Performs the indexing (`container[index]`) operation.
    #[logic]
    #[rustc_diagnostic_item = "creusot_index_logic_method"]
    fn index_logic(self, idx: I) -> Self::Item;
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IndexLogic<Int> for Vec<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IndexLogic<usize> for Vec<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for [T] {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T> IndexLogic<usize> for [T] {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T, const N: usize> IndexLogic<Int> for [T; N] {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, const N: usize> IndexLogic<usize> for [T; N] {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for Snapshot<Seq<T>> {
    type Item = T;

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { (*self)[ix] }
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
impl<T> IndexLogic<Int> for Vec<T> {
    type Item = T;
}

#[cfg(not(feature = "nightly"))]
impl<T> IndexLogic<usize> for Vec<T> {
    type Item = T;
}
