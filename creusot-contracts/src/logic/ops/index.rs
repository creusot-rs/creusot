//! Definition of [`IndexLogic`]

use crate::*;
use ::std::alloc::Allocator;

/// Used for indexing operations (`container[index]`) in pearlite.
pub trait IndexLogic<I: ?Sized> {
    type Item;

    /// Performs the indexing (`container[index]`) operation.
    #[logic]
    #[rustc_diagnostic_item = "creusot_index_logic_method"]
    fn index_logic(self, idx: I) -> Self::Item;
}

impl<T, A: Allocator> IndexLogic<Int> for Vec<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, A: Allocator> IndexLogic<usize> for Vec<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for [T] {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T> IndexLogic<usize> for [T] {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T, const N: usize> IndexLogic<Int> for [T; N] {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, const N: usize> IndexLogic<usize> for [T; N] {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for Snapshot<Seq<T>> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { (*self)[ix] }
    }
}
