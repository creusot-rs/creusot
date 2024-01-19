use ::std::alloc::Allocator;

use crate::*;

pub trait IndexLogic<I> {
    type Item;

    #[ghost]
    #[rustc_diagnostic_item = "index_logic_method"]
    fn index_logic(self, idx: I) -> Self::Item;
}

impl<T, A: Allocator> IndexLogic<Int> for Vec<T, A> {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, A: Allocator> IndexLogic<usize> for Vec<T, A> {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for [T] {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    #[rustc_diagnostic_item = "slice_index_logic"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T> IndexLogic<usize> for [T] {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T, const N: usize> IndexLogic<Int> for [T; N] {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, const N: usize> IndexLogic<usize> for [T; N] {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> IndexLogic<Int> for Ghost<Seq<T>> {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { (*self)[ix] }
    }
}
