#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, logic::ops::IndexLogic, std::iter::Iterator, *};
use ::std::array::*;

impl<T, const N: usize> Invariant for [T; N] {
    #[logic(open, prophetic)]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) && self@.len() == N@ }
    }
}

impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[cfg_attr(target_pointer_width = "16", creusot::builtins = "creusot.slice.Slice16.view")]
    #[cfg_attr(target_pointer_width = "32", creusot::builtins = "creusot.slice.Slice32.view")]
    #[cfg_attr(target_pointer_width = "64", creusot::builtins = "creusot.slice.Slice64.view")]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T, const N: usize> Resolve for [T; N] {
    #[logic(open, prophetic)]
    fn resolve(self) -> bool {
        pearlite! { forall<i: Int> 0 <= i && i < N@ ==> resolve(self@[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T, const N: usize> IndexLogic<Int> for [T; N] {
    type Item = T;

    #[logic(open)]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, const N: usize> IndexLogic<usize> for [T; N] {
    type Item = T;

    #[logic(open)]
    #[creusot::why3_attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T, const N: usize> View for IntoIter<T, N> {
    type ViewTy = Seq<T>;

    #[logic(open)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { self@ == visited.concat(o@) }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@ == Seq::empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

extern_spec! {
    impl<T, const N: usize> IntoIterator for [T; N] {
        #[ensures(self@ == result@)]
        fn into_iter(self) -> std::array::IntoIter<T, N>;
    }

    impl<T: Clone, const N: usize> Clone for [T; N] {
        #[ensures(forall<i> 0 <= i && i < self@.len() ==>
            T::clone.postcondition((&self@[i],), result@[i]))]
        fn clone(&self) -> [T; N];
    }
}
