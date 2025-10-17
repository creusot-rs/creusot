#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, logic::ops::IndexLogic, std::iter::Iterator, *};
use ::std::array::*;

impl<T, const N: usize> Invariant for [T; N] {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) && self@.len() == N@ }
    }
}

impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    #[logic]
    #[cfg_attr(target_pointer_width = "16", builtin("creusot.slice.Slice16.view"))]
    #[cfg_attr(target_pointer_width = "32", builtin("creusot.slice.Slice32.view"))]
    #[cfg_attr(target_pointer_width = "64", builtin("creusot.slice.Slice64.view"))]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T, const N: usize> Resolve for [T; N] {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
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

    #[logic(open, inline)]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, const N: usize> IndexLogic<usize> for [T; N] {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T, const N: usize> View for IntoIter<T, N> {
    type ViewTy = Seq<T>;

    #[logic(opaque)]
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
        pearlite! { resolve(self) && self@ == Seq::empty() }
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
        #[check(ghost)]
        #[ensures(self@ == result@)]
        fn into_iter(self) -> std::array::IntoIter<T, N>;
    }

    impl<T: Clone, const N: usize> Clone for [T; N] {
        #[ensures(forall<i> 0 <= i && i < self@.len() ==>
            T::clone.postcondition((&self@[i],), result@[i]))]
        fn clone(&self) -> [T; N];
    }
}
