use crate::{invariant::*, logic::ops::IndexLogic, prelude::*};
#[cfg(creusot)]
use crate::{mode::Mode, resolve::structural_resolve};
use core::array::*;

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

impl<T, const N: usize> IteratorSpec for IntoIter<T, N> {
    #[logic(open, prophetic)]
    fn produces(self, _: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { self@ == visited.concat(o@) }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && self@ == Seq::empty() }
    }

    #[logic(open, law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
    }
}

extern_spec! {
    impl<T, const N: usize> IntoIterator for [T; N] {
        #[check(ghost)]
        #[ensures(self@ == result@)]
        fn into_iter(self) -> core::array::IntoIter<T, N>;
    }

    impl<T: Clone, const N: usize> Clone for [T; N] {
        #[ensures(|result, mode| forall<i> 0 <= i && i < self@.len() ==>
            T::clone.postcondition(mode, (&self@[i],), result@[i]))]
        fn clone(&self) -> [T; N];
    }

    impl<T, const N: usize> [T; N] {
        #[check(ghost)]
        #[ensures(result@ == self@)]
        fn as_slice(&self) -> &[T] {
            self
        }

        #[check(ghost)]
        #[ensures(result@ == self@)]
        #[ensures((^self)@.len() == (*self)@.len())]
        #[ensures((^result)@ == (^self)@)]
        fn as_mut_slice(&mut self) -> &mut [T] {
            self
        }
    }
}
