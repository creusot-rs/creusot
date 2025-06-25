use crate::{invariant::*, std::iter::Iterator, *};
use ::std::array::*;

impl<T, const N: usize> Invariant for [T; N] {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    #[creusot::trusted_ignore_structural_inv]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) }
    }
}

impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[cfg_attr(target_pointer_width = "16", creusot::builtins = "creusot.slice.Slice16.id")]
    #[cfg_attr(target_pointer_width = "32", creusot::builtins = "creusot.slice.Slice32.id")]
    #[cfg_attr(target_pointer_width = "64", creusot::builtins = "creusot.slice.Slice64.id")]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    // TODO
    // #[ensures(result.len() == N@)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T, const N: usize> View for IntoIter<T, N> {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[open]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { self@ == visited.concat(o@) }
    }

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@ == Seq::EMPTY }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
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
}
