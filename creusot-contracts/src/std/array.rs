use crate::{
    invariant::*,
    std::iter::{IntoIterator, Iterator},
    *,
};
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

    //TODO laurent valider l'approche de separation en 3 block
    
    #[cfg(target_pointer_width = "64")]
    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.prelude.Slice64.id"]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn view(self) -> Self::ViewTy {
        dead
    }

    #[cfg(target_pointer_width = "32")]
    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.prelude.Slice32.id"]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn view(self) -> Self::ViewTy {
        dead
    }

    #[cfg(target_pointer_width = "16")]
    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.prelude.Slice16.id"]
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
    #[ensures(forall<i: _> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
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

impl<T, const N: usize> IntoIterator for [T; N] {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate(prophetic)]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self@ == res@ }
    }
}
