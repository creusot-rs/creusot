use crate::{invariant::*, *};

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
    #[open]
    #[creusot::builtins = "prelude.prelude.Slice.id"]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}

impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[open(self)]
    // TODO
    // #[ensures(result.len() == N@)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i: _> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}
