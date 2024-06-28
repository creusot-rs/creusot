use crate::*;

impl<T, const N: usize> View for [T; N] {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[open]
    #[creusot::builtins = "prelude.Slice.id"]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}

impl<T: EqModel, const N: usize> EqModel for [T; N] {
    type EqModelTy = Seq<T::EqModelTy>;

    #[logic]
    #[trusted]
    #[open(self)]
    // TODO
    // #[ensures(result.len() == N@)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i: _> 0 <= i && i < result.len() ==> result[i] == self[i].eq_model())]
    fn eq_model(self) -> Self::EqModelTy {
        pearlite! { absurd }
    }
}
