use crate::*;

impl<T, const N: usize> ShallowModel for [T; N] {
    type ShallowModelTy = Seq<T>;

    #[logic]
    #[trusted]
    #[open]
    #[creusot::builtins = "prelude.Slice.id"]
    // TODO:
    // #[ensures(result.len() == N@)]
    // Warning: #[ensures] and #[trusted] are incompatible, so this might require
    fn shallow_model(self) -> Self::ShallowModelTy {
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
    #[ensures(self.shallow_model().len() == result.len())]
    #[ensures(forall<i: _> 0 <= i && i < result.len() ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}
