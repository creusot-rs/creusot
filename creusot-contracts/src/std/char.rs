use crate::{Default, *};
pub use ::std::char::*;

impl View for char {
    type ViewTy = Int;
    #[logic]
    #[trusted]
    #[creusot::builtins = "creusot.prelude.Char.to_int"]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for char {
    type DeepModelTy = Int;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self@ }
    }
}

impl Default for char {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { self@ == 0 }
    }
}
