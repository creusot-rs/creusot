use crate::{ghost::Plain, *};
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

extern_spec! {
    impl Default for char {
        #[check(ghost)]
        #[ensures(result@ == 0)]
        fn default() -> char;
    }
}

#[trusted]
impl Plain for char {}

/// Extra methods for `char`
pub trait CharExt {
    #[logic]
    pub fn to_utf8(self) -> Seq<u8>;
}

impl CharExt for char {
    #[logic]
    #[trusted]
    #[ensures(1 <= result.len() && result.len() <= 4)]
    fn to_utf8(self) -> Seq<u8> {
        dead
    }
}

#[trusted]
#[logic]
#[open]
#[ensures(forall<c1: char, c2: char> c1.to_utf8() == c2.to_utf8() ==> c1 == c2)]
pub fn injective_to_utf8() {}
