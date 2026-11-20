use crate::{ghost::Plain, prelude::*};

impl View for char {
    type ViewTy = Int;
    #[logic]
    #[builtin("creusot.prelude.Char.to_int")]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for char {
    type DeepModelTy = Int;
    #[logic(open, inline)]
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

    impl char {
        #[check(ghost)]
        #[ensures(result == (self@ <= 127))]
        fn is_ascii(&self) -> bool;
    }
}

impl Plain for char {
    #[trusted]
    #[ensures(*result == *snap)]
    #[check(ghost)]
    #[allow(unused_variables)]
    fn into_ghost(snap: Snapshot<Self>) -> Ghost<Self> {
        Ghost::conjure()
    }
}

/// Extra methods for `char`
pub trait CharExt {
    #[logic]
    pub fn to_utf8(self) -> Seq<u8>;

    #[logic]
    #[requires(num >= 0)]
    #[requires(num <= 0x10FFFF)]
    #[requires(num < 0xD800 || num > 0xDFFF)]
    pub fn from_int(num: Int) -> Self;
}

impl CharExt for char {
    #[trusted]
    #[logic(opaque)]
    #[ensures(1 <= result.len() && result.len() <= 4)]
    #[ensures((self@ <= 127) == (result.len() == 1))]
    #[ensures(self@ <= 127 ==> result[0]@ == self@)]
    fn to_utf8(self) -> Seq<u8> {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[requires(num >= 0)]
    #[requires(num <= 0x10FFFF)]
    #[requires(num < 0xD800 || num > 0xDFFF)]
    #[ensures(result@ == num)]
    fn from_int(num: Int) -> Self {
        dead
    }
}

#[trusted]
#[logic(open)]
#[ensures(forall<c1: char, c2: char> c1.to_utf8() == c2.to_utf8() ==> c1 == c2)]
pub fn injective_to_utf8() {}
