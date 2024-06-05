use crate::{Default, *};

impl DeepModel for () {
    type DeepModelTy = ();

    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { () }
    }
}

impl Default for () {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { true }
    }
}

macro_rules! tuple_impls {
    ( $( ($name:ident, $idx:tt) )+ ) => {
        impl<$($name: DeepModel),+> DeepModel for ($($name,)+) {
            type DeepModelTy = ($($name::DeepModelTy,)+);

            #[logic]
            #[open]
            fn deep_model(self) -> Self::DeepModelTy {
                pearlite! { ($(self.$idx.deep_model(),)+) }
            }
        }

        impl<$($name: Default),+> Default for ($($name,)+) {
            #[predicate(prophetic)]
            #[open]
            fn is_default(self) -> bool {
                pearlite! { $(self.$idx.is_default())&&+ }
            }
        }
    };
}

tuple_impls! { (A,0) }
tuple_impls! { (A,0) (B,1) }
tuple_impls! { (A,0) (B,1) (C,2) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) (H,7) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) (H,7) (I,8) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) (H,7) (I,8) (J,9) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) (H,7) (I,8) (J,9) (K,10) }
tuple_impls! { (A,0) (B,1) (C,2) (D,3) (E,4) (F,5) (G,6) (H,7) (I,8) (J,9) (K,10) (L,11) }
