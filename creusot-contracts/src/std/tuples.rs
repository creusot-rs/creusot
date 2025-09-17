use crate::*;

impl DeepModel for () {
    type DeepModelTy = ();

    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { () }
    }
}

macro_rules! tuple_impls {
    ( $( ($name:ident, $idx:tt) )+ ) => {
        impl<$($name: DeepModel),+> DeepModel for ($($name,)+) {
            type DeepModelTy = ($($name::DeepModelTy,)+);

            #[logic(open)]
            fn deep_model(self) -> Self::DeepModelTy {
                pearlite! { ($(self.$idx.deep_model(),)+) }
            }
        }

        extern_spec! {
            impl<$($name: Default),+> Default for ($($name,)+) {
                #[ensures($($name::default.postcondition((), result.$idx))&&+)]
                fn default() -> ($($name,)+);
            }
        }
    };
}

tuple_impls! { (T,0) }
tuple_impls! { (U,0) (T,1) }
tuple_impls! { (V,0) (U,1) (T,2) }
tuple_impls! { (W,0) (V,1) (U,2) (T,3) }
tuple_impls! { (X,0) (W,1) (V,2) (U,3) (T,4) }
tuple_impls! { (Y,0) (X,1) (W,2) (V,3) (U,4) (T,5) }
tuple_impls! { (Z,0) (Y,1) (X,2) (W,3) (V,4) (U,5) (T,6) }
tuple_impls! { (A,0) (Z,1) (Y,2) (X,3) (W,4) (V,5) (U,6) (T,7) }
tuple_impls! { (B,0) (A,1) (Z,2) (Y,3) (X,4) (W,5) (V,6) (U,7) (T,8) }
tuple_impls! { (C,0) (B,1) (A,2) (Z,3) (Y,4) (X,5) (W,6) (V,7) (U,8) (T,9) }
tuple_impls! { (D,0) (C,1) (B,2) (A,3) (Z,4) (Y,5) (X,6) (W,7) (V,8) (U,9) (T,10) }
tuple_impls! { (E,0) (D,1) (C,2) (B,3) (A,4) (Z,5) (Y,6) (X,7) (W,8) (V,9) (U,10) (T,11) }
