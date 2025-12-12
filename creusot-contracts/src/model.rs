//! Logical models of types: [`View`] and [`DeepModel`]
use crate::prelude::*;

/// The view of a type is its logical model as typically used to specify a data
/// structure. It is typically "shallow", and does not involve the model of
/// other types contained by the datastructure.
/// This kind of model is mostly useful for notation purposes,
/// because this trait is linked to the `@` notation of pearlite.
#[diagnostic::on_unimplemented(
    message = "Cannot take the view of `{Self}`",
    label = "no implementation for `{Self}@`"
)]
pub trait View {
    type ViewTy;
    #[logic]
    #[intrinsic("view")]
    fn view(self) -> Self::ViewTy;
}

pub use crate::base_macros::DeepModel;

/// The deep model corresponds to the model used for specifying
/// operations such as equality, hash function or ordering, which are
/// computed deeply in a data structure.
/// Typically, such a model recursively calls deep models of inner types.
pub trait DeepModel {
    type DeepModelTy;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy;
}

impl<T: DeepModel + ?Sized> DeepModel for &T {
    type DeepModelTy = T::DeepModelTy;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: DeepModel + ?Sized> DeepModel for &mut T {
    type DeepModelTy = T::DeepModelTy;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl DeepModel for bool {
    type DeepModelTy = bool;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl DeepModel for Int {
    type DeepModelTy = Int;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

#[cfg(feature = "std")]
impl View for String {
    type ViewTy = Seq<char>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for core::cmp::Ordering {
    type DeepModelTy = core::cmp::Ordering;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
