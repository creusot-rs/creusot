use crate::*;

/// The view of a type is its logical model as typically used to specify a data
/// structure. It is typically "shallow", and does not involve the model of
/// other types contained by the datastructure.
/// This kind of model is mostly useful for notation purposes,
/// because this trait is linked to the @ notation of pearlite.
#[diagnostic::on_unimplemented(
    message = "Cannot take the model of `{Self}`",
    label = "no implementation for `{Self}@`"
)]
pub trait View {
    type ViewTy;
    #[logic]
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
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: View + ?Sized> View for &T {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        (*self).view()
    }
}

impl<T: DeepModel + ?Sized> DeepModel for &mut T {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: View + ?Sized> View for &mut T {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        (*self).view()
    }
}

impl DeepModel for bool {
    type DeepModelTy = bool;

    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl DeepModel for Int {
    type DeepModelTy = Int;

    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl View for String {
    type ViewTy = Seq<char>;

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for std::cmp::Ordering {
    type DeepModelTy = std::cmp::Ordering;

    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
