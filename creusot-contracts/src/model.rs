use ::std::{rc::Rc, sync::Arc};

use crate::*;

/// The shallow model of a type is typically used to specify a data
/// structure. This kind of model is mostly useful for notation purposes,
/// because this trait is linked to the @ notation of pearlite.
/// Models of inner types are typically not involved.
pub trait View {
    type ViewTy;
    #[logic]
    fn view(self) -> Self::ViewTy;
}

pub use crate::base_macros::EqModel;

/// The deep model corresponds to the model used for specifying
/// operations such as equality, hash function or ordering, which are
/// computed deeply in a data structure.
/// Typically, such a model recursively calls deep models of inner types.
pub trait EqModel {
    type EqModelTy;
    #[logic]
    fn eq_model(self) -> Self::EqModelTy;
}

impl<T: EqModel> EqModel for Rc<T> {
    type EqModelTy = T::EqModelTy;
    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        pearlite! { self.view().eq_model() }
    }
}

impl<T> View for Rc<T> {
    type ViewTy = T;
    #[logic]
    #[open]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}

impl View for str {
    type ViewTy = Seq<char>;

    #[logic]
    #[open]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}

impl<T: EqModel> EqModel for Arc<T> {
    type EqModelTy = T::EqModelTy;
    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        pearlite! { self@.eq_model() }
    }
}

impl<T> View for Arc<T> {
    type ViewTy = T;
    #[logic]
    #[open]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}

impl<T: EqModel + ?Sized> EqModel for &T {
    type EqModelTy = T::EqModelTy;
    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        (*self).eq_model()
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

impl<T: EqModel + ?Sized> EqModel for &mut T {
    type EqModelTy = T::EqModelTy;
    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        (*self).eq_model()
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

impl EqModel for bool {
    type EqModelTy = bool;

    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        self
    }
}

impl View for String {
    type ViewTy = Seq<char>;

    #[logic]
    #[open(self)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        pearlite! { absurd }
    }
}
