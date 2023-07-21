use ::std::{rc::Rc, sync::Arc};

use crate::*;

/// The shallow model of a type is typically used to specify a data
/// structure. This kind of model is mostly useful for notation purposes,
/// because this trait is linked to the @ notation of pearlite.
/// Models of inner types are typically not involved.
pub trait ShallowModel {
    type ShallowModelTy;
    #[ghost]
    fn shallow_model(self) -> Self::ShallowModelTy;
}

#[cfg(creusot)]
pub use creusot_contracts_proc::DeepModel;

/// The deep model corresponds to the model used for specifying
/// operations such as equality, hash function or ordering, which are
/// computed deeply in a data structure.
/// Typically, such a model recursively calls deep models of inner types.
pub trait DeepModel {
    type DeepModelTy;
    #[ghost]
    fn deep_model(self) -> Self::DeepModelTy;
}

impl<T: DeepModel> DeepModel for Rc<T> {
    type DeepModelTy = T::DeepModelTy;
    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.shallow_model().deep_model() }
    }
}

impl<T> ShallowModel for Rc<T> {
    type ShallowModelTy = T;
    #[ghost]
    #[open]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

impl<T: DeepModel> DeepModel for Arc<T> {
    type DeepModelTy = T::DeepModelTy;
    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self@.deep_model() }
    }
}

impl<T> ShallowModel for Arc<T> {
    type ShallowModelTy = T;
    #[ghost]
    #[open]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

impl<T: DeepModel + ?Sized> DeepModel for &T {
    type DeepModelTy = T::DeepModelTy;
    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for &T {
    type ShallowModelTy = T::ShallowModelTy;
    #[ghost]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

impl<T: DeepModel + ?Sized> DeepModel for &mut T {
    type DeepModelTy = T::DeepModelTy;
    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for &mut T {
    type ShallowModelTy = T::ShallowModelTy;
    #[ghost]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

impl DeepModel for bool {
    type DeepModelTy = bool;

    #[ghost]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
