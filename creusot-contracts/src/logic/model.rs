use crate as creusot_contracts;
use crate::{macros::*, Int, Seq};
#[cfg(feature = "contracts")]
use std::alloc::Allocator;

/// The shallow model of a type is typically used to specify a data
/// structure. This kind of model is mostly useful for notation purposes,
/// because this trait is linked to the @ notation of pearlite.
/// Models of inner types are typically not involved.
pub trait ShallowModel {
    type ShallowModelTy;
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy;
}

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
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for &T {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

impl<T: DeepModel + ?Sized> DeepModel for &mut T {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for &mut T {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

#[cfg(feature = "contracts")]
impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Box<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

#[cfg(feature = "contracts")]
impl<T: ShallowModel + ?Sized, A: Allocator> ShallowModel for Box<T, A> {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

impl<T, const N: usize> ShallowModel for [T; N] {
    type ShallowModelTy = Seq<T>;

    // We define this as trusted because builtins and ensures are incompatible
    #[logic]
    #[trusted]
    // TODO
    // #[ensures(result.len() == @N)]
    #[ensures(result == array_model(self))]
    fn shallow_model(self) -> Self::ShallowModelTy {
        array_model(self)
    }
}

#[logic]
#[trusted]
#[creusot::builtins = "prelude.Slice.id"]
fn array_model<T, const N: usize>(_: [T; N]) -> Seq<T> {
    pearlite! { absurd }
}

impl<T: DeepModel, const N: usize> DeepModel for [T; N] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    // TODO
    // #[ensures(result.len() == @N)]
    #[ensures(self.shallow_model().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < result.len() ==> result[i] == (@self)[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}

impl<T: DeepModel, U: DeepModel> DeepModel for (T, U) {
    type DeepModelTy = (T::DeepModelTy, U::DeepModelTy);

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { (self.0.deep_model(), self.1.deep_model()) }
    }
}

impl DeepModel for bool {
    type DeepModelTy = bool;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}

impl<T: DeepModel> DeepModel for Option<T> {
    type DeepModelTy = Option<T::DeepModelTy>;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Some(t) => Some(t.deep_model()),
            None => None,
        }
    }
}
