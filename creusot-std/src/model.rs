//! Logical models of types: [`View`] and [`DeepModel`]
use crate::prelude::*;
use core::cmp::Ordering;

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

/// The derive macro for the `DeepModel` trait.
///
/// This macro can be used to implement `DeepModel` by recursively delegating into `DeepModel` of
/// each individual field. For a struct, it generates a new struct and for an enum it generates a
/// new enum. Other types are not supported. The generated type is named the same as the type this
/// is derived for with the `DeepModel` suffix appended to it.
///
/// The visibility of the generated types and their fields will be the same (including the
/// `non_exhaustive` attribute, if present) and the types of the fields will be the `DeepModelTy` of
/// the corresponding field. For instance, `pub struct Foo { bar: u32 }` will become
/// `pub struct FooDeepModel { bar: Int }`.
///
/// To avoid exposing private fields, the generated `deep_model` method will have openess restricted
/// to the most restrictive visibility of the type. If the type is public but its field is private,
/// the resulting openess will be private. `#[non_exhaustive]` acts as if the type had an additional
/// `pub(crate)` field. The visibility is computed as intersection, so paths `super::super` and
/// `super` will become `super`. If the visibility cannot be computed precisely a conservative
/// default is used - the private visibility. Therefore it's not recommended to mix styles of
/// specifying the visibility - either use relative (`super::super::...`) or absolute
/// (`crate::foo::bar`) in all items.
///
/// While this works well for structs that are either fully private or fully public, mixed
/// visibility has the consequence that your downstream users may have hard time verifying their
/// code because it won't see the relationship between the fields of struct and its deep model. This
/// cannot be solved automatically and in such case a more precise manual implementation may be
/// required.
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

impl DeepModel for Ordering {
    type DeepModelTy = Ordering;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
