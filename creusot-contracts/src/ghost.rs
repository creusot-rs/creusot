use crate::{
    std::ops::{Deref, DerefMut},
    *,
};
use ::std::marker::PhantomData;

// FIXME: better doc
/// Any item that implements `Ghost` must **not** be able to break the ownership rules,
/// be it in ghost or runtime code.
///
/// Additionnaly, it should be zero-sized, so that it's not possible to extract
/// information from a ghost bloc and use it in normal code.
#[rustc_diagnostic_item = "ghost_trait"]
#[trusted]
pub trait Ghost {}

macro_rules! impl_ghost_tuple {
    ($($ty_param:ident),*) => {
        impl_ghost_tuple!{ @inner $($ty_param,)* || []; }
    };
    (@inner $ty_param:ident, $($rest:ident,)* || $( [ $($done:ident,)* ] ;)*) => {
        impl_ghost_tuple! {
            @inner $($rest,)* ||
            [] ; $( [ $ty_param, $($done,)* ] ;)*
        }
    };
    (@inner || $( [ $($done:ident,)* ] ;)*) => {
        $(
            #[trusted]
            impl<$($done : Ghost),*> Ghost for ($($done,)*) {}
        )*
    };
}

impl_ghost_tuple! { T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }

#[trusted]
impl<T> Ghost for Snapshot<T> {}

pub struct GhostBox<T: ?Sized>(PhantomData<T>);

impl<T: ?Sized> Deref for GhostBox<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[pure]
    #[open(self)]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}
impl<T: ?Sized> DerefMut for GhostBox<T> {
    #[trusted]
    #[logic]
    #[pure]
    #[open(self)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        pearlite! { absurd }
    }
}
#[trusted]
impl<T: ?Sized> Ghost for GhostBox<T> {}

impl<T: ShallowModel + ?Sized> ShallowModel for GhostBox<T> {
    type ShallowModelTy = T::ShallowModelTy;

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deref().shallow_model() }
    }
}

impl<T> GhostBox<T> {
    #[trusted]
    #[pure]
    #[ensures(*result == x)]
    pub fn new(x: T) -> Self {
        Self(PhantomData)
    }
    
    #[trusted]
    #[pure]
    #[requires(true)]
    #[ensures(true)]
    pub fn uninit() -> Self {
        Self(PhantomData)
    }

    #[trusted]
    #[logic]
    #[open(self)]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        pearlite! { absurd }
    }
}
