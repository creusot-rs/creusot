#![cfg_attr(not(creusot), allow(unused_variables))]

use crate::{
    std::ops::{Deref, DerefMut},
    *,
};

#[rustc_diagnostic_item = "ghost_box"]
#[cfg(creusot)]
pub struct GhostBox<T: ?Sized>(T);

#[cfg(not(creusot))]
pub struct GhostBox<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: Clone + ?Sized> Clone for GhostBox<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Copy + ?Sized> Copy for GhostBox<T> {}

impl<T: ?Sized> Deref for GhostBox<T> {
    type Target = T;

    // This function can only be called in `ghost!` context
    #[pure]
    #[ensures((*self).0 == *result)]
    fn deref(&self) -> &Self::Target {
        #[cfg(creusot)]
        {
            &self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}
impl<T: ?Sized> DerefMut for GhostBox<T> {
    // This function can only be called in `ghost!` context
    #[pure]
    #[ensures((^self).0 == ^result)]
    #[ensures((*self).0 == *result)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        #[cfg(creusot)]
        {
            &mut self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for GhostBox<T> {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.shallow_model()
    }
}

#[trusted]
impl<T: ?Sized> Resolve for GhostBox<T> {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0)
    }
}

impl<T: ?Sized> GhostBox<T> {
    /// Transforms a `&GhostBox<T>` into a `GhostBox<&T>`.
    #[pure]
    #[ensures(result.0 == &self.0)]
    pub fn borrow(&self) -> GhostBox<&T> {
        #[cfg(creusot)]
        {
            GhostBox(&self.0)
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }

    /// Transforms a `&mut GhostBox<T>` into a `GhostBox<&mut T>`.
    #[pure]
    #[ensures(result.0 == &mut self.0)]
    pub fn borrow_mut(&mut self) -> GhostBox<&mut T> {
        #[cfg(creusot)]
        {
            GhostBox(&mut self.0)
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}

impl<T> GhostBox<T> {
    /// Creates a new ghost variable.
    ///
    /// This function can only be called in ghost code.
    #[rustc_diagnostic_item = "ghost_box_new"]
    #[pure]
    #[ensures(result.0 == x)]
    pub fn new(x: T) -> Self {
        #[cfg(creusot)]
        {
            Self(x)
        }
        #[cfg(not(creusot))]
        {
            Self(std::marker::PhantomData)
        }
    }

    // Internal function to easily create a GhostBox in non-creusot mode.
    #[requires(false)]
    #[doc(hidden)]
    pub fn from_fn(_f: impl Fn() -> T) -> Self {
        #[cfg(creusot)]
        {
            panic!()
        }
        #[cfg(not(creusot))]
        {
            GhostBox(std::marker::PhantomData)
        }
    }

    /// Returns the inner value of the `GhostBox`.
    #[logic]
    #[open(self)]
    #[ensures(result == self.0)]
    pub fn inner(self) -> T {
        self.0
    }
}
