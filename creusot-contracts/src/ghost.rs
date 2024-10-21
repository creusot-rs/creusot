#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{
    std::ops::{Deref, DerefMut},
    *,
};

/// A type that can be used in `ghost` context.
///
/// This type may be used to make more complicated proofs possible. In particular, some
/// proof may need a notion of non-duplicable token to carry around.
///
/// Conceptually, a `GhostBox<T>` is a pointer to an item of type `T` that resides in
/// a special "ghost" heap. This heap is innacessible from normal code, and `GhostBox`
/// values cannot be used to influence the behavior of normal code.
///
/// This box can be dereferenced in a `ghost` block:
/// ```compile_fail
/// let b: GhostBox<i32> = GhostBox::new(1);
/// ghost! {
///     let value: i32 = *b;
///     // use value here
/// }
/// let value: i32 = *b; // compile error !
/// ```
#[cfg_attr(creusot, rustc_diagnostic_item = "ghost_box")]
pub struct GhostBox<T>(#[cfg(creusot)] Box<T>, #[cfg(not(creusot))] std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized + Clone> Clone for GhostBox<T> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        #[cfg(creusot)]
        {
            Self(self.0.clone())
        }
        #[cfg(not(creusot))]
        {
            Self(std::marker::PhantomData)
        }
    }
}

impl<T: ?Sized> Deref for GhostBox<T> {
    type Target = T;

    /// This function can only be called in `ghost!` context
    #[pure]
    #[ensures(*(*self).0 == *result)]
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
    /// This function can only be called in `ghost!` context
    #[pure]
    #[ensures(result == &mut *self.0)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        #[cfg(creusot)]
        {
            &mut *self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}

impl<T: View + ?Sized> View for GhostBox<T> {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

impl<T: ?Sized> Resolve for GhostBox<T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        resolve(&self.0)
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(&self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T: ?Sized> GhostBox<T> {
    /// Transforms a `&GhostBox<T>` into `GhostBox<&T>`.
    #[pure]
    #[ensures(*result.0 == &*self.0)]
    pub fn borrow(&self) -> GhostBox<&T> {
        #[cfg(creusot)]
        {
            GhostBox(Box::new(&*self.0))
        }
        #[cfg(not(creusot))]
        {
            GhostBox(std::marker::PhantomData)
        }
    }

    /// Transforms a `&mut GhostBox<T>` into a `GhostBox<&mut T>`.
    #[pure]
    #[ensures(*result.0 == &mut *self.0)]
    pub fn borrow_mut(&mut self) -> GhostBox<&mut T> {
        #[cfg(creusot)]
        {
            GhostBox(Box::new(&mut *self.0))
        }
        #[cfg(not(creusot))]
        {
            GhostBox(std::marker::PhantomData)
        }
    }

    // Internal function to easily create a GhostBox in non-creusot mode.
    #[cfg(not(creusot))]
    #[doc(hidden)]
    pub fn from_fn(_: impl FnOnce() -> T) -> Self {
        GhostBox(std::marker::PhantomData)
    }
}

impl<T> GhostBox<T> {
    /// Creates a new ghost variable.
    ///
    /// This function can only be called in `ghost!` code.
    #[pure]
    #[ensures(*result.0 == x)]
    #[rustc_diagnostic_item = "ghost_box_new"]
    pub fn new(x: T) -> Self {
        #[cfg(creusot)]
        {
            Self(Box::new(x))
        }
        #[cfg(not(creusot))]
        {
            let _ = x;
            Self(std::marker::PhantomData)
        }
    }

    /// Returns the inner value of the `GhostBox`.
    ///
    /// This function can only be called in `ghost!` context.
    #[pure]
    #[ensures(result == *self.0)]
    #[rustc_diagnostic_item = "ghost_box_into_inner"]
    pub fn into_inner(self) -> T {
        #[cfg(creusot)]
        {
            *self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }

    /// Returns the inner value of the `GhostBox`.
    ///
    /// You should prefer the dereference operator `*` instead.
    #[logic]
    #[open]
    #[rustc_diagnostic_item = "ghost_box_inner_logic"]
    pub fn inner_logic(self) -> T {
        *self.0
    }
}
