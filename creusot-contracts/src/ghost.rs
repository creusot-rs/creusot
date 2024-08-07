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
#[rustc_diagnostic_item = "ghost_box"]
pub struct GhostBox<T: ?Sized>(Box<T>);

impl<T: ?Sized> Deref for GhostBox<T> {
    type Target = T;

    // This function can only be called in `ghost!` context
    #[pure]
    #[ensures(*(*self).0 == *result)]
    fn deref(&self) -> &Self::Target {
        &(*self.0)
    }
}
impl<T: ?Sized> DerefMut for GhostBox<T> {
    // This function can only be called in `ghost!` context
    #[pure]
    #[ensures(*(^self).0 == ^result)]
    #[ensures(*(*self).0 == *result)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut (*self.0)
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for GhostBox<T> {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self.0).shallow_model()
    }
}

#[trusted]
impl<T: ?Sized> Resolve for GhostBox<T> {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        Resolve::resolve(*self.0)
    }
}

impl<T> GhostBox<T> {
    #[rustc_diagnostic_item = "ghost_box_new"]
    #[pure]
    #[ensures(*result.0 == x)]
    pub fn new(x: T) -> Self {
        Self(Box::new(x))
    }

    #[trusted]
    #[pure]
    #[requires(true)]
    #[ensures(true)]
    pub fn uninit() -> Self {
        loop {}
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(result == *self.0)]
    pub fn inner(self) -> T {
        *self.0
    }
}
