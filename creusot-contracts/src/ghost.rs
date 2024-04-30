use crate::{
    std::ops::{Deref, DerefMut},
    *,
};
use ::std::marker::PhantomData;

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
