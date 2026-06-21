// Audit: the opaque_builtin_impl lint fires on an unmodeled builtin impl over a
// concrete type (tuple Clone) but NOT on the ordinary generic `T::clone`.
extern crate creusot_std;

#[derive(Clone)]
pub struct W(pub u32);

// SHOULD warn: builtin Clone for the concrete tuple (W, W).
pub fn clone_tuple(x: (W, W)) -> (W, W) {
    x.clone()
}

// SHOULD NOT warn: generic parameter, the ordinary unresolved case.
pub fn clone_generic<T: Clone>(x: &T) -> T {
    x.clone()
}
