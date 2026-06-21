// Builtin tuple `Clone` carries the synthesized element-wise structural
// postcondition (via the `PostconditionOnce` intrinsic, like `#[derive(Clone)]`),
// recursing through nested tuples down to the leaves. The cases below exercise
// distinct leaf laws and tuple shapes.
extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result.0 == x.0 && result.1 == x.1)]
pub fn clone_flat(x: (u32, bool)) -> (u32, bool) {
    x.clone()
}

#[ensures(result.0.0 == x.0.0 && result.0.1 == x.0.1 && result.1 == x.1)]
pub fn clone_nested(x: ((u32, bool), u8)) -> ((u32, bool), u8) {
    x.clone()
}

// Generic fields: the law *composes* each field's own `Clone` postcondition
// rather than asserting a primitive equality.
#[ensures(T::clone.postcondition((&x.0,), result.0))]
#[ensures(U::clone.postcondition((&x.1,), result.1))]
pub fn clone_generic<T: Clone, U: Clone>(x: (T, U)) -> (T, U) {
    x.clone()
}

// Reference leaf: `<&u32 as Clone>::clone` is the shared-ref copy law, so the
// cloned reference is equal to the source (a leaf law distinct from the others).
#[ensures(*result.1 == *x.1)]
pub fn clone_ref_leaf(x: (bool, &u32)) -> (bool, &u32) {
    x.clone()
}

// Arity-1 tuple (distinct arity branch of the recursion).
#[ensures(result.0 == x.0)]
pub fn clone_one(x: (u32,)) -> (u32,) {
    x.clone()
}

// Unit leaf: `()` is an empty tuple, handled as a (trivial) leaf; the `bool`
// field is still constrained.
#[ensures(result.0 == x.0)]
pub fn clone_unit_leaf(x: (bool, ())) -> (bool, ()) {
    x.clone()
}

pub fn clone_closure(x: u32) -> impl Fn(u32) -> u32 {
    let f = move |y: u32| x + y;
    f.clone()
}

pub fn clone_tuple_with_closure(b: bool, x: u32) -> (bool, impl Fn(u32) -> u32) {
    let t = (b, move |y: u32| x + y);
    t.clone()
}
