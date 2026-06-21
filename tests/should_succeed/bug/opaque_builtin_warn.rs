// Counter-examples for the `opaque_builtin_impl` lint.
extern crate creusot_std;

// (1) Cloning a closure resolves to the compiler-builtin `Clone` impl, which has
// no synthesized law: the result is left unconstrained, so the lint WARNS.
pub fn clone_closure(x: u32) -> impl Fn(u32) -> u32 {
    let f = move |y: u32| x + y;
    f.clone()
}

// (2) A tuple containing a closure leaf: the call is tuple `Clone`, so the lint
// is SUPPRESSED (a structural law is synthesized). The closure leaf's conjunct
// is vacuous, but no second warning is emitted here — only `clone_closure`
// above warns (see the .stderr).
pub fn clone_tuple_with_closure(b: bool, x: u32) -> (bool, impl Fn(u32) -> u32) {
    let t = (b, move |y: u32| x + y);
    t.clone()
}
