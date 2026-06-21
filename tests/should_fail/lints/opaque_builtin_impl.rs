// `opaque_builtin_impl` fires when a call resolves to an unmodeled builtin trait
// impl whose result is left (partly) unconstrained. `#![deny]` makes it an error
// (like the other `should_fail/lints/` tests), so no `.coma` is emitted and the
// why3 proof job skips it.
#![deny(creusot::opaque_builtin_impl)]
extern crate creusot_std;

// (1) Cloning a closure: the compiler-builtin `Clone` impl has no synthesized
// law, so the result is unconstrained — the lint fires.
pub fn clone_closure(x: u32) -> impl Fn(u32) -> u32 {
    let f = move |y: u32| x + y;
    f.clone()
}

// (2) A tuple containing a closure leaf: the synthesized tuple-`Clone` law is
// incomplete (the closure leaf's conjunct is vacuous), so the lint still fires,
// naming the whole `(bool, closure)` type — the loss is flagged, not silent.
pub fn clone_tuple_with_closure(b: bool, x: u32) -> (bool, impl Fn(u32) -> u32) {
    let t = (b, move |y: u32| x + y);
    t.clone()
}
