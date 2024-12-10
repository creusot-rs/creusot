#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

struct S;

#[logic]
fn views(x: S) {
    let _ = x.view();
    // FIXME(diagnostics): this error is printed twice, why?
    let _ = pearlite! { x@ };
}

// FIXME(diagnostics): separating this into 2 functions causes the second one to be ignored. We probably have an early exit that is a bit too eager (Look into the "Cannot fetch THIR body" error).
