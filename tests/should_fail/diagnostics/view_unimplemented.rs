#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

struct S;

#[logic]
fn views(x: S) {
    let _ = x.view();
}

fn view_operator(x: S) {
    // FIXME(diagnostics): this error is printed twice, why?
    let _ = pearlite! { x@ };
}
