#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

struct S;

// FIXME(diagnostics): the current desugaring of indexing does not yield a nice error message :(
#[logic]
fn indexing(x: S) {
    let _ = x[0];
}
