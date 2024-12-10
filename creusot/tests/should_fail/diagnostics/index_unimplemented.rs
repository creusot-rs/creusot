#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

struct S;

// FIXME(diagnostics): the current desugaring of indexing does not yield a nice error message :(
#[logic]
fn indexing(x: S) {
    let _ = x[0];
}
