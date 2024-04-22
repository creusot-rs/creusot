#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

fn recurses(b: bool) {
    if b {
        recurses(!b);
    }
}
